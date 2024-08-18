import { options } from "./cli";
import { fnInLateImpl, LateImpls } from "./impls";
import { LetDecl, FnParameter, AstTy, Expr, AstFnSignature, RecordFields, Stmt, Module, FnDecl, PathSegment, Pat, Impl, ImplItem, Generics, Trait } from "./parse";
import { Resolutions, PrimitiveTy, BindingPat } from "./resolve";
import { Span, ppSpan } from "./span";
import { TokenType } from "./token";
import { Ty, UNIT, isUnit, BOOL, U64, RecordType, hasTyVid, EMPTY_FLAGS, TYPARAM_MASK, TYVID_MASK, instantiateTy, ppTy, normalize, I32, STR_SLICE, U8, NEVER, eqTy, TyParamCheck, genericArgsOfTy } from "./ty";
import { assert, assertUnreachable, swapRemove, todo } from "./util";
import { visitInStmt } from "./visit";
import { bug, err, emitErrorRaw as error, spanless_bug } from './error';

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'Binary' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index' | 'FnArgument' | 'UseInCondition' | 'Unary' | 'Pattern' | 'JoinBlock';
type Constraint = { cause: ConstraintCause, at: Span, depth: number } & ConstraintType;
const MAX_CONSTRAINT_DEPTH = 200;

type FnLocalState = {
    expectedReturnTy: Ty;
    returnFound: boolean;
};

export type TypeckResults = {
    infcx: Infcx,
    loweredTys: Map<AstTy, Ty>,
    instantiatedFnSigs: Map<Expr, InstantiatedFnSig>,
    exprTys: Map<Expr, Ty>,
    patTys: Map<LetDecl | FnParameter | BindingPat, Ty>,
    selectedMethods: Map<Expr, { type: 'Fn' } & ImplItem>,
    hadErrors: boolean,
    impls: LateImpls
};

export type InstantiatedFnSig = {
    parameters: Ty[],
    ret: Ty,
    args: Ty[]
};

type InfTyVar = {
    constrainedTy: Ty | null,
    // when we come across a constraint that we can't make any progress on (such as ?0t == ?1t), instead of adding it back to infcx.constraints,
    // add the constraint to both sides' `delayedConstraints` and only push all of them at some later point to infcx.constraints
    // when either one gets constrained
    //
    // this is done like this so as to prevent overflows for fallback: `1 + 1` requires `?1i == ?2i` with no way to immediately make progress,
    // so store it as a delayed constraint in both ?1i and ?2i.
    // now if we come across e.g. `?2i == i32` and `?2i` gets constrained, we can process the old `?1i == ?2i` constraint and finally make progress on that.
    // OTOH, if it never gets constrained, at the end of LUB check, we can apply fallback by forcefully constraining all integer type vars to i32
    // and re-add their constraints one last time so that we check `i32 == i32`, which succeeds
    delayedConstraints: Constraint[],
    origin: TyVarOrigin,
};
type TyVarOrigin = { type: 'Expr', expr: Expr }
    | { type: 'GenericArg', span: Span }
    | { type: 'BindingPat', span: Span }
    | { type: 'Let', span: Span }
    // special: falls back to `i32` and doesn't need to be constrained
    | { type: 'IntegerLiteral', span: Span };

function tyVarOriginSpan(origin: TyVarOrigin): Span {
    switch (origin.type) {
        case 'Expr': return origin.expr.span;
        case 'GenericArg': return origin.span;
        case 'BindingPat': return origin.span;
        case 'Let': return origin.span;
        case 'IntegerLiteral': return origin.span;
    }
}

function originFallback(origin: TyVarOrigin): Ty | null {
    switch (origin.type) {
        case 'IntegerLiteral': return I32;
        default: return null;
    }
}

function tyVarHasFallback(tyvar: InfTyVar): boolean {
    return originFallback(tyvar.origin) !== null;
}

function peelInfixDerefOpTy(isDeref: boolean, ty: Ty, span: Span): Ty {
    if (isDeref) {
        if (ty.type !== 'Pointer') {
            err(span, `deref property access requires a pointer type, got ${ppTy(ty)}`)
        }
        return ty.pointee;
    } else {
        return ty;
    }
}

export type LUBResult = { hadErrors: boolean };

class Infcx {
    tyVars: Array<InfTyVar> = [];
    constraints: Constraint[] = [];
    fnStack: FnLocalState[] = [];
    exprTys = new Map<Expr, Ty>();

    constructor() { }

    sub(cause: ConstraintCause, at: Span, sub: Ty, sup: Ty) {
        this.constraints.push({ type: 'SubtypeOf', at, cause, sub, sup, depth: 0 });
    }

    nestedSub(parent: Constraint, sub: Ty, sup: Ty, at?: Span) {
        this.constraints.push({ type: 'SubtypeOf', at: at || parent.at, cause: parent.cause, depth: parent.depth + 1, sub, sup });
    }

    mkTyVar(origin: TyVarOrigin): Ty {
        const id = this.tyVars.length;
        this.tyVars.push({ constrainedTy: null, origin, delayedConstraints: [] });
        const ty: Ty = { type: 'TyVid', flags: TYVID_MASK, id };
        if (origin.type === 'Expr') {
            this.exprTys.set(origin.expr, ty);
        }
        return ty;
    }

    withFn(expect: Ty | undefined, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect || UNIT, returnFound: false });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (!isUnit(expectedReturnTy) && !returnFound) {
            spanless_bug(`expected ${expectedReturnTy.type}, got ()`);
        }
    }

    registerReturn(at: Span, ty: Ty) {
        const fs = this.fnStack[this.fnStack.length - 1];
        fs.returnFound = true;
        const sup = fs.expectedReturnTy;
        this.sub('Return', at, ty, sup);
    }

    tryResolve(ty: Ty): Ty {
        if (ty.type === 'TyVid' && this.tyVars[ty.id].constrainedTy) {
            return this.tyVars[ty.id].constrainedTy!;
        }
        return ty;
    }
}

export function returnTy(sig: AstFnSignature, typeck: TypeckResults): Ty {
    return sig.ret ? typeck.loweredTys.get(sig.ret)! : UNIT;
}

export function typeck(src: string, ast: Module, res: Resolutions): TypeckResults {
    const infcx = new Infcx();
    const loweredTys = new Map<AstTy, Ty>();
    const instantiatedFnSigs = new Map<Expr, InstantiatedFnSig>();
    // TODO: move away from LetDecl | FnParam, once LetDecl | FnParam is implemented in terms of patterns
    const patTys: Map<LetDecl | FnParameter | BindingPat, Ty> = new Map();
    const selectedMethods: Map<Expr, { type: 'Fn' } & ImplItem> = new Map();

    const lateImpls: LateImpls = res.impls.map(([ty, impl]) => [lowerTy(ty), impl]);

    function lowerTy(ty: AstTy): Ty {
        let lowered = loweredTys.get(ty);
        if (lowered) return lowered;

        function lowerInner(ty: AstTy): Ty {
            switch (ty.type) {
                case 'Path': {
                    const tyres = res.tyResolutions.get(ty)!;
                    switch (tyres.type) {
                        case 'TyParam': return { type: 'TyParam', flags: TYPARAM_MASK, id: tyres.id, parentItem: tyres.parentItem };
                        case 'Primitive': switch (tyres.kind) {
                            case PrimitiveTy.Never: return { type: 'never', flags: EMPTY_FLAGS };
                            case PrimitiveTy.I8: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 8 } };
                            case PrimitiveTy.I16: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 16 } };
                            case PrimitiveTy.I32: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 32 } };
                            case PrimitiveTy.I64: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 64 } };
                            case PrimitiveTy.U8: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 8 } };
                            case PrimitiveTy.U16: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 16 } };
                            case PrimitiveTy.U32: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 32 } };
                            case PrimitiveTy.U64: return { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 64 } };
                            case PrimitiveTy.Bool: return BOOL;
                            case PrimitiveTy.Str: return { type: 'str', flags: EMPTY_FLAGS };
                            default: assertUnreachable(tyres.kind)
                        }
                        case 'TyAlias':
                            const args: Ty[] = [];
                            let flags = EMPTY_FLAGS;
                            for (const arg of ty.value.segments[0].args) {
                                const lowered = lowerTy(arg.ty);
                                flags |= lowered.flags;
                                args.push(lowered);
                            }
                            return { type: 'Alias', flags, decl: tyres, alias: lowerTy(tyres.alias), args };
                        case 'Enum': return { type: 'Enum', flags: EMPTY_FLAGS, decl: tyres };
                        case 'Mod': bug(ty.span, 'cannot lower module as a type');
                        case 'Trait': bug(ty.span, `expected type, got trait ${ty.value}`);
                        case 'Self': return lowerTy(tyres.selfTy);
                        case 'Root': bug(ty.span, 'cannot lower root paths');
                        default: assertUnreachable(tyres)
                    }
                }
                case 'Array': {
                    const elemTy = lowerTy(ty.elemTy);
                    return { type: 'Array', flags: elemTy.flags, elemTy, len: ty.len };
                }
                case 'Pointer': {
                    const pointee = lowerTy(ty.pointeeTy);
                    return { type: 'Pointer', flags: pointee.flags, mtb: ty.mtb, pointee };
                }
                case 'Record': {
                    let flags = EMPTY_FLAGS;
                    const fields: RecordFields<Ty> = [];
                    for (const [k, sty] of ty.fields) {
                        const lowered = lowerTy(sty);
                        fields.push([k, lowered]);
                        flags |= lowered.flags;
                    }
                    return { type: 'Record', flags, fields };
                }
                case 'Tuple': {
                    let flags = EMPTY_FLAGS;
                    const elements: Ty[] = [];
                    for (const element of ty.elements) {
                        const lowered = lowerTy(element);
                        flags |= lowered.flags;
                        elements.push(lowered);
                    }
                    return { type: 'Tuple', flags, elements };
                }
                case 'Alias': bug(ty.span, 'cannot lower type aliases directly');
                case 'Infer': bug(ty.span, 'cannot lower `_` here');
                case 'Enum': return { type: 'Enum', flags: EMPTY_FLAGS, decl: ty };
                default: assertUnreachable(ty);
            }
        }
        lowered = lowerInner(ty);
        loweredTys.set(ty, lowered);
        return lowered;
    }

    function typeckFnSig(sig: AstFnSignature, enclosingImplOrTrait?: Impl | Trait): Ty | undefined {
        const ret = sig.ret && lowerTy(sig.ret);
        for (const parameter of sig.parameters) {
            if (parameter.type === 'Receiver') {
                if (!enclosingImplOrTrait) spanless_bug('receiver outside of an impl or trait');

                let recv: Ty;
                if (enclosingImplOrTrait.type === 'Impl') {
                    recv = lowerTy(enclosingImplOrTrait.selfTy);
                } else {
                    recv = { type: 'TyParam', flags: TYPARAM_MASK, id: 0, parentItem: enclosingImplOrTrait };
                }

                if (parameter.ptr) {
                    recv = { type: 'Pointer', flags: recv.flags, mtb: parameter.ptr, pointee: recv };
                }
                patTys.set(parameter, recv);
            } else {
                patTys.set(parameter, lowerTy(parameter.ty));
            }
        }
        return ret;
    }

    function typeckFn(decl: FnDecl, enclosingImpl?: Impl) {
        const ret = typeckFnSig(decl.sig, enclosingImpl);
        infcx.withFn(ret, () => { typeckExpr(decl.body); });
    }

    function typeckStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': typeckFn(stmt); break;
            case 'Expr': typeckExpr(stmt.value); break;
            case 'LetDecl': {
                const rety = stmt.init === null ? infcx.mkTyVar({ type: 'Let', span: stmt.span }) : typeckExpr(stmt.init);
                if (stmt.ty) {
                    const annotatedTy = lowerTy(stmt.ty);
                    infcx.sub('Assignment', stmt.span, rety, annotatedTy);
                    // this isn't more wrong than using `rety`, but allows some additional cases to typeck:
                    // let x: {x:i32} = bitcast(1);
                    // x.x;
                    //
                    // if we register the local with the expression's type, we'd use a type variable,
                    // which some expressions aren't ready to deal with (eg property access)
                    // using the annotated type allows that to compile because it won't be a type variable, but a proper record type.
                    // we still require proving annotatedTy == initTy at the end of typeck, though, above
                    patTys.set(stmt, annotatedTy);
                } else {
                    patTys.set(stmt, rety);
                }
                break;
            }
            case 'TyAlias': break;
            case 'ExternFnDecl': typeckFnSig(stmt.sig); break;
            case 'Impl': {
                lowerTy(stmt.selfTy);
                for (const item of stmt.items) {
                    typeckFn(item.decl, stmt);
                }
                break;
            }
            case 'Mod': {
                for (const item of stmt.items) {
                    typeckStmt(item);
                }
                break;
            }
            case 'Trait': {
                for (const item of stmt.items) {
                    typeckFnSig(item.sig, stmt);
                }
                break;
            }
            case 'Use': break;
            default: assertUnreachable(stmt);
        }
    }

    function typeckPat(pat: Pat): Ty {
        switch (pat.type) {
            case 'Number': return I32;
            case 'RangeFrom':
            case 'RangeTo': {
                const operand = pat.type === 'RangeFrom' ? pat.from : pat.to;
                if (operand.type !== 'String') {
                    todo('RangeFrom/RangeTo for non-strings')
                }
                return STR_SLICE;
            }
            case 'String': return STR_SLICE;
            case 'Range': todo('range');
            case 'Path': {
                const pathres = res.patResolutions.get(pat);
                if (pathres) {
                    switch (pathres.type) {
                        case 'Binding': {
                            const ty = infcx.mkTyVar({ type: 'BindingPat', span: pat.span });
                            patTys.set(pathres, ty);
                            return ty;
                        }
                        case 'Variant': return { type: 'Enum', decl: pathres.enum, flags: EMPTY_FLAGS };
                    }
                } else {
                    bug(pat.span, 'unknown res in pattern: ' + pathres);
                }
            }
        }
    }

    function typeckExpr(expr: Expr): Ty {
        function inner(expr: Expr): Ty {
            switch (expr.type) {
                case 'Block': {
                    for (const stmt of expr.stmts) {
                        typeckStmt(stmt);
                    }
                    if (expr.tailExpr) {
                        return typeckExpr(expr.tailExpr);
                    } else {
                        return UNIT;
                    }
                }
                case 'Path': {
                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        // TODO: is EMPTY_FLAGS correct here..?
                        case 'FnDecl': return { type: 'FnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'ExternFnDecl': return { type: 'ExternFnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'TraitFn':
                            return { type: 'TraitFn', value: litres.value, flags: EMPTY_FLAGS };
                        case 'LetDecl':
                        case 'Binding': return patTys.get(litres)!;
                        case 'FnParam': return patTys.get(litres.param)!;
                        case 'Variant': return lowerTy(litres.enum);
                        default: assertUnreachable(litres);
                    }
                }
                case 'Return': {
                    const ret = typeckExpr(expr.value);
                    infcx.registerReturn(expr.span, ret);
                    return { type: 'never', flags: EMPTY_FLAGS };
                }
                case 'ArrayLiteral': {
                    let elemTy: Ty;
                    if (expr.elements.length === 0) {
                        elemTy = infcx.mkTyVar({ type: "Expr", expr });
                    } else {
                        elemTy = typeckExpr(expr.elements[0]);
                        for (let i = 1; i < expr.elements.length; i++) infcx.sub('ArrayLiteral', expr.elements[i].span, typeckExpr(expr.elements[i]), elemTy);
                    }
                    return { type: 'Array', flags: elemTy.flags, elemTy, len: expr.elements.length };
                }
                case 'ArrayRepeat': {
                    const elemTy = typeckExpr(expr.element);
                    return { type: 'Array', elemTy, flags: elemTy.flags, len: expr.count };
                }
                case 'Assignment': {
                    infcx.sub('Assignment', expr.span, typeckExpr(expr.value), typeckExpr(expr.target));
                    return UNIT;
                }
                case 'Index': {
                    infcx.sub('Index', expr.span, typeckExpr(expr.index), U64);
                    const target = typeckExpr(expr.target);
                    if (target.type === 'Array') {
                        return target.elemTy;
                    } else {
                        // TODO: constraint for tyvar
                        err(expr.span, `cannot index into ${target.type}`);
                    }
                }
                // TODO: typescript's "as const" can create a literal type?
                case 'Number':
                    if (expr.suffix) {
                        return { type: 'int', flags: EMPTY_FLAGS, value: expr.suffix };
                    } else {
                        return infcx.mkTyVar({ span: expr.span, type: 'IntegerLiteral' });
                    }
                case 'ByteCharacter': return U8;
                case 'Bool': return BOOL;
                case 'String': return STR_SLICE;
                case 'Binary': {
                    const lhsTy = typeckExpr(expr.lhs);
                    const rhsTy = typeckExpr(expr.rhs);
                    let expectedLhsTy: Ty;
                    let expectedRhsTy: Ty;
                    let resultTy: Ty;
                    // TODO: we should constrain it to any int type
                    switch (expr.op) {
                        case TokenType.Plus:
                        case TokenType.Minus:
                        case TokenType.Star:
                        case TokenType.Slash:
                        case TokenType.Percent:
                            expectedLhsTy = rhsTy;
                            expectedRhsTy = lhsTy;
                            resultTy = lhsTy;
                            break;
                        case TokenType.Lt:
                        case TokenType.Le:
                        case TokenType.Gt:
                        case TokenType.Ge:
                        case TokenType.EqEq:
                        case TokenType.NotEq:
                            expectedLhsTy = rhsTy;
                            expectedRhsTy = lhsTy;
                            resultTy = BOOL;
                            break;
                        case TokenType.AndAnd:
                        case TokenType.OrOr:
                            expectedLhsTy = rhsTy;
                            expectedRhsTy = lhsTy;
                            resultTy = BOOL;
                            break;
                        default: assertUnreachable(expr);
                    }
                    infcx.sub('Binary', expr.lhs.span, lhsTy, expectedLhsTy);
                    infcx.sub('Binary', expr.rhs.span, rhsTy, expectedRhsTy);
                    return resultTy;
                }
                case 'AddrOf': {
                    const pointee = typeckExpr(expr.pointee);
                    return { type: 'Pointer', flags: pointee.flags, mtb: expr.mtb, pointee };
                }
                case 'Deref': {
                    const pointee = typeckExpr(expr.pointee);
                    if (pointee.type === 'Pointer') {
                        return pointee.pointee;
                    } else {
                        err(expr.span, `attempted to dereference non-pointer type ${pointee.type}`);
                    }
                };
                case 'Record': {
                    const fields: RecordFields<Ty> = [];
                    let flags = EMPTY_FLAGS;
                    for (const [key, value] of expr.fields) {
                        const ty = typeckExpr(value);
                        fields.push([key, ty]);
                        flags |= ty.flags;
                    }
                    return { type: 'Record', flags, fields };
                }
                case 'FnCall': {
                    const callee = typeckExpr(expr.callee);
                    if (expr.callee.type !== 'Path') {
                        // TODO: move the substitution stuff to typechecking paths specifically
                        bug(expr.span, 'callee must be a path to a FnDef');
                    }

                    const sig: InstantiatedFnSig = {
                        parameters: [],
                        ret: UNIT,
                        args: []
                    };

                    let astSig: AstFnSignature;
                    let selfTy: Ty | null;
                    if (callee.type === 'FnDef' || callee.type === 'ExternFnDef') {
                        astSig = callee.decl.sig;
                        const parent = (callee.decl as FnDecl).parent;
                        selfTy = parent ? lowerTy(parent.selfTy) : null;

                        let segmentsAndGenerics: [PathSegment<AstTy>, Generics][];
                        if (callee.type === 'FnDef' && callee.decl.parent !== null) {
                            // This is a call to an associated function.
                            // The parent `impl` can have generics that we need to subtitute also

                            const [ty, assoc] = expr.callee.path.segments.slice(-2);
                            segmentsAndGenerics = [
                                [ty, callee.decl.parent.generics],
                                [assoc, callee.decl.sig.generics],
                            ];
                        } else {
                            // This is a call to a free function.
                            segmentsAndGenerics = [
                                [expr.callee.path.segments[expr.callee.path.segments.length - 1], callee.decl.sig.generics]
                            ];
                        }

                        for (const [segment, generics] of segmentsAndGenerics) {
                            if (segment.args.length === 0) {
                                for (let i = 0; i < generics.length; i++) {
                                    sig.args.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                                }
                            } else {
                                for (const arg of segment.args) {
                                    if (arg.ty.type === 'Infer') {
                                        sig.args.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                                    } else {
                                        sig.args.push(lowerTy(arg.ty));
                                    }
                                }
                            }
                        }
                    } else if (callee.type === 'TraitFn') {
                        astSig = callee.value.sig;
                        selfTy = infcx.mkTyVar({ type: 'GenericArg', span: expr.span });
                        // Implicit `Self` type in `<??? as Default>::default`
                        sig.args.push(selfTy);

                        // Traits currently don't have generic parameters, so we only need to consider the last associated fn segment's generics
                        const segments = expr.callee.path.segments;
                        for (const arg of segments[segments.length - 1].args) {
                            if (arg.ty.type === 'Infer') {
                                sig.args.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                            } else {
                                sig.args.push(lowerTy(arg.ty));
                            }
                        }
                    } else {
                        bug(expr.span, `invalid callee: ${callee.type}`);
                    }


                    // with `genericArgs` created we can fix up the signature
                    for (const param of astSig.parameters) {
                        let ty: Ty;
                        if (param.type === 'Receiver') {
                            ty = selfTy!;
                            if (param.ptr) {
                                ty = { type: 'Pointer', flags: ty.flags, mtb: param.ptr, pointee: ty };
                            }
                        } else {
                            ty = lowerTy(param.ty);
                        }
                        sig.parameters.push(instantiateTy(ty, sig.args));
                    }
                    if (astSig.ret) {
                        sig.ret = instantiateTy(lowerTy(astSig.ret), sig.args);
                    }

                    instantiatedFnSigs.set(expr, sig);

                    const expectedCount = sig.parameters.length;
                    const gotCount = expr.args.length;
                    if (gotCount !== expectedCount) {
                        err(expr.span, `mismatched number of arguments; expected ${expectedCount}, got ${gotCount}`);
                    }

                    for (let i = 0; i < gotCount; i++) {
                        infcx.sub('FnArgument', expr.args[i].span, typeckExpr(expr.args[i]), sig.parameters[i]);
                    }

                    return sig.ret;
                }
                case 'Property': {
                    const target = normalize(peelInfixDerefOpTy(expr.deref, typeckExpr(expr.target), expr.span));

                    switch (target.type) {
                        case 'Record':
                            const field = target.fields.find(([k]) => k === expr.property);
                            if (!field) {
                                err(expr.span, `field '${expr.property}' not found on type ${ppTy(target)}`);
                            }
                            return field[1];
                        case 'Tuple':
                            if (typeof expr.property !== 'number') {
                                err(expr.span, 'field access on tuple must be a number');
                            }
                            if (expr.property >= target.elements.length) {
                                err(expr.span, `tried to access field ${expr.property}, but tuple only has ${target.elements.length} elements`);
                            }
                            return target.elements[expr.property];
                        default:
                            err(expr.span, `property access requires record or tuple type, got ${ppTy(target)}`);
                    }
                }
                case 'If': {
                    infcx.sub('UseInCondition', expr.condition.span, typeckExpr(expr.condition), BOOL);
                    const thenTy = typeckExpr(expr.then);
                    if (expr.else) {
                        const elseTy = typeckExpr(expr.else);
                        infcx.sub('JoinBlock', expr.span, thenTy, elseTy);
                        return thenTy;
                    } else {
                        infcx.sub('JoinBlock', expr.span, thenTy, UNIT);
                        return UNIT;
                    }
                }
                case 'While':
                    infcx.sub('UseInCondition', expr.condition.span, typeckExpr(expr.condition), BOOL);
                    typeckExpr(expr.body);
                    return UNIT;
                case 'Unary': {
                    let expectedTy: Ty;
                    let resultTy: Ty;
                    const rhsTy = typeckExpr(expr.rhs);
                    switch (expr.op) {
                        // TODO: we could(should?) allow !num
                        case TokenType.Not: expectedTy = BOOL; resultTy = BOOL; break;
                        // TODO: any signed int
                        case TokenType.Minus: expectedTy = rhsTy; resultTy = rhsTy; break;
                    }

                    infcx.sub('Unary', expr.rhs.span, rhsTy, expectedTy);
                    return resultTy;
                }
                case 'Tuple': {
                    let flags = EMPTY_FLAGS;
                    const elements: Ty[] = [];
                    for (const element of expr.elements) {
                        const ty = typeckExpr(element);
                        flags |= ty.flags;
                        elements.push(ty);
                    }
                    return { type: 'Tuple', elements, flags };
                }
                case 'Break':
                case 'Continue':
                    return { type: 'never', flags: EMPTY_FLAGS };
                case 'Match': {
                    const scrutineeTy = typeckExpr(expr.scrutinee);
                    let armTy: Ty | null = null;
                    for (const arm of expr.arms) {
                        const patTy = typeckPat(arm.pat);
                        const bodyTy = typeckExpr(arm.body);
                        if (armTy) {
                            infcx.sub('JoinBlock', arm.body.span, bodyTy, armTy)
                        } else {
                            armTy = bodyTy;
                        }
                        infcx.sub('Pattern', expr.span, patTy, scrutineeTy);
                    }
                    return armTy || NEVER;
                }
                case 'MethodCall': {
                    const targetTy = peelInfixDerefOpTy(expr.deref, typeckExpr(expr.target), expr.span);

                    // the pointe_e_ type is exclusively used for method lookup/selection
                    const derefTargetTy = targetTy.type === 'Pointer' ? targetTy.pointee : targetTy;

                    let selectedMethod = fnInLateImpl(lateImpls, derefTargetTy, expr.path.ident);

                    if (!selectedMethod) {
                        err(expr.span, `method '${expr.path.ident}' not found on ${ppTy(derefTargetTy)}`);
                    }

                    if (selectedMethod.decl.sig.parameters[0].type !== 'Receiver') {
                        err(expr.span, `selected method '${expr.path.ident}' does not have a receiver parameter`);
                    }

                    const genericArgs: Ty[] = [];
                    if (selectedMethod.decl.parent!.ofTrait) {
                        // Trait methods have an implicit `Self` generic parameter we need to add
                        genericArgs.push(targetTy);
                    }

                    if (selectedMethod.decl.parent) {
                        for (const _ of selectedMethod.decl.parent.generics) {
                            genericArgs.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                        }
                    }

                    if (expr.path.args.length > 0) {
                        for (const arg of expr.path.args) {
                            if (arg.ty.type === 'Infer') {
                                genericArgs.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                            } else {
                                genericArgs.push(lowerTy(arg.ty));
                            }
                        }
                    } else {
                        for (let i = 0; i < selectedMethod.decl.sig.generics.length; i++) {
                            const tv = infcx.mkTyVar({ type: 'GenericArg', span: expr.span });
                            genericArgs.push(tv);
                        }
                    }

                    const parameters: Ty[] = [];
                    let ret: Ty;
                    for (const param of selectedMethod.decl.sig.parameters) {
                        let ty: Ty;
                        if (param.type === 'Receiver') {
                            ty = lowerTy((selectedMethod.decl as FnDecl).parent!.selfTy);
                            if (param.ptr) {
                                ty = { type: 'Pointer', flags: ty.flags, mtb: param.ptr, pointee: ty };
                            }
                        } else {
                            ty = lowerTy(param.ty);
                        }
                        parameters.push(instantiateTy(ty, genericArgs));
                    }
                    if (selectedMethod.decl.sig.ret) {
                        ret = instantiateTy(lowerTy(selectedMethod.decl.sig.ret), genericArgs);
                    } else {
                        ret = UNIT;
                    }

                    const sig: InstantiatedFnSig = {
                        args: genericArgs,
                        parameters,
                        ret
                    };

                    instantiatedFnSigs.set(expr, sig);
                    selectedMethods.set(expr, selectedMethod);

                    if (expr.args.length !== sig.parameters.length - 1) {
                        err(expr.span, `argument length mismatch (${expr.args.length} != ${sig.parameters.length - 1})`);
                    }

                    infcx.sub('FnArgument', expr.target.span, targetTy, sig.parameters[0]);
                    for (let i = 0; i < sig.parameters.length - 1; i++) {
                        // Relate our args with the instantiated signature.
                        infcx.sub('FnArgument', expr.args[i].span, typeckExpr(expr.args[i]), sig.parameters[i + 1]);
                    }

                    return sig.ret;
                }
                default: assertUnreachable(expr);
            }
        }
        const t = inner(expr);
        if (t === undefined) {
            assert(false, `type-checking ${ppSpan(src, expr.span)} returned invalid type`);
        }
        infcx.exprTys.set(expr, t);
        return t;
    }

    function computeLUBTypes(): LUBResult {
        let errors = false;

        // we're using a simple number here that's decremented when constraining a new var
        // to save on another pass through the tyVars at the end in the happy case where everything was constrained
        let remainingInferVars = infcx.tyVars
            .reduce((prev, curr) => prev + +(curr.constrainedTy === null), 0);

        const constrainVid = (vid: number, ty: Ty) => {
            const tyvar = infcx.tyVars[vid];
            assert(tyvar.constrainedTy === null, 'tried to constrain the same TyVid twice');
            remainingInferVars--;
            tyvar.constrainedTy = ty;
            for (const constraint of tyvar.delayedConstraints) infcx.constraints.push(constraint);
        };

        function lubStep() {
            while (infcx.constraints.length > 0) {
                for (let i = infcx.constraints.length - 1; i >= 0; i--) {
                    // We iterate the constraints backwards because we sometimes add the same constraint back unchanged
                    // if we don't have enough information yet (e.g. TyVid <: TyVid).
                    // To avoid getting stuck in an infinite loop of processing the same thing that's constantly being re-added,
                    // don't use `pop()` but rather swap `i` with the last element.
                    let constraint = swapRemove(infcx.constraints, i);
                    const sub = infcx.tryResolve(constraint.sub);
                    const sup = infcx.tryResolve(constraint.sup);
                    if (constraint.depth >= MAX_CONSTRAINT_DEPTH) {
                        let pretty: string;
                        switch (constraint.type) {
                            case 'SubtypeOf':
                                // <: would be more correct, but there is currently no difference, and this is easier to understand
                                pretty = `${ppTy(sub)} == ${ppTy(sup)}`;
                                break;
                        }
                        error(
                            src, constraint.at,
                            `type error: overflow evaluating whether \`${pretty}\` holds`,
                            'consider adding type annotations to help inference'
                        );
                        errors = true;
                        continue;
                    }

                    function subFields(parent: Constraint, sub: Ty & RecordType, sup: Ty & RecordType) {
                        if (sub.fields.length !== sup.fields.length) {
                            // Fast fail: no point in comparing fields when they lengths don't match.
                            error(src, constraint.at, `type error: subtype has ${sub.fields.length} fields but supertype requires ${sup.fields.length}`);
                        } else {
                            for (let i = 0; i < sub.fields.length; i++) {
                                const subf = sub.fields[i];
                                const supf = sup.fields[i];
                                if (subf[0] !== supf[0]) {
                                    error(src, constraint.at, `type error: field '${subf[0]}' not present at index ${i} in ${ppTy(sup)}`);
                                } else {
                                    infcx.nestedSub(parent, subf[1], supf[1]);
                                }
                            }
                        }
                    }

                    switch (constraint.type) {
                        case 'SubtypeOf':
                            // Trivial cases which are always true without requiring nested constraints:
                            if (
                                // int == int of same size & signedness
                                (sub.type === 'int' && sup.type === 'int' && sub.value.bits === sup.value.bits && sub.value.signed === sup.value.signed)
                                // bool == bool
                                || (sub.type === 'bool' && sup.type === 'bool')
                                // same type parameters
                                || (sub.type === 'TyParam' && sup.type === 'TyParam' && sub.id === sup.id)
                                || (sub.type === 'str' && sup.type === 'str')
                                || (sub.type === 'Enum' && sup.type === 'Enum' && sub.decl === sup.decl)
                            ) {
                                // OK
                            } else if (sub.type === 'Record' && sup.type === 'Record') {
                                subFields(constraint, sub, sup);
                            } else if (sub.type === 'Tuple' && sup.type === 'Tuple') {
                                if (sub.elements.length !== sup.elements.length) {
                                    error(src, constraint.at, `type error: tuple size mismatch (${sub.elements.length} != ${sup.elements.length})`);
                                } else {
                                    for (let i = 0; i < sub.elements.length; i++) {
                                        const subf = sub.elements[i];
                                        const supf = sup.elements[i];
                                        infcx.nestedSub(constraint, subf, supf);
                                    }
                                }
                            } else if (sub.type === 'Array' && sup.type === 'Array') {
                                if (sub.len !== sup.len) {
                                    error(src, constraint.at, `type error: array length mismatch (${sub.len} != ${sup.len})`);
                                }
                                infcx.nestedSub(constraint, sub.elemTy, sup.elemTy);
                            } else if (sub.type === 'Pointer' && sup.type === 'Pointer') {
                                infcx.nestedSub(constraint, sub.pointee, sup.pointee);
                            } else if (sub.type === 'Record' && sup.type === 'Alias') {
                                // TODO: also check args
                                const nsup = normalize(sup);
                                if (nsup.type === 'Record') {
                                    if (
                                        sup.decl.constructibleIn.length > 0
                                        // Can only unify if the constraint was added in any of the specified functions.
                                        // TODO: actually check this. figure out how to get the parentFn here
                                        && !sup.decl.constructibleIn.some((v) => true)
                                    ) {
                                        error(src, constraint.at, `error: '${sup.decl.name}' cannot be constructed here`);
                                    }
                                    subFields(constraint, sub, nsup);
                                }
                            } else if (sub.type === 'Alias' && sup.type === 'Alias') {
                                // TODO: check constructibleIn for both aliases
                                infcx.nestedSub(constraint, normalize(sub), normalize(sup));
                            } else if (sub.type === 'Alias') {
                                infcx.nestedSub(constraint, normalize(sub), normalize(sup));
                            } else if ((sub.type === 'TyVid' && sup.type !== 'TyVid') || (sup.type === 'TyVid' && sub.type !== 'TyVid')) {
                                let tyvid: { type: 'TyVid' } & Ty;
                                let other: Ty;

                                if (sub.type === 'TyVid') {
                                    tyvid = sub;
                                    other = sup;
                                } else if (sup.type === 'TyVid') {
                                    tyvid = sup;
                                    other = sub;
                                } else {
                                    throw 'unreachable';
                                }

                                if (infcx.tyVars[tyvid.id].origin.type === 'IntegerLiteral' && other.type !== 'int') {
                                    // attempting to constrain an integer variable to a non-int type
                                    const msub = sub === tyvid ? '{{integer}}' : ppTy(sub);
                                    const msup = sup === tyvid ? '{{integer}}' : ppTy(sup);
                                    error(src, constraint.at, `type error: ${msub} is not assignable to ${msup}`);
                                    errors = true;
                                } else {
                                    constrainVid(tyvid.id, other);
                                }
                            } else if (sub.type === 'TyVid' && sup.type === 'TyVid') {
                                // Both related types are type variables, can't progress; delay them
                                infcx.tyVars[sub.id].delayedConstraints.push(constraint);
                                infcx.tyVars[sup.id].delayedConstraints.push(constraint);
                            }
                            else if (sub.type === 'never') {
                                // OK. Never is a subtype of all types.
                            } else {
                                // Error case.

                                let message: string;
                                switch (constraint.cause) {
                                    case 'Binary':
                                        message = `left-hand side and right-hand side must be of the same type, got ${sub.type} and ${sup.type}`;
                                        break;
                                    default: message = `${ppTy(sub)} is not assignable to ${ppTy(sup)}`;
                                }

                                error(src, constraint.at, `type error: ${message}`);
                                errors = true;
                            }
                            break;
                        default: assertUnreachable(constraint.type)
                    }
                }
            }
        }

        // Initial LUB check: pre-fallback.
        // After this, any type variable with no fallback *should* have been constrained to a specific type.
        lubStep();

        if (remainingInferVars > 0) {
            // We have remaining infer variables; this either means fallback needs to apply (for integer types specifically)
            // or we tell the user that type annotations are needed if there is no fallback
            // Note that if fallback did apply at least once, we do want to allow normal unconstrained type variables.
            // This can happen when relating a type variable and an integer variable, which should work.

            let fallbackApplied = false;
            for (let i = 0; i < infcx.tyVars.length; i++) {
                const tyvar = infcx.tyVars[i];
                if (!tyvar.constrainedTy) {
                    const fallback = originFallback(tyvar.origin);

                    if (fallback) {
                        if (options.verbose) {
                            console.log(`fallback @ ${ppSpan(src, tyVarOriginSpan(tyvar.origin))}`);
                        }
                        constrainVid(i, fallback);
                        fallbackApplied = true;
                    }
                }
            }

            function reportTypeAnnotationsNeeded() {
                for (const tyvar of infcx.tyVars) {
                    if (!tyvar.constrainedTy && !tyVarHasFallback(tyvar)) {
                        error(src, tyVarOriginSpan(tyvar.origin), 'type error: type annotations needed');
                        errors = true;
                    }
                }
            }

            if (!fallbackApplied) {
                // If fallback did not even apply once, we will not make any progress in any further lubStep call,
                // so emit an error here.
                reportTypeAnnotationsNeeded();
            }

            if (!errors) {
                // If errors didn't occur (implying that fallback occurred), we can make more progress.
                lubStep();

                if (remainingInferVars > 0) {
                    // If we *still* have remaining infer vars after applying fallback, give up. There's nothing else we can do.
                    reportTypeAnnotationsNeeded();
                }
            }
        }

        return { hadErrors: errors }
    }

    for (const stmt of ast.stmts) {
        typeckStmt(stmt);
    }

    const lub = computeLUBTypes();

    function instantiateTyVars(ty: Ty): Ty {
        if (!hasTyVid(ty)) return ty;

        const instantiateMany = (tys: Ty[]): { instantiated: Ty[], flags: number } => {
            let flags = EMPTY_FLAGS;
            const instantiated: Ty[] = [];
            for (const ty of tys) {
                const inst = instantiateTyVars(ty);
                flags |= inst.flags;
                instantiated.push(inst);
            }
            return { instantiated, flags };
        }

        switch (ty.type) {
            case 'Alias': {
                const { flags, instantiated: args } = instantiateMany(ty.args);
                return { ...ty, flags, args };
            }
            case 'Array': {
                const elemTy = instantiateTyVars(ty.elemTy);
                return { ...ty, flags: elemTy.flags, elemTy };
            }
            case 'TyVid':
                // the constrained type might itself reference other type variables, see tests/later-infer.chg for a full example
                return instantiateTyVars(infcx.tyVars[ty.id].constrainedTy!);
            case 'FnDef':
            case 'ExternFnDef':
            case 'TraitFn':
                spanless_bug('cannot instantiate FnDef, this should be handled separately for fn calls');
            case 'int':
            case 'str':
            case 'TyParam':
            case 'bool':
            case 'never': return ty;
            case 'Pointer': {
                const pointee = instantiateTyVars(ty.pointee);
                return { ...ty, flags: pointee.flags, pointee }
            };
            case 'Record': {
                let flags = EMPTY_FLAGS;
                const fields: [string, Ty][] = [];
                for (const [k, v] of ty.fields) {
                    const inst = instantiateTyVars(v);
                    flags |= inst.flags;
                    fields.push([k, inst]);
                }
                return { ...ty, flags, fields };
            }
            case 'Tuple': {
                const { flags, instantiated: elements } = instantiateMany(ty.elements);
                return { ...ty, flags, elements };
            }
            case 'Enum': return ty;
            default: assertUnreachable(ty);
        }
    }

    function writebackExpr(expr: Expr) {
        let ty = infcx.exprTys.get(expr)!;
        switch (expr.type) {
            case 'FnCall':
            case 'MethodCall':
                const uninstantiatedSig = instantiatedFnSigs.get(expr)!;
                instantiatedFnSigs.set(expr, {
                    args: uninstantiatedSig.args.map(instantiateTyVars),
                    parameters: uninstantiatedSig.parameters.map(instantiateTyVars),
                    ret: instantiateTyVars(uninstantiatedSig.ret)
                });
                break;
        }

        if (hasTyVid(ty)) {
            const instantiated = instantiateTyVars(ty);
            infcx.exprTys.set(expr, instantiated);
        }
    }

    function writebackStmt(stmt: Stmt) {
        if (stmt.type === 'LetDecl') {
            const ty = patTys.get(stmt)!;
            if (hasTyVid(ty)) {
                const instantiated = instantiateTyVars(ty);
                patTys.set(stmt, instantiated);
            }
        }
    }

    // Now that all type variables have been constrained, populate the various maps.
    // Writeback assumes there were no errors and all ty vars were fully constrained, which may not be the case with errors
    if (!lub.hadErrors) {
        for (const stmt of ast.stmts) visitInStmt(stmt, writebackExpr, writebackStmt);
    }

    return { infcx, loweredTys, exprTys: infcx.exprTys, instantiatedFnSigs, patTys, selectedMethods: selectedMethods, hadErrors: lub.hadErrors, impls: lateImpls };
}
