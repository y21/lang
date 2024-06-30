import { options } from "./cli";
import { LetDecl, FnParameter, AstTy, Expr, AstFnSignature, RecordFields, Stmt, Program, FnDecl, PathSegment, Pat } from "./parse";
import { Resolutions, PrimitiveTy, BindingPat } from "./resolve";
import { Span } from "./span";
import { TokenType } from "./token";
import { Ty, UNIT, isUnit, BOOL, U64, RecordType, hasTyVid, EMPTY_FLAGS, TYPARAM_MASK, TYVID_MASK, instantiateTy, ppTy, normalize, I32, STR_SLICE } from "./ty";
import { assert, assertUnreachable, todo } from "./util";
import { forEachExprInStmt } from "./visit";

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'Binary' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index' | 'FnArgument' | 'UseInCondition' | 'Unary' | 'Pattern';
type Constraint = { cause: ConstraintCause, at: Span, depth: number } & ConstraintType;
const MAX_CONSTRAINT_DEPTH = 200;

type FnLocalState = {
    expectedReturnTy: Ty;
    returnFound: boolean;
    // TODO: move away from localTypes and to patTypes, once LetDecl is implemented in terms of patterns
    localTypes: Map<LetDecl | FnParameter, Ty>;
    patTypes: Map<BindingPat, Ty>;
};

export type TypeckResults = {
    infcx: Infcx,
    loweredTys: Map<AstTy, Ty>,
    instantiatedFnSigs: Map<Expr, InstantiatedFnSig>,
    exprTys: Map<Expr, Ty>,
    hadErrors: boolean
};

export type InstantiatedFnSig = {
    parameters: Ty[],
    ret: Ty,
    args: Ty[]
};

type InfTyVar = {
    constrainedTy: Ty | null,
    origin: TyVarOrigin,
};
type TyVarOrigin = ({ type: 'Expr', expr: Expr } | { type: 'GenericArg', span: Span }) | { type: 'BindingPat', span: Span };
function tyVarOriginSpan(origin: TyVarOrigin): Span {
    switch (origin.type) {
        case 'Expr': return origin.expr.span;
        case 'GenericArg': return origin.span;
        case 'BindingPat': return origin.span;
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
        this.tyVars.push({ constrainedTy: null, origin });
        const ty: Ty = { type: 'TyVid', flags: TYVID_MASK, id };
        if (origin.type === 'Expr') {
            this.exprTys.set(origin.expr, ty);
        }
        return ty;
    }

    withFn(expect: Ty | undefined, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect || UNIT, returnFound: false, localTypes: new Map(), patTypes: new Map() });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (!isUnit(expectedReturnTy) && !returnFound) {
            throw `Expected ${expectedReturnTy.type}, got ()`;
        }
    }

    registerLocal(decl: LetDecl, ty: Ty) {
        this.fnStack[this.fnStack.length - 1].localTypes.set(decl, ty);
    }

    registerPat(pat: BindingPat, ty: Ty) {
        this.fnStack[this.fnStack.length - 1].patTypes.set(pat, ty);
    }

    localTy(decl: LetDecl | FnParameter): Ty | undefined {
        return this.fnStack[this.fnStack.length - 1].localTypes.get(decl);
    }

    patTy(pat: BindingPat): Ty | undefined {
        return this.fnStack[this.fnStack.length - 1].patTypes.get(pat);
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

function error(src: string, span: Span, message: string, note?: string) {
    const red = (text: string) => options.colors ? `\x1b[1;31m${text}\x1b[0m` : text;

    let lineStart = src.lastIndexOf('\n', span[0]);
    let lineEnd = src.indexOf('\n', span[1]);
    const col = span[0] - lineStart;
    const snipLen = span[1] - span[0];
    const line = src.substring(lineStart, lineEnd);

    console.error('');
    console.error(line);
    console.error(' '.repeat(col - 1) + red(
        '^'.repeat(snipLen) +
        `  ${message}`));
    if (note) {
        console.error();
        console.error('note: ' + note);
    }
}

export function typeck(src: string, ast: Program, res: Resolutions): TypeckResults {
    const infcx = new Infcx();
    const loweredTys = new Map<AstTy, Ty>();
    const instantiatedFnSigs = new Map<Expr, InstantiatedFnSig>();

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
                case 'Alias': throw new Error('cannot lower type aliases directly');
                case 'Infer': throw new Error('cannot lower `_` here');
                case 'Enum': return { type: 'Enum', flags: EMPTY_FLAGS, decl: ty };
                default: assertUnreachable(ty);
            }
        }
        lowered = lowerInner(ty);
        loweredTys.set(ty, lowered);
        return lowered;
    }

    function typeckFn(decl: FnDecl) {
        const ret = decl.sig.ret && lowerTy(decl.sig.ret);
        infcx.withFn(ret, () => { typeckExpr(decl.body); });
    }

    function typeckStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': typeckFn(stmt); break;
            case 'Expr': typeckExpr(stmt.value); break;
            case 'LetDecl': {
                const rety = typeckExpr(stmt.init);
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
                    infcx.registerLocal(stmt, annotatedTy);
                } else {
                    infcx.registerLocal(stmt, rety);
                }
                break;
            }
            case 'TyAlias': break;
            case 'ExternFnDecl': if (stmt.sig.ret) lowerTy(stmt.sig.ret); break;
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
                            return ty;
                        }
                        case 'Variant': return { type: 'Enum', decl: pathres.enum, flags: EMPTY_FLAGS };
                    }
                } else {
                    throw new Error('unknown res in pattern');
                }
            }
        }
    }

    function typeckExpr(expr: Expr): Ty {
        function inner(expr: Expr): Ty {
            switch (expr.type) {
                case 'Block': for (const stmt of expr.stmts) typeckStmt(stmt); return UNIT;
                case 'Path': {
                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        // TODO: is EMPTY_FLAGS correct here..?
                        case 'FnDecl': return { type: 'FnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'ExternFnDecl': return { type: 'ExternFnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'LetDecl': return infcx.localTy(litres)!;
                        case 'FnParam': return lowerTy(litres.param.ty);
                        case 'Variant': return { type: 'Enum', decl: litres.enum, flags: EMPTY_FLAGS };
                        case 'Binding': return infcx.patTy(litres)!;
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
                        throw `Cannot index into ${target.type}`
                    }
                }
                // TODO: typescript's "as const" can create a literal type?
                case 'Number': return { type: 'int', flags: EMPTY_FLAGS, value: expr.suffix };
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
                        throw `Attempted to dereference non-pointer type ${pointee.type}`;
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
                    const sig = (() => {
                        const callee = typeckExpr(expr.callee);
                        if (callee.type !== 'FnDef' && callee.type !== 'ExternFnDef') {
                            throw new Error('callee must be a FnDef');
                        }

                        // HACK: create the signature with dummy data so that we have an object reference to stick into the ty var
                        const sig: InstantiatedFnSig = {
                            parameters: [],
                            ret: UNIT,
                            args: []
                        };

                        let segments: PathSegment<AstTy>[];
                        let segment: PathSegment<AstTy>;

                        if (
                            expr.callee.type === 'Path'
                            && (segments = expr.callee.path.segments)
                            && (segment = segments[segments.length - 1])
                            && segment.args.length > 0
                        ) {
                            sig.args = segment.args.map(ty => {
                                return ty.ty.type === 'Infer'
                                    ? infcx.mkTyVar({ type: 'GenericArg', span: expr.span })
                                    : lowerTy(ty.ty)
                            });
                        } else {
                            for (let i = 0; i < callee.decl.sig.generics.length; i++) {
                                const tv = infcx.mkTyVar({ type: 'GenericArg', span: expr.span });
                                sig.args.push(tv);
                            }
                        }

                        // with `genericArgs` created we can fix up the signature
                        for (const param of callee.decl.sig.parameters) {
                            const ty = lowerTy(param.ty);
                            sig.parameters.push(instantiateTy(ty, sig.args));
                        }
                        if (callee.decl.sig.ret) {
                            sig.ret = instantiateTy(lowerTy(callee.decl.sig.ret), sig.args);
                        }

                        return sig;
                    })();
                    instantiatedFnSigs.set(expr, sig);

                    const expectedCount = sig.parameters.length;
                    const gotCount = expr.args.length;
                    if (gotCount !== expectedCount) {
                        throw new Error(`mismatched number of arguments; expected ${expectedCount}, got ${gotCount}`);
                    }

                    for (let i = 0; i < gotCount; i++) {
                        infcx.sub('FnArgument', expr.args[i].span, typeckExpr(expr.args[i]), sig.parameters[i]);
                    }

                    return sig.ret;
                }
                case 'Property':
                    const target = normalize(typeckExpr(expr.target));
                    switch (target.type) {
                        case 'Record':
                            const field = target.fields.find(([k]) => k === expr.property);
                            if (!field) {
                                throw new Error(`field '${expr.property}' not found on type ${ppTy(target)}`);
                            }
                            return field[1];
                        case 'Tuple':
                            if (typeof expr.property !== 'number') {
                                throw new Error('field access on tuple must be a number');
                            }
                            if (expr.property >= target.elements.length) {
                                throw new Error(`tried to access field ${expr.property}, but tuple only has ${target.elements.length} elements`);
                            }
                            return target.elements[expr.property];
                        default:
                            throw new Error(`property access requires record or tuple type, got ${ppTy(target)}`);
                    }
                case 'If':
                    infcx.sub('UseInCondition', expr.condition.span, typeckExpr(expr.condition), BOOL);
                    typeckExpr(expr.then);
                    if (expr.else) {
                        typeckExpr(expr.else);
                    }
                    return UNIT;
                case 'While':
                    infcx.sub('UseInCondition', expr.condition.span, typeckExpr(expr.condition), BOOL);
                    typeckExpr(expr.body);
                    return UNIT;
                case 'Unary': {
                    let expectedTy: Ty;
                    let resultTy: Ty;
                    switch (expr.op) {
                        // TODO: we could(should?) allow !num
                        case TokenType.Not: expectedTy = BOOL; resultTy = BOOL; break;
                    }

                    infcx.sub('Unary', expr.rhs.span, typeckExpr(expr.rhs), expectedTy);
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
                    for (const arm of expr.arms) {
                        const patTy = typeckPat(arm.pat);
                        typeckExpr(arm.body);
                        infcx.sub('Pattern', expr.span, patTy, scrutineeTy);
                    }
                    return UNIT;
                }
                default: assertUnreachable(expr);
            }
        }
        const t = inner(expr);
        infcx.exprTys.set(expr, t);
        return t;
    }

    function computeLUBTypes(): LUBResult {
        let errors = false;
        let madeProgress = true;
        // we're using a simple number here that's decremented when constraining a new var
        // to save on another pass through the tyVars at the end in the happy case where everything was constrained
        let remainingInferVars = infcx.tyVars.reduce((prev, curr) => prev + +(curr.constrainedTy === null), 0);
        assert(remainingInferVars === infcx.tyVars.length, 'cannot call computeLUBTypes() with already constrained infer vars');

        const constrainVid = (vid: number, ty: Ty) => {
            assert(infcx.tyVars[vid].constrainedTy === null, 'tried to constrain the same TyVid twice');
            remainingInferVars--;
            infcx.tyVars[vid].constrainedTy = ty;
            madeProgress = true;
        };

        while (madeProgress && infcx.constraints.length > 0) {
            for (let i = infcx.constraints.length - 1; i >= 0; i--) {
                const constraint = infcx.constraints.pop()!;
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
                        madeProgress = true;
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

                            constrainVid(tyvid.id, other);
                        } else if (sub.type === 'TyVid' && sup.type === 'TyVid') {
                            // Both related types are type variables, can't progress
                            infcx.nestedSub(constraint, sub, sup);
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

        if (infcx.constraints.length > 0) {
            throw new Error('LUB compute got stuck making no progress but there are still constraints!');
        }

        if (remainingInferVars > 0) {
            for (const tyvar of infcx.tyVars) {
                if (tyvar.constrainedTy === null) {
                    error(src, tyVarOriginSpan(tyvar.origin), `type error: unconstrained type variable created here`)
                    errors = true;
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
                throw new Error('cannot instantiate FnDef, this should be handled separately for fn calls');
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

    // Now that all type variables have been constrained, populate the various maps.
    function writebackExpr(expr: Expr) {
        let ty = infcx.exprTys.get(expr)!;
        switch (expr.type) {
            case 'FnCall':
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
    if (!lub.hadErrors) {
        // Writeback assumes there were no errors and all ty vars were fully constrained, which may not be the case with errors
        for (const stmt of ast.stmts) forEachExprInStmt(stmt, writebackExpr);
    }

    return { infcx, loweredTys, exprTys: infcx.exprTys, instantiatedFnSigs, hadErrors: lub.hadErrors };
}
