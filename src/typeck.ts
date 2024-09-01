import { options } from "./cli";
import { itemInLateImpl, LateImplLookupResult, LateImpls } from "./impls";
import { LetDecl, FnParameter, AstTy, Expr, AstFnSignature, RecordFields, Stmt, Module, FnDecl, PathSegment, Pat, Impl, ImplItem, Generics, Trait, Path, GenericArg, WhereClause } from "./parse";
import { Resolutions, PrimitiveTy, BindingPat, TypeResolution, TraitFn } from "./resolve";
import { SourceMap, Span, ppSpan, shrinkToHi } from "./span";
import { TokenType } from "./token";
import { Ty, UNIT, isUnit, BOOL, U64, RecordType, hasTyVid, EMPTY_FLAGS, TYPARAM_MASK, TYVID_MASK, instantiateTy, ppTy, normalize, I32, STR_SLICE, U8, NEVER, flagsOfTys, withoutTyVid } from "./ty";
import { assert, assertUnreachable, expectLast, getOrInsert, inspect, swapRemove, todo } from "./util";
import { visitInStmt } from "./visit";
import { bug, err, emitErrorRaw as error, spanless_bug, Suggestion } from './error';

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'Binary' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index' | 'FnArgument' | 'UseInCondition' | 'Unary' | 'Pattern' | 'JoinBlock' | 'MethodCallReceiver';
type Constraint = { cause: ConstraintCause, at: Span, depth: number } & ConstraintType;
const MAX_CONSTRAINT_DEPTH = 200;

type FnLocalState = {
    expectedReturnTy: Ty;
    whereClause: LoweredWhereClause,
    returnFound: boolean;
};

export type LoweredTypeBound = { type: 'TraitImpl', ty: Ty, trait: Trait };
export type LoweredWhereClause = { bounds: LoweredTypeBound[] };
export type TypeckTypeRelativeResolution = { type: 'FnDef', value: FnDecl } | { type: 'TraitFn', value: TraitFn };
const EMPTY_WHERE_CLAUSE: LoweredWhereClause = { bounds: [] };

export type TypeckResults = {
    infcx: Infcx,
    loweredTys: Map<AstTy, Ty>,
    instantiatedFnSigs: Map<Expr, InstantiatedFnSig>,
    exprTys: Map<Expr, Ty>,
    patTys: Map<LetDecl | FnParameter | BindingPat, Ty>,
    typeRelativeResolutions: Map<TypeResolution, TypeckTypeRelativeResolution>,
    selectedMethods: Map<Expr, { type: 'Fn' } & ImplItem>,
    hadErrors: boolean,
    coercions: Map<Expr, Coercion[]>,
    impls: LateImpls
};

// Gets the **coerced** type of an expression. This is pretty much almost always what you want (over only looking into exprTys).
export function exprTy(typeck: TypeckResults, expr: Expr) {
    let ty: Ty = typeck.exprTys.get(expr) || bug(expr.span, 'no type recorded for expression');

    let coercions: Coercion[] | undefined;
    if (coercions = typeck.coercions.get(expr)) {
        for (const coercion of coercions) {
            ty = coercion.to;
        }
    }

    return ty;
}

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
    // Used for coercions
    constraintToExpr: Map<Constraint, Expr> = new Map();

    constructor() { }

    // Require `sub` to be a subtype of `sup` but disallow coercing it.
    // You should only really use it when you don't have an expression. Otherwise use `subCoerce`
    subNoCoerce(cause: ConstraintCause, at: Span, sub: Ty, sup: Ty) {
        const constraint: Constraint = { type: 'SubtypeOf', at, cause, sub, sup, depth: 0 };
        this.constraints.push(constraint);
    }
    // Prefer using this over `subNoCoerce` when possible.
    subCoerce(cause: ConstraintCause, expr: Expr, sub: Ty, sup: Ty) {
        const constraint: Constraint = { type: 'SubtypeOf', at: expr.span, cause, sub, sup, depth: 0 };
        this.constraintToExpr.set(constraint, expr);
        this.constraints.push(constraint);
    }

    nestedSubNoCoerce(parent: Constraint, sub: Ty, sup: Ty, at?: Span) {
        this.constraints.push({ type: 'SubtypeOf', at: at || parent.at, cause: parent.cause, depth: parent.depth + 1, sub, sup });
    }

    // You should call this if the nested constraint has an associated expression and the nested constraint
    // still essentially represents the same expression.
    nestedSubCoerce(parent: Constraint, sub: Ty, sup: Ty, at?: Span) {
        const constraint: Constraint = { type: 'SubtypeOf', at: at || parent.at, cause: parent.cause, depth: parent.depth + 1, sub, sup };
        this.constraints.push(constraint);
        let parentExpr: Expr | undefined;
        if (parentExpr = this.constraintToExpr.get(parent)) {
            this.constraintToExpr.set(constraint, parentExpr);
        }
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

    withFn(expect: Ty | undefined, whereClause: LoweredWhereClause, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect || UNIT, returnFound: false, whereClause });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (!isUnit(expectedReturnTy) && !returnFound) {
            spanless_bug(`expected ${expectedReturnTy.type}, got ()`);
        }
    }

    registerReturn(expr: Expr, ty: Ty) {
        const fs = this.fnStack[this.fnStack.length - 1];
        fs.returnFound = true;
        const sup = fs.expectedReturnTy;
        this.subCoerce('Return', expr, ty, sup);
    }

    tryResolve(ty: Ty): Ty {
        if (ty.type === 'TyVid' && this.tyVars[ty.id].constrainedTy) {
            return this.tyVars[ty.id].constrainedTy!;
        }
        return ty;
    }

    whereClause(): LoweredWhereClause {
        return expectLast(this.fnStack).whereClause;
    }

    expectConstraintExpr(c: Constraint): Expr {
        const e = this.constraintToExpr.get(c);
        if (!e) {
            spanless_bug(`expected constraint ${inspect(c)} to have an associated expr but it did not`)
        }
        return e;
    }
}

export function returnTy(sig: AstFnSignature, typeck: TypeckResults): Ty {
    return sig.ret ? typeck.loweredTys.get(sig.ret)! : UNIT;
}

export type Coercion = {
    type: 'Autoref',
    to: Ty
} | {
    type: 'UnsizeArray',
    to: { type: 'Pointer', pointee: { type: 'Slice' } } & Ty
};

export function typeck(sm: SourceMap, ast: Module, res: Resolutions): TypeckResults {
    const infcx = new Infcx();
    const loweredTys = new Map<AstTy, Ty>();
    const instantiatedFnSigs = new Map<Expr, InstantiatedFnSig>();
    // TODO: move away from LetDecl | FnParam, once LetDecl | FnParam is implemented in terms of patterns
    const patTys: Map<LetDecl | FnParameter | BindingPat, Ty> = new Map();
    const selectedMethods: Map<Expr, { type: 'Fn' } & ImplItem> = new Map();
    const coercions: Map<Expr, Coercion[]> = new Map();
    const addCoercion = (expr: Expr, coercion: Coercion) => {
        if (coercions.has(expr)) coercions.get(expr)!.push(coercion);
        coercions.set(expr, [coercion]);
    }
    const typeRelativeResolutions: Map<TypeResolution, TypeckTypeRelativeResolution> = new Map();

    const lateImpls: LateImpls = res.impls.map(([ty, impl]) => {
        return [lowerTy(ty), impl]
    });

    function lowerTyResolution(res: TypeResolution, span: Span, genericArgs: GenericArg<AstTy>[]): Ty {
        switch (res.type) {
            case 'TyParam': return { type: 'TyParam', flags: TYPARAM_MASK, id: res.id, parentItem: res.parentItem };
            case 'Primitive': switch (res.kind) {
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
                default: assertUnreachable(res.kind)
            }
            case 'TyAlias':
                const args: Ty[] = [];
                let flags = EMPTY_FLAGS;
                for (const arg of genericArgs) {
                    const lowered = lowerTy(arg.ty);
                    flags |= lowered.flags;
                    args.push(lowered);
                }
                return { type: 'Alias', flags, decl: res, alias: lowerTy(res.alias), args };
            case 'Enum': return { type: 'Enum', flags: EMPTY_FLAGS, decl: res };
            case 'Mod': bug(span, 'cannot lower module as a type');
            case 'Trait': bug(span, `expected type, got trait ${inspect(res)}`);
            case 'Self': return lowerTy(res.selfTy);
            case 'Root': bug(span, 'cannot lower root paths');
            case 'TypeRelative': {
                // TODO: once we have associated types, this path will be reachable
                bug(span, 'there are no type-relative types');
            }
            default: assertUnreachable(res)
        }
    }

    function lowerWhereClause(where: WhereClause): LoweredWhereClause {
        const bounds: LoweredTypeBound[] = [];
        for (const bound of where.bounds) {
            const ty = lowerTy(bound.ty);
            for (const astTrait of bound.traits) {
                const trait = res.tyResolutions.get(astTrait);
                if (!trait || trait.type !== 'Trait') {
                    spanless_bug('trait bound path must point to a trait, got: ' + trait);
                }
                bounds.push({ ty, trait, type: 'TraitImpl' });
            }
        }
        return { bounds };
    }

    function lowerTy(ty: AstTy): Ty {
        let lowered = loweredTys.get(ty);
        if (lowered) return lowered;

        function lowerInner(ty: AstTy): Ty {
            switch (ty.type) {
                case 'Path': {
                    const tyres = res.tyResolutions.get(ty)!;
                    // TODO: this looks questionable
                    return lowerTyResolution(tyres, ty.span, ty.value.segments[ty.value.segments.length - 1]?.args);
                }
                case 'Array': {
                    const elemTy = lowerTy(ty.elemTy);
                    return { type: 'Array', flags: elemTy.flags, elemTy, len: ty.len };
                }
                case 'Slice': {
                    const elemTy = lowerTy(ty.elemTy);
                    return { type: 'Slice', flags: elemTy.flags, elemTy };
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
        infcx.withFn(ret, decl.where ? lowerWhereClause(decl.where) : EMPTY_WHERE_CLAUSE, () => { typeckExpr(decl.body); });
    }

    function typeckStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': typeckFn(stmt); break;
            case 'Expr': typeckExpr(stmt.value); break;
            case 'LetDecl': {
                const rety = stmt.init === null ? infcx.mkTyVar({ type: 'Let', span: stmt.span }) : typeckExpr(stmt.init);
                if (stmt.ty) {
                    const annotatedTy = lowerTy(stmt.ty);

                    if (stmt.init) {
                        infcx.subCoerce('Assignment', stmt.init, rety, annotatedTy);
                    } else {
                        infcx.subNoCoerce('Assignment', stmt.span, rety, annotatedTy);
                    }

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
                    function pushSegmentGenerics(genericCount: number, segment: PathSegment<AstTy>, into: Ty[]) {
                        if (segment.args.length > 0) {
                            if (segment.args.length !== genericCount) {
                                error(
                                    sm,
                                    expr.span,
                                    'generic argument count mismatch',
                                    `item is declared with ${genericCount} generic parameters, but ${segment.args.length} were specified`
                                );
                            }
                            into.push(...segment.args.map(g => lowerTy(g.ty)));
                        } else {
                            // ::<> not present at all, insert ty vars
                            for (let i = 0; i < genericCount; i++) {
                                into.push(infcx.mkTyVar({ type: 'GenericArg', span: expr.span }));
                            }
                        }
                    }


                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        case 'FnDecl': {
                            // free_fn()
                            const args: Ty[] = [];
                            assert(litres.parent === null, 'FnDecl resolution must be a free function, but got one with a parent impl');
                            pushSegmentGenerics(litres.sig.generics.length, expectLast(expr.path.segments), args);
                            return { type: 'FnDef', flags: flagsOfTys(args), decl: litres, args };
                        }
                        case 'ExternFnDecl': {
                            const args: Ty[] = [];
                            pushSegmentGenerics(litres.sig.generics.length, expectLast(expr.path.segments), args);
                            return { type: 'ExternFnDef', flags: EMPTY_FLAGS, decl: litres, args };
                        }
                        case 'TraitFn': {
                            // Trait::assoc()

                            // Self type is an inference variable.
                            const args: Ty[] = [infcx.mkTyVar({ type: 'GenericArg', span: expr.span })];

                            pushSegmentGenerics(litres.value.sig.generics.length, expectLast(expr.path.segments), args);
                            return { type: 'TraitFn', value: litres.value, flags: flagsOfTys(args), args };
                        }
                        case 'LetDecl':
                        case 'Binding': return patTys.get(litres)!;
                        case 'FnParam': return patTys.get(litres.param)!;
                        case 'Variant': return lowerTy(litres.enum);
                        case 'TypeRelative': {
                            const ty = lowerTyResolution(litres.ty, expr.span, litres.tyArgs);
                            if (litres.segments.length != 1) {
                                bug(expr.span, 'type relative path must have exactly one trailing segment, got: ' + inspect(litres.segments));
                            }

                            if (ty.type === 'TyParam') {
                                const where = infcx.whereClause();
                                const res = itemInLateImpl(lateImpls, ty, litres.segments[0].ident, where);
                                if (!res || res.type !== 'TraitItem') {
                                    bug(expr.span, 'generic type relative lookup was not a trait item')
                                }
                                const args: Ty[] = [ty];
                                pushSegmentGenerics(res.value.sig.generics.length, litres.segments[0], args);
                                const traitFn: Ty = { type: 'TraitFn', args, flags: flagsOfTys(args), value: { parentTrait: res.trait, sig: res.value.sig } };
                                typeRelativeResolutions.set(litres, traitFn);
                                return traitFn;
                            }

                            const lookupResult = itemInLateImpl(lateImpls, ty, litres.segments[0].ident) as ({ type: 'ImplItem' } & LateImplLookupResult) | null;
                            if (!lookupResult) {
                                bug(expr.span, `item '${litres.segments[0].ident}' not found on type ${ppTy(ty)}`);
                            }
                            const { value: item } = lookupResult;
                            if (!item.decl.parent) {
                                bug(item.decl.body.span, 'associated function has no parent impl')
                            }

                            const tyAndItem = expr.path.segments.slice(-2);

                            if (item.decl.parent.ofTrait) {
                                const trait = res.tyResolutions.get(item.decl.parent.ofTrait) as Trait;
                                const args: Ty[] = [
                                    ty // self type
                                ];

                                // Self generic arg has already been added and it also cannot be named with generic args
                                pushSegmentGenerics(item.decl.parent.generics.length, tyAndItem[0], args);
                                pushSegmentGenerics(item.decl.sig.generics.length, tyAndItem[1], args);

                                const relRes: Ty = { type: 'TraitFn', flags: flagsOfTys(args), value: { parentTrait: trait, sig: item.decl.sig }, args };
                                typeRelativeResolutions.set(litres, relRes);
                                return relRes;
                            } else {
                                const args: Ty[] = [];

                                pushSegmentGenerics(item.decl.parent.generics.length, tyAndItem[0], args);
                                pushSegmentGenerics(item.decl.sig.generics.length, tyAndItem[1], args);

                                typeRelativeResolutions.set(litres, { type: 'FnDef', value: item.decl });
                                return { type: 'FnDef', decl: item.decl, flags: flagsOfTys(args), args };
                            }
                        }
                        default: assertUnreachable(litres);
                    }
                }
                case 'Return': {
                    const ret = typeckExpr(expr.value);
                    infcx.registerReturn(expr, ret);
                    return { type: 'never', flags: EMPTY_FLAGS };
                }
                case 'ArrayLiteral': {
                    let elemTy: Ty;
                    if (expr.elements.length === 0) {
                        elemTy = infcx.mkTyVar({ type: "Expr", expr });
                    } else {
                        elemTy = typeckExpr(expr.elements[0]);
                        for (let i = 1; i < expr.elements.length; i++) infcx.subCoerce('ArrayLiteral', expr.elements[i], typeckExpr(expr.elements[i]), elemTy);
                    }
                    return { type: 'Array', flags: elemTy.flags, elemTy, len: expr.elements.length };
                }
                case 'ArrayRepeat': {
                    const elemTy = typeckExpr(expr.element);
                    return { type: 'Array', elemTy, flags: elemTy.flags, len: expr.count };
                }
                case 'Assignment': {
                    infcx.subCoerce('Assignment', expr.value, typeckExpr(expr.value), typeckExpr(expr.target));
                    return UNIT;
                }
                case 'Index': {
                    infcx.subCoerce('Index', expr.index, typeckExpr(expr.index), U64);
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
                    infcx.subCoerce('Binary', expr.lhs, lhsTy, expectedLhsTy);
                    infcx.subCoerce('Binary', expr.rhs, rhsTy, expectedRhsTy);
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

                    let astSig: AstFnSignature;
                    let selfTy: Ty | null;
                    switch (callee.type) {
                        case 'ExternFnDef':
                            astSig = callee.decl.sig;
                            selfTy = null;
                            break;
                        case 'FnDef':
                            astSig = callee.decl.sig;
                            selfTy = callee.decl.parent ? lowerTy(callee.decl.parent.selfTy) : null;
                            break;
                        case 'TraitFn':
                            astSig = callee.value.sig;
                            selfTy = callee.args[0];
                            break;
                        default:
                            bug(expr.span, 'callee must be a fn:' + callee.type);
                    }

                    const sig: InstantiatedFnSig = {
                        parameters: [],
                        ret: UNIT,
                        args: callee.args,
                    };


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
                        infcx.subCoerce('FnArgument', expr.args[i], typeckExpr(expr.args[i]), sig.parameters[i]);
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
                        default: {
                            const suggestions: Suggestion[] = [];
                            if (target.type === 'Pointer') {
                                suggestions.push({
                                    message: 'consider using dereference-property syntax to access a property on the pointee',
                                    replacements: [
                                        {
                                            span: shrinkToHi(expr.target.span),
                                            replacement: '*'
                                        },
                                    ]
                                })
                            }
                            err(expr.span, `property access requires record or tuple type, got ${ppTy(target)}`, undefined, suggestions);
                        }
                    }
                }
                case 'If': {
                    infcx.subCoerce('UseInCondition', expr.condition, typeckExpr(expr.condition), BOOL);
                    const thenTy = typeckExpr(expr.then);
                    if (expr.else) {
                        const elseTy = typeckExpr(expr.else);
                        infcx.subCoerce('JoinBlock', expr.then, thenTy, elseTy);
                        return thenTy;
                    } else {
                        infcx.subCoerce('JoinBlock', expr.then, thenTy, UNIT);
                        return UNIT;
                    }
                }
                case 'While':
                    infcx.subCoerce('UseInCondition', expr.condition, typeckExpr(expr.condition), BOOL);
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

                    infcx.subCoerce('Unary', expr.rhs, rhsTy, expectedTy);
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
                            infcx.subCoerce('JoinBlock', arm.body, bodyTy, armTy)
                        } else {
                            armTy = bodyTy;
                        }
                        infcx.subNoCoerce('Pattern', expr.span, patTy, scrutineeTy);
                    }
                    return armTy || NEVER;
                }
                case 'MethodCall': {
                    const targetTy = peelInfixDerefOpTy(expr.deref, typeckExpr(expr.target), expr.span);

                    // the pointe_e_ type is exclusively used for method lookup/selection
                    const derefTargetTy = targetTy.type === 'Pointer' ? targetTy.pointee : targetTy;

                    const methodLookupResult = itemInLateImpl(lateImpls, derefTargetTy, expr.path.ident);
                    if (methodLookupResult && methodLookupResult.type !== 'ImplItem') {
                        bug(expr.span, 'must be an impl item')
                    }
                    const hasReceiver = methodLookupResult?.value.decl.sig.parameters[0]?.type === 'Receiver';

                    if (!methodLookupResult || !hasReceiver) {
                        err(
                            expr.span,
                            `method '${expr.path.ident}' not found on ${ppTy(derefTargetTy)}`,
                            methodLookupResult && !hasReceiver ? 'this function exists on the type but it has no `self` receiver' : undefined
                        );
                    }
                    const { value: selectedMethod } = methodLookupResult;

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

                    infcx.subCoerce('MethodCallReceiver', expr.target, targetTy, sig.parameters[0]);
                    for (let i = 0; i < sig.parameters.length - 1; i++) {
                        // Relate our args with the instantiated signature.
                        infcx.subCoerce('FnArgument', expr.args[i], typeckExpr(expr.args[i]), sig.parameters[i + 1]);
                    }

                    return sig.ret;
                }
                default: assertUnreachable(expr);
            }
        }
        const t = inner(expr);
        if (t === undefined) {
            bug(expr.span, `type-checking expression returned invalid type`);
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

        const tryCoerce = (ct: Constraint, coercion: Coercion) => {
            let expr: Expr | undefined;
            if ((expr = infcx.constraintToExpr.get(ct))) {
                addCoercion(expr, coercion);
            } else {
                reportTypeMismatch(ct, ct.sup, ct.sub, `${ppTy(ct.sub)} can coerce to ${ppTy(ct.sup)}, but only in expressions`);
            }
        };

        function reportTypeMismatch(constraint: Constraint, expect: Ty, got: Ty, note?: string) {
            let message: string;
            switch (constraint.cause) {
                case 'Binary':
                    message = `left-hand side and right-hand side must be of the same type, got ${got.type} and ${expect.type}`;
                    break;
                default: message = `${ppTy(got)} is not assignable to ${ppTy(expect)}`;
            }

            error(sm, constraint.at, `type error: ${message}`, note);
            errors = true;
        }

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
                            sm, constraint.at,
                            `type error: overflow evaluating whether \`${pretty}\` holds`,
                            'consider adding type annotations to help inference'
                        );
                        errors = true;
                        continue;
                    }

                    function subFields(parent: Constraint, sub: Ty & RecordType, sup: Ty & RecordType) {
                        if (sub.fields.length !== sup.fields.length) {
                            // Fast fail: no point in comparing fields when they lengths don't match.
                            error(sm, constraint.at, `type error: subtype has ${sub.fields.length} fields but supertype requires ${sup.fields.length}`);
                        } else {
                            for (let i = 0; i < sub.fields.length; i++) {
                                const subf = sub.fields[i];
                                const supf = sup.fields[i];
                                if (subf[0] !== supf[0]) {
                                    error(sm, constraint.at, `type error: field '${subf[0]}' not present at index ${i} in ${ppTy(sup)}`);
                                } else {
                                    infcx.nestedSubNoCoerce(parent, subf[1], supf[1]);
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
                                    error(sm, constraint.at, `type error: tuple size mismatch (${sub.elements.length} != ${sup.elements.length})`);
                                } else {
                                    for (let i = 0; i < sub.elements.length; i++) {
                                        const subf = sub.elements[i];
                                        const supf = sup.elements[i];
                                        infcx.nestedSubNoCoerce(constraint, subf, supf);
                                    }
                                }
                            } else if (sub.type === 'Array' && sup.type === 'Array') {
                                if (sub.len !== sup.len) {
                                    error(sm, constraint.at, `type error: array length mismatch (${sub.len} != ${sup.len})`);
                                }
                                infcx.nestedSubNoCoerce(constraint, sub.elemTy, sup.elemTy);
                            } else if (sub.type === 'Slice' && sup.type === 'Slice') {
                                infcx.nestedSubNoCoerce(constraint, sub.elemTy, sup.elemTy);
                            } else if (sub.type === 'Pointer' && sup.type === 'Pointer') {
                                if (sub.pointee.type === 'Array' && sup.pointee.type === 'Slice' && sub.mtb === sup.mtb) {
                                    // Arrays can coerce to slices
                                    tryCoerce(constraint, { type: 'UnsizeArray', to: sup as Ty & { type: 'Pointer', pointee: { type: 'Slice' } } });

                                    infcx.nestedSubNoCoerce(constraint, sub.pointee.elemTy, sup.pointee.elemTy);
                                } else {
                                    infcx.nestedSubNoCoerce(constraint, sub.pointee, sup.pointee);
                                }
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
                                        error(sm, constraint.at, `error: '${sup.decl.name}' cannot be constructed here`);
                                    }
                                    subFields(constraint, sub, nsup);
                                }
                            } else if (sub.type === 'Alias' && sup.type === 'Alias') {
                                // TODO: check constructibleIn for both aliases
                                infcx.nestedSubCoerce(constraint, normalize(sub), normalize(sup));
                            } else if (sub.type === 'Alias') {
                                infcx.nestedSubCoerce(constraint, normalize(sub), normalize(sup));
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
                                    error(sm, constraint.at, `type error: ${msub} is not assignable to ${msup}`);
                                    errors = true;
                                } else {
                                    constrainVid(tyvid.id, other);
                                }
                            } else if (sub.type === 'TyVid' && sup.type === 'TyVid') {
                                // Both related types are type variables, can't progress; delay them
                                infcx.tyVars[sub.id].delayedConstraints.push(constraint);
                                infcx.tyVars[sup.id].delayedConstraints.push(constraint);
                            } else if (sub.type === 'never') {
                                // OK. Never is a subtype of all types.
                            } else if (sup.type === 'Pointer' && sub.type !== 'Pointer' && constraint.cause === 'MethodCallReceiver') {
                                // `T* == T` in a method call receiver: try to autoref
                                const coercedTy: Ty = { type: 'Pointer', pointee: sub, flags: sub.flags, mtb: sup.mtb };
                                addCoercion(infcx.expectConstraintExpr(constraint), { type: 'Autoref', to: coercedTy });
                                infcx.nestedSubNoCoerce(constraint, sup, coercedTy);
                            } else {
                                // Error case.

                                reportTypeMismatch(constraint, sup, sub);
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
                            console.log(`fallback @ ${ppSpan(sm.source, tyVarOriginSpan(tyvar.origin))}`);
                        }
                        constrainVid(i, fallback);
                        fallbackApplied = true;
                    }
                }
            }

            function reportTypeAnnotationsNeeded() {
                for (const tyvar of infcx.tyVars) {
                    if (!tyvar.constrainedTy && !tyVarHasFallback(tyvar)) {
                        error(sm, tyVarOriginSpan(tyvar.origin), 'type error: type annotations needed');
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
            case 'Array':
            case 'Slice': {
                const elemTy = instantiateTyVars(ty.elemTy);
                return { ...ty, flags: elemTy.flags, elemTy };
            }
            case 'TyVid':
                // the constrained type might itself reference other type variables, see tests/later-infer.chg for a full example
                return instantiateTyVars(infcx.tyVars[ty.id].constrainedTy!);
            case 'FnDef':
                return { type: ty.type, flags: withoutTyVid(ty.flags), args: ty.args.map(ty => instantiateTyVars(ty)), decl: ty.decl };
            case 'ExternFnDef':
                return { type: ty.type, flags: withoutTyVid(ty.flags), args: ty.args.map(ty => instantiateTyVars(ty)), decl: ty.decl };
            case 'TraitFn':
                return { type: ty.type, flags: withoutTyVid(ty.flags), args: ty.args.map(ty => instantiateTyVars(ty)), value: ty.value };
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

        let exprCoercions = coercions.get(expr);
        if (exprCoercions) {
            for (const coercion of exprCoercions) {
                coercion.to = instantiateTyVars(coercion.to);
            }
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

    return {
        infcx,
        loweredTys,
        exprTys: infcx.exprTys,
        instantiatedFnSigs,
        patTys,
        selectedMethods: selectedMethods,
        hadErrors: lub.hadErrors,
        impls: lateImpls,
        typeRelativeResolutions,
        coercions
    };
}
