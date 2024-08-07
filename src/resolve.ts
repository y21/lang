import { addEarlyImpl, EarlyImpls, itemInEarlyImpls } from "./impls";
import { AstFnSignature, Pat, AstTy, Expr, ExternFnDecl, FnDecl, FnParameter, Generics, LetDecl, Path, Program, Stmt, TyAliasDecl, VariantId, Impl, PathSegment, Mod, ModItem, Trait } from "./parse";
import { assertUnreachable } from "./util";

type Scope<T> = Map<string, T>;

class ResNamespace<T> {
    scopes: (Map<string, T>)[] = [];
    add(name: string, value: T) {
        this.current()!.set(name, value);
    }
    find(name: string): T | null {
        for (let i = this.scopes.length - 1; i >= 0; i--) {
            const el = this.scopes[i].get(name);
            if (el) return el;
        }
        return null;
    }
    current(): Scope<T> | null {
        if (this.scopes.length === 0) {
            return null;
        } else {
            return this.scopes[this.scopes.length - 1];
        }
    }
    withScope(f: () => void) {
        this.scopes.push(new Map());
        f();
        this.scopes.pop();
    }
}

export enum PrimitiveTy {
    Never,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Bool,
    Str
}

export type IntrinsicName = 'bitcast' | 'ext' | 'trunc';
export type Intrinsic = ({ abi: 'intrinsic' }) & ExternFnDecl;

export function mkIntrinsic(name: IntrinsicName, generics: Generics, parameters: FnParameter[], ret: AstTy): Intrinsic {
    return {
        type: 'ExternFnDecl',
        abi: 'intrinsic',
        sig: {
            name: name,
            generics,
            parameters,
            ret,
        },
    }
}

function identPathTy(ident: string): AstTy {
    return { type: 'Path', value: { segments: [{ args: [], ident }] } };
}

const INTRINSICS: Intrinsic[] = [
    mkIntrinsic('bitcast', ['T', 'U'], [{ type: 'Parameter', name: 'v', ty: identPathTy('T') }], identPathTy('U')),
    mkIntrinsic('ext', ['T', 'U'], [{ type: 'Parameter', name: 'v', ty: identPathTy('T') }], identPathTy('U')),
    mkIntrinsic('trunc', ['T', 'U'], [{ type: 'Parameter', name: 'v', ty: identPathTy('T') }], identPathTy('U'))
];
export type TyParamResolution = {
    type: 'TyParam',
    id: number,
    parentItem: FnDecl | TyAliasDecl | ExternFnDecl | Impl | Trait,
};
export type TypeResolution = TyParamResolution
    | { type: 'Primitive', kind: PrimitiveTy }
    | TyAliasDecl
    | { type: 'Self', selfTy: AstTy }
    | ({ type: 'Enum' } & AstTy)
    | Mod
    | Trait;
export type BindingPat = { type: 'Binding', ident: string };
export type PatResolution = VariantResolution | BindingPat;
export type VariantResolution = { type: 'Variant', enum: { type: 'Enum' } & AstTy, variant: VariantId };
export type TypeResolutions = Map<AstTy, TypeResolution>;
/**
 * Partially resolved trait fn. This corresponds to "Default::default" paths with no self type specified.
 * These are incomplete because it relies on inference to fill that self type in.
 */
export type TraitFn = { parentTrait: Trait, sig: AstFnSignature };
export type ValueResolution = FnDecl | LetDecl | ExternFnDecl | ({ type: 'FnParam', param: FnParameter }) | VariantResolution | BindingPat | { type: 'TraitFn', value: TraitFn };
export type ValueResolutions = Map<Expr, ValueResolution>;
export type PatResolutions = Map<Pat, PatResolution>;
export type Resolutions = {
    tyResolutions: TypeResolutions,
    valueResolutions: ValueResolutions,
    patResolutions: PatResolutions,
    breakableResolutions: Map<Expr, Breakable>,
    impls: EarlyImpls,
    entrypoint: FnDecl
};

export type BreakableType = 'While';
export type Breakable = { type: BreakableType, target: { type: 'While' } & Expr };

export function computeResolutions(ast: Program): Resolutions {
    const tyRes = new ResNamespace<TypeResolution>();
    const valRes = new ResNamespace<ValueResolution>();
    const breakableStack: Breakable[] = [];
    const findBreakable = (): Breakable => {
        if (breakableStack.length === 0) {
            throw new Error('no breakable found');
        }
        return breakableStack[breakableStack.length - 1];
    }

    // The scope in which the enclosing type alias is defined in.
    // Normally, when we enter a type alias, we add a new scope, so that generics are only usable within the type alias itself and not outside.
    //
    //    type X<T> = /* T can be referred to only in here */;
    //
    //    /* T cannot be referred to here */
    //
    // This `tyAliasScope` is needed for us to be able to add `enum`s in the same scope where the type alias is defined in
    // and not restricted to just the type alias.
    let tyAliasScope: Scope<TypeResolution> | null = null;

    let entrypoint: FnDecl | null = null;

    const tyMap: Map<AstTy, TypeResolution> = new Map();
    const exprMap: Map<Expr, ValueResolution> = new Map();
    const patMap: Map<Pat, PatResolution> = new Map();
    const breakableMap: Map<Expr, Breakable> = new Map();
    const impls: EarlyImpls = [];

    const withAllScopes = (f: () => void) => {
        tyRes.withScope(() => {
            valRes.withScope(() => {
                f();
            });
        });
    };

    const registerRes = <K, T>(nskey: string, mapkey: K, ns: ResNamespace<T>, map: Map<K, T>) => {
        const res = ns.find(nskey);
        if (!res) throw `Cannot resolve ${nskey}`;
        map.set(mapkey, res);
    };

    function resolveTyPath(path: Path<AstTy>, ty: AstTy) {
        if (path.segments.length !== 1) {
            throw new Error('path must have one segment');
        }
        for (const arg of path.segments[0].args) resolveTy(arg.ty);

        const segment = path.segments[0];
        switch (segment.ident) {
            case 'never': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Never }); break;
            case 'i8': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I8 }); break;
            case 'i16': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I16 }); break;
            case 'i32': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I32 }); break;
            case 'i64': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I64 }); break;
            case 'u8': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.U8 }); break;
            case 'u16': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.U16 }); break;
            case 'u32': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.U32 }); break;
            case 'u64': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.U64 }); break;
            case 'bool': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Bool }); break;
            case 'str': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Str }); break;
            default: registerRes(segment.ident, ty, tyRes, tyMap); break;
        }
    }

    function resolveTy(ty: AstTy) {
        switch (ty.type) {
            case 'Path': {
                resolveTyPath(ty.value, ty);
                break;
            }
            case 'Array': resolveTy(ty.elemTy); break;
            case 'Pointer': resolveTy(ty.pointeeTy); break;
            case 'Record':
                for (const [, v] of ty.fields) resolveTy(v);
                break;
            case 'Alias':
                resolveTy(ty.alias);
                break;
            case 'Infer': break;
            case 'Tuple': for (const elem of ty.elements) resolveTy(elem); break;
            case 'Enum':
                if (tyAliasScope === null) {
                    throw new Error('enum types can currently only appear in type aliases');
                }
                tyAliasScope.set(ty.name, ty);
                break;
            default: assertUnreachable(ty);
        }
    }

    function resolveStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': resolveFnDecl(stmt); break;
            case 'ExternFnDecl': {
                valRes.add(stmt.sig.name, stmt);
                withAllScopes(() => {
                    resolveFnSig(stmt.sig, stmt);
                });
                break;
            }
            case 'Expr': resolveExpr(stmt.value); break;
            case 'LetDecl': {
                valRes.add(stmt.name, stmt);
                if (stmt.init) {
                    resolveExpr(stmt.init);
                }
                if (stmt.ty) {
                    resolveTy(stmt.ty);
                }
                break;
            }
            case 'TyAlias': {
                tyRes.add(stmt.name, stmt);
                tyAliasScope = tyRes.current()!;
                tyRes.withScope(() => {
                    for (let i = 0; i < stmt.generics.length; i++) {
                        tyRes.add(stmt.generics[i], { type: 'TyParam', id: i, parentItem: stmt });
                    }

                    resolveTy(stmt.alias);
                    for (const path of stmt.constructibleIn) {
                        if (path.segments.length !== 1) throw 'wrong segment length';
                        for (const args of path.segments[0].args) {
                            resolveTy(args.ty);
                        }
                    }
                });
                tyAliasScope = null;
                break;
            }
            case 'Impl': {
                tyRes.withScope(() => {
                    for (let i = 0; i < stmt.generics.length; i++) {
                        tyRes.add(stmt.generics[i], { type: 'TyParam', id: i + (stmt.ofTrait ? 1 : 0), parentItem: stmt });
                    }

                    if (stmt.ofTrait) {
                        resolveTy(stmt.ofTrait);
                    }

                    resolveTy(stmt.selfTy);
                    tyRes.add('Self', { type: 'Self', selfTy: stmt.selfTy });
                    addEarlyImpl(impls, stmt.selfTy, stmt);

                    for (const item of stmt.items) {
                        switch (item.type) {
                            case 'Fn': resolveFnDecl(item.decl, stmt); break;
                            default: assertUnreachable(item.type);
                        }
                    }
                });
                break;
            }
            case 'Trait': {
                tyRes.add(stmt.name, stmt);
                tyRes.withScope(() => {
                    tyRes.add('Self', { type: 'TyParam', id: 0, parentItem: stmt });
                    for (const item of stmt.items) {
                        // TODO: once traits can have generics, this needs to be updated to not be hardcoded to 1 anymore
                        resolveFnSig(item.sig, stmt, 1);
                    }
                });
                break;
            }
            case 'Mod': {
                tyRes.add(stmt.name, stmt);
                tyRes.withScope(() => {
                    for (const item of stmt.items) {
                        resolveStmt(item);
                    }
                });
                break;
            }
            default: assertUnreachable(stmt);
        }
    }

    function resolveEnumPath(path: Path<AstTy>): VariantResolution {
        const [def, variant] = path.segments.slice(-2);
        const defRes = tyRes.find(def.ident);
        if (!defRes || defRes.type !== 'Enum') {
            throw new Error(`first path segment must be an enum, got ${defRes?.type}`);
        }
        const variantIdx = defRes.variants.findIndex(v => v.name === variant.ident);
        return { type: 'Variant', enum: defRes, variant: variantIdx };
    }

    function resolvePat(pat: Pat) {
        switch (pat.type) {
            case 'Number': break;
            case 'Path':
                switch (pat.path.segments.length) {
                    case 1:
                        // new binding
                        const ident = pat.path.segments[0].ident;
                        const binding: BindingPat = { type: 'Binding', ident };
                        patMap.set(pat, binding);
                        valRes.add(ident, binding);
                        break;
                    case 2:
                        patMap.set(pat, resolveEnumPath(pat.path));
                        break;
                    default: throw new Error('only 1-2 path segments are currently supported');
                }
                break;
        }
    }

    function resolveExpr(expr: Expr) {
        switch (expr.type) {
            case 'Path':
                switch (expr.path.segments.length) {
                    case 1: {
                        const [segment] = expr.path.segments;
                        registerRes(segment.ident, expr, valRes, exprMap);
                        if (segment.args) {
                            for (const arg of segment.args) resolveTy(arg.ty);
                        }
                        break;
                    }
                    default: {
                        const segments = expr.path.segments.values();
                        let segment: IteratorResult<PathSegment<AstTy>>;

                        let currentTy: null | TypeResolution = null;

                        while (!(segment = segments.next()).done) {
                            for (const arg of segment.value.args) resolveTy(arg.ty);

                            switch (currentTy?.type) {
                                case 'TyAlias': {
                                    const selectedItem = itemInEarlyImpls(impls, tyMap, currentTy, segment.value.ident);

                                    if (!selectedItem || selectedItem.type !== 'Fn') {
                                        throw new Error('unimplemented segment');
                                    }

                                    exprMap.set(expr, selectedItem.decl);
                                    break;
                                }
                                case 'Trait': {
                                    const selectedItem = currentTy.items.find(item => item.sig.name === segment.value.ident);

                                    if (!selectedItem || selectedItem.type !== 'Fn') {
                                        throw new Error('unimplemented segment');
                                    }

                                    exprMap.set(expr, { type: 'TraitFn', value: { parentTrait: currentTy, sig: selectedItem.sig } });
                                    break;
                                }
                                case 'Enum': {
                                    const variant = currentTy.variants.findIndex(variant => variant.name === segment.value.ident);
                                    if (variant === -1) {
                                        throw new Error(`variant '${segment.value.ident}' not found on enum ${currentTy.name}`);
                                    }
                                    exprMap.set(expr, resolveEnumPath(expr.path));
                                    break;
                                }
                                case 'Mod': {
                                    const stmt: ModItem | undefined = currentTy.items.find((item: ModItem) => {
                                        switch (item.type) {
                                            case 'FnDecl':
                                                return item.sig.name === segment.value.ident;
                                            default:
                                                return item.name === segment.value.ident;
                                        }
                                    });
                                    if (!stmt) {
                                        throw new Error(`'${segment.value.ident}' does not exist in module ${currentTy.name}`);
                                    }
                                    if (stmt.type === 'FnDecl') {
                                        exprMap.set(expr, stmt);
                                    } else {
                                        currentTy = stmt;
                                    }
                                    break;
                                }
                                case undefined:
                                    currentTy = tyRes.find(segment.value.ident);
                                    break;
                                default: throw new Error(`unimplemented path on type ${currentTy?.type}`);
                            }
                        }
                    }
                }
                break;
            case 'Block':
                for (const stmt of expr.stmts) resolveStmt(stmt);
                if (expr.tailExpr) resolveExpr(expr.tailExpr)
                break;
            case 'Return': resolveExpr(expr.value); break;
            case 'ArrayLiteral': for (const e of expr.elements) resolveExpr(e); break;
            case 'ArrayRepeat': resolveExpr(expr.element); break;
            case 'FnCall': {
                for (const arg of expr.args) resolveExpr(arg);
                resolveExpr(expr.callee);
                break;
            }
            case 'Assignment': {
                resolveExpr(expr.target);
                resolveExpr(expr.value);
                break;
            }
            case 'Index': {
                resolveExpr(expr.index);
                resolveExpr(expr.target);
                break;
            }
            case 'Property': {
                resolveExpr(expr.target);
                break;
            }
            case 'Number':
            case 'String':
            case 'Bool':
            case 'ByteCharacter':
                break;
            case 'Binary':
                resolveExpr(expr.lhs);
                resolveExpr(expr.rhs);
                break;
            case 'AddrOf':
                resolveExpr(expr.pointee);
                break;
            case 'Deref':
                resolveExpr(expr.pointee);
                break;
            case 'Record':
                for (const [, v] of expr.fields) {
                    resolveExpr(v);
                }
                break;
            case 'If':
                resolveExpr(expr.condition);
                resolveExpr(expr.then);
                if (expr.else) {
                    resolveExpr(expr.else);
                }
                break;
            case 'While':
                resolveExpr(expr.condition);
                breakableStack.push({ type: 'While', target: expr });
                resolveExpr(expr.body);
                break;
            case 'Unary':
                resolveExpr(expr.rhs);
                break;
            case 'Tuple':
                for (const element of expr.elements) {
                    resolveExpr(element);
                }
                break;
            case 'Break':
            case 'Continue': {
                const target = findBreakable();
                breakableMap.set(expr, target);
                break;
            }
            case 'Match': {
                resolveExpr(expr.scrutinee);
                for (const arm of expr.arms) {
                    valRes.withScope(() => {
                        resolvePat(arm.pat);
                        resolveExpr(arm.body);
                    });
                }
                break;
            }
            case 'MethodCall': {
                for (const arg of expr.args) resolveExpr(arg);
                for (const arg of expr.path.args) resolveTy(arg.ty);
                resolveExpr(expr.target);
                break;
            }
            default: assertUnreachable(expr);
        }
    }

    function resolveFnSig(sig: AstFnSignature, item: FnDecl | ExternFnDecl | Trait, parentGenericCount?: number) {
        for (let i = 0; i < sig.generics.length; i++) {
            tyRes.add(sig.generics[i], { type: 'TyParam', id: i + (parentGenericCount || 0), parentItem: item });
        }

        for (const param of sig.parameters) {
            valRes.add(param.type === 'Receiver' ? 'self' : param.name, { type: 'FnParam', param });
            if (param.type === 'Parameter') {
                resolveTy(param.ty);
            }
        }

        if (sig.ret) {
            resolveTy(sig.ret);
        }
    }

    function resolveFnDecl(decl: FnDecl, impl?: Impl) {
        if (INTRINSICS.some(ins => ins.sig.name === decl.sig.name)) {
            throw new Error(`function cannot have name '${decl.sig.name}' because it is the name of an intrinsic`);
        }
        valRes.add(decl.sig.name, decl);
        withAllScopes(() => {
            const parentGenericsCount = impl ?
                impl.generics.length + (impl.ofTrait ? 1 : 0)
                : 0;
            resolveFnSig(decl.sig, decl, parentGenericsCount);
            resolveExpr(decl.body);
        });
    }

    valRes.withScope(() => {
        for (const intrinsic of INTRINSICS) {
            resolveStmt({ type: 'ExternFnDecl', abi: 'intrinsic', span: [0, 0], sig: intrinsic.sig });
        }

        tyRes.withScope(() => {
            for (const stmt of ast.stmts) {
                if (stmt.type === 'FnDecl' && stmt.sig.name === 'main') {
                    entrypoint = stmt;
                }
                resolveStmt(stmt);
            }
        });
    });

    if (!entrypoint) {
        throw "'main' function not found";
    }

    return { tyResolutions: tyMap, valueResolutions: exprMap, breakableResolutions: breakableMap, patResolutions: patMap, entrypoint, impls };
}
