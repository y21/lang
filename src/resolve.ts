import { EarlyImpls } from "./impls";
import { AstFnSignature, Pat, AstTy, Expr, ExternFnDecl, FnDecl, FnParameter, Generics, LetDecl, Path, Program, Stmt, TyAliasDecl, VariantId, Impl, PathSegment, Mod, ModItem, Trait } from "./parse";
import { assert, assertUnreachable, todo } from "./util";

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
    | Trait
    | { type: 'Root' };
export type BindingPat = { type: 'Binding' };
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

/////////////////////////
type CanonicalPath = string;
type Unresolved = { fromPath: CanonicalPath, path: string, node: UnresolvedNode };
type UnresolvedNode = { type: 'Expr', value: Expr } | { type: 'Ty', value: AstTy } | { type: 'Pat', value: Pat };
type Unresolveds = Array<Unresolved>;

export function computeResolutions(ast: Program): Resolutions {
    let currentPath: CanonicalPath = 'root';
    const lastPathSegment = (path: string) => path.slice(path.lastIndexOf('::') + 2);
    const lastCurrentPathSegment = () => lastPathSegment(currentPath);

    let nextScopeId = (() => {
        let scopes = 0;
        return () => scopes++;
    })();
    const typeNs = new Map<CanonicalPath, TypeResolution>();

    // Primitives
    const primitives: [string, PrimitiveTy][] = [
        ['bool', PrimitiveTy.Bool],
        ['i8', PrimitiveTy.I8],
        ['i16', PrimitiveTy.I16],
        ['i32', PrimitiveTy.I32],
        ['i64', PrimitiveTy.I64],
        ['u8', PrimitiveTy.U8],
        ['u16', PrimitiveTy.U16],
        ['u32', PrimitiveTy.U32],
        ['u64', PrimitiveTy.U64],
        ['str', PrimitiveTy.Str],
        ['never', PrimitiveTy.Never]
    ];
    for (const [path, pty] of primitives) {
        // Register them at the root scope, so during path resolution they act as absolute paths
        // TODO: what would happen if we had a library named `i32`? does this still work fine?
        typeNs.set(path, { type: 'Primitive', kind: pty });
    }

    const valueNs = new Map<CanonicalPath, ValueResolution>();
    const unresolveds = new Map<string, Unresolveds>();

    const addToUnresolveds = (ref: UnresolvedNode, path: Path<AstTy>) => {
        const lastSegment = path.segments[path.segments.length - 1].ident;
        let items: Unresolveds | undefined;
        const value: Unresolved = {
            fromPath: currentPath,
            path: path.segments.map(s => s.ident).join('::'),
            node: ref
        };

        if (items = unresolveds.get(lastSegment)) {
            items.push(value);
        } else {
            unresolveds.set(lastSegment, [value]);
        }
    }

    const valueResolutions: ValueResolutions = new Map();
    const patResolutions: PatResolutions = new Map();
    const tyResolutions: TypeResolutions = new Map();
    const impls: EarlyImpls = [];

    // The scope in which the enclosing type alias is defined in.
    // Normally, when we enter a type alias, we add a new scope, so that generics are only usable within the type alias itself and not outside.
    //
    //    type X<T> = /* T can be referred to only in here */;
    //
    //    /* T cannot be referred to here */
    //
    // This `tyAliasScope` is needed for us to be able to add `enum`s in the same scope where the type alias is defined in
    // and not restricted to just the type alias.
    let tyAliasScope: CanonicalPath | null = null;

    const breakableStack: Breakable[] = [];
    const breakableResolutions: Map<Expr, Breakable> = new Map();
    const findBreakable = () => {
        if (breakableStack.length === 0) {
            throw new Error('no breakable found');
        }
        return breakableStack[breakableStack.length - 1];
    }

    function withTyAliasScoped(name: string, fn: () => void) {
        assert(tyAliasScope !== null);
        const old = currentPath;
        currentPath = `${tyAliasScope}::${name}`;
        fn();
        currentPath = old;
    }

    function withNamedScope(name: string, fn: () => void) {
        const old = currentPath;
        currentPath += `::${name}`;
        fn();
        currentPath = old;
    }

    function withUnnamedScope(fn: () => void) {
        withNamedScope(`{${nextScopeId()}}`, fn);
    }

    function forEachResolvablePath<T>(prefix: string, suffix: string, cb: (_: string) => ('continue' | ['break', T])): T | undefined {
        assert(!suffix.startsWith('::'));

        let path = prefix;
        while (true) {
            const tmpPath = path.length === 0 ? suffix : path + '::' + suffix;

            const ret = cb(tmpPath);
            if (ret !== 'continue') {
                return ret[1];
            }

            let modRes: TypeResolution | undefined;
            if ((modRes = typeNs.get(tmpPath)) && modRes.type === 'Mod') {
                // We've reached a module boundary. Stop walking up and try to resolve it as an absolute path one last time
                todo('handle mod boundary');
            }

            if (path.length === 0) {
                break;
            }
            const lastSegmentIdx = path.lastIndexOf('::');
            if (lastSegmentIdx > 0) {
                path = path.slice(0, lastSegmentIdx);
            } else {
                path = '';
            }
        }
    }

    function tryEarlyResolveRelativePath<T>(input: Path<AstTy>, namespaceMap: Map<CanonicalPath, T>): T | undefined {
        return forEachResolvablePath(currentPath, input.segments.map(s => s.ident).join('::'), (path) => {
            let resolved: T | undefined;
            if (resolved = namespaceMap.get(path)) {
                return ['break', resolved];
            }
            return 'continue';
        });
    }

    function processLateResolved(
        path: CanonicalPath,
        fn: (_: Unresolved) => 'remove' | 'retain'
    ) {
        let maybeResolvables: Unresolveds | undefined;
        const keySegment = lastPathSegment(path);
        if (maybeResolvables = unresolveds.get(keySegment)) {
            // Go backwards to avoid index invalidation
            for (let i = maybeResolvables.length - 1; i >= 0; i--) {
                const res = maybeResolvables[i];

                if (fn(res) === 'remove') {
                    maybeResolvables.splice(i, 1);
                    if (maybeResolvables.length === 0) {
                        unresolveds.delete(keySegment);
                    }
                }
            }
        }
    }

    // Checks if `to` is a path that is reachable from `from`.
    function isPathReachableFrom(to: CanonicalPath, from_prefix: string, from_suffix: string): boolean {
        return forEachResolvablePath(from_prefix, from_suffix, (path) => {
            if (path === to) {
                return ['break', true];
            }
            return 'continue';
        }) === true;
    }

    // You should call this when visiting any kind of item (type or value) that can be "late resolved", i.e.
    // nodes that can be referenced before its definition.
    // This tries to find unresolveds that can be resolved with this definition
    function lateResolveforItemDefinition<K, V>(
        path: CanonicalPath,
        resMap: Map<K, V>,
        item: V
    ) {
        processLateResolved(path, (unres) => {
            if (isPathReachableFrom(path, unres.fromPath, unres.path)) {
                resMap.set(unres.node.value as K, item);
                return 'remove';
            }

            return 'retain';
        });
    }

    function visitPat(pat: Pat) {
        switch (pat.type) {
            case 'Number':
            case 'Range':
            case 'RangeFrom':
            case 'RangeTo':
            case 'String':
                break;
            case 'Path': {
                const ret = forEachResolvablePath(currentPath, pat.path.segments.map(s => s.ident).join('::'), (path) => {
                    const res = valueNs.get(path);
                    if (res?.type === 'Variant') {
                        return ['break', res as PatResolution];
                    }
                    return 'continue';
                });

                if (ret) {
                    patResolutions.set(pat, ret);
                } else {
                    addToUnresolveds({ type: 'Pat', value: pat }, pat.path);
                }

                break;
            }
            default: assertUnreachable(pat);
        }
    }
    function visitTy(ty: AstTy) {
        switch (ty.type) {
            case 'Path': {
                visitPath(ty.value, { type: 'Ty', value: ty }, typeNs, tyResolutions);
                break;
            }
            case 'Array': visitTy(ty.elemTy); break;
            case 'Pointer': visitTy(ty.pointeeTy); break;
            case 'Record':
                for (const [, v] of ty.fields) visitTy(v);
                break;
            case 'Alias':
                visitTy(ty.alias);
                break;
            case 'Infer': break;
            case 'Tuple': for (const elem of ty.elements) visitTy(elem); break;
            case 'Enum':
                if (tyAliasScope === null) {
                    throw new Error('enum types can currently only appear in type aliases');
                }
                withTyAliasScoped(ty.name, () => {
                    lateResolveforItemDefinition(currentPath, tyResolutions, ty);
                    typeNs.set(currentPath, ty);
                    for (let i = 0; i < ty.variants.length; i++) {
                        withNamedScope(ty.variants[i].name, () => {
                            const res: VariantResolution = { type: 'Variant', enum: ty, variant: i };
                            lateResolveforItemDefinition(currentPath, valueResolutions, res);
                            valueNs.set(currentPath, res);
                        });
                    }
                });
                break;
            default: assertUnreachable(ty);
        }
    }
    function visitExpr(expr: Expr) {
        switch (expr.type) {
            case 'Block':
                withUnnamedScope(() => {
                    for (const stmt of expr.stmts) visitStmt(stmt);
                    if (expr.tailExpr) visitExpr(expr.tailExpr)
                });
                break;
            case 'Return': visitExpr(expr.value); break;
            case 'ArrayLiteral': for (const e of expr.elements) visitExpr(e); break;
            case 'ArrayRepeat': visitExpr(expr.element); break;
            case 'FnCall': {
                for (const arg of expr.args) visitExpr(arg);
                visitExpr(expr.callee);
                break;
            }
            case 'Assignment': {
                visitExpr(expr.target);
                visitExpr(expr.value);
                break;
            }
            case 'Index': {
                visitExpr(expr.index);
                visitExpr(expr.target);
                break;
            }
            case 'Property': {
                visitExpr(expr.target);
                break;
            }
            case 'Number':
            case 'String':
            case 'Bool':
            case 'ByteCharacter':
                break;
            case 'Binary':
                visitExpr(expr.lhs);
                visitExpr(expr.rhs);
                break;
            case 'AddrOf':
                visitExpr(expr.pointee);
                break;
            case 'Deref':
                visitExpr(expr.pointee);
                break;
            case 'Record':
                for (const [, v] of expr.fields) {
                    visitExpr(v);
                }
                break;
            case 'If':
                visitExpr(expr.condition);
                visitExpr(expr.then);
                if (expr.else) {
                    visitExpr(expr.else);
                }
                break;
            case 'While':
                breakableStack.push({ type: 'While', target: expr });
                visitExpr(expr.condition);
                visitExpr(expr.body);
                breakableStack.pop();
                break;
            case 'Unary':
                visitExpr(expr.rhs);
                break;
            case 'Tuple':
                for (const element of expr.elements) {
                    visitExpr(element);
                }
                break;
            case 'Break':
            case 'Continue': {
                const target = findBreakable();
                breakableResolutions.set(expr, target);
                break;
            }
            case 'Match': {
                visitExpr(expr.scrutinee);
                for (const arm of expr.arms) {
                    withUnnamedScope(() => {
                        visitPat(arm.pat);
                        visitExpr(arm.body);
                    });
                }
                break;
            }
            case 'MethodCall': {
                for (const arg of expr.args) visitExpr(arg);
                for (const arg of expr.path.args) visitTy(arg.ty);
                visitExpr(expr.target);
                break;
            }
            case 'Path': {
                visitPath(expr.path, { type: 'Expr', value: expr }, valueNs, valueResolutions);
                break;
            }
            default: assertUnreachable(expr);
        }
    }

    function visitPath<
        K extends Expr | AstTy | Pat,
        U extends ({ type: 'Expr', value: K } | { type: 'Pat', value: K } | { type: 'Ty', value: K }) & UnresolvedNode,
        T
    >(path: Path<AstTy>, ref: U, ns: Map<string, T>, resMap: Map<K, T>) {
        let res: T | undefined;
        if (res = tryEarlyResolveRelativePath(path, ns)) {
            resMap.set(ref.value, res);
        } else {
            addToUnresolveds(ref, path);
        }

        for (const segment of path.segments) {
            for (const arg of segment.args) {
                visitTy(arg.ty);
            }
        }
    }

    // Visits a fn signature, split up from `visitFnDecl` since traits don't have a full declaration.
    // Requires that a scope has already been created at callsite.
    function visitFnSigInScope(sig: AstFnSignature, item: FnDecl | ExternFnDecl | Trait, parentGenericsCount: number) {
        assert(lastCurrentPathSegment() === sig.name);
        for (let i = 0; i < sig.generics.length; i++) {
            typeNs.set(`${currentPath}::${sig.generics[i]}`, { type: 'TyParam', id: i + parentGenericsCount, parentItem: item });
        }

        if (sig.ret) visitTy(sig.ret);
        for (const param of sig.parameters) {
            // Directly setting it is fine because this cannot possibly late-resolve anything
            valueNs.set(`${currentPath}::${param.type === 'Receiver' ? 'self' : param.name}`, { type: 'FnParam', param });

            if (param.type === 'Parameter') {
                visitTy(param.ty);
            }
        }
    }

    function visitFnDecl(decl: FnDecl, impl?: Impl) {
        withNamedScope(decl.sig.name, () => {
            lateResolveforItemDefinition(currentPath, valueResolutions, decl);
            valueNs.set(currentPath, decl);
            let parentGenericsCount: number;
            if (impl) {
                parentGenericsCount = impl.generics.length;
                if (impl.ofTrait) {
                    parentGenericsCount++;
                }
            } else {
                parentGenericsCount = 0;
            }
            visitFnSigInScope(decl.sig, decl, parentGenericsCount);
            visitExpr(decl.body);
        });
    }

    function visitStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': visitFnDecl(stmt); break;
            case 'Expr': visitExpr(stmt.value); break;
            case 'LetDecl': {
                if (stmt.init) visitExpr(stmt.init);
                if (stmt.ty) visitTy(stmt.ty);

                // This deserves an explanation:
                // for scoping & shadowing purposes we generally consider `let` as introducing a new scope.
                // I.e.
                //
                //   let x = 1;
                //   use(x);
                //   let x = 2;
                //   use(x);
                //
                // is treated as:
                //
                //   {
                //     let x = 1;
                //     use(x);
                //     {
                //       let x = 2;
                //       use(x);
                //     }
                //   }
                //
                // The why is that we may not know whether the let pattern is a path that introduces a binding or a path to
                // e.g. an enum variant (let Variant = ..).
                // So, we need to late-resolve it at the very end of name resolution:
                // If `x` in the above is still in unresolveds at the very end, it means that there is nothing that it refers to
                // and we need to do the usual late resolving.
                //
                // However, if they were both in the same scope, then they would
                // end up with the same canonical path `root::{0}::x`.
                // This means that we would resolve both `use(x)` to refer to the second `x`, which is wrong.
                // If we insert a scope, then every shadowed variable has its own canonical path.
                currentPath += `::{${nextScopeId()}}`;

                // Let decls are not late-resolved
                valueNs.set(`${currentPath}::${stmt.name}`, stmt);
                break;
            }
            case 'ExternFnDecl': {
                withNamedScope(stmt.sig.name, () => {
                    valueNs.set(currentPath, stmt);
                    visitFnSigInScope(stmt.sig, stmt, 0);
                });
                break;
            }
            case 'TyAlias': {
                tyAliasScope = currentPath;
                withNamedScope(stmt.name, () => {
                    if (stmt.alias.type !== 'Enum') {
                        // We only register a resolution to the type alias 
                        lateResolveforItemDefinition(currentPath, tyResolutions, stmt);
                        typeNs.set(currentPath, stmt);
                    }
                    for (let i = 0; i < stmt.generics.length; i++) {
                        typeNs.set(`${currentPath}::${stmt.generics[i]}`, { type: 'TyParam', id: i, parentItem: stmt });
                    }
                    // TODO: visit contructibleIn
                    visitTy(stmt.alias);
                });
                tyAliasScope = null;
                break;
            }
            case 'Mod': {
                assert!(stmt.modType === 'Inline');
                withNamedScope(stmt.name, () => {
                    for (const item of (stmt as Mod).items) {
                        visitStmt(item);
                    }
                });
                break;
            }
            case 'Impl': {
                let handle = () => {
                    typeNs.set(`${currentPath}::Self`, { type: 'Self', selfTy: stmt.selfTy });

                    for (let i = 0; i < stmt.generics.length; i++) {
                        typeNs.set(`${currentPath}::${stmt.generics[i]}`, { type: 'TyParam', id: i + (stmt.ofTrait ? 1 : 0), parentItem: stmt });
                    }

                    if (stmt.ofTrait) {
                        visitTy(stmt.ofTrait);
                    }

                    visitTy(stmt.selfTy);

                    impls.push([stmt.selfTy, stmt]);
                    for (const item of stmt.items) {
                        switch (item.type) {
                            case 'Fn': visitFnDecl(item.decl, stmt); break;
                            default: assertUnreachable(item.type);
                        }
                    }
                };

                if (stmt.selfTy.type === 'Path') {
                    withNamedScope(stmt.selfTy.value.segments.map(s => s.ident).join('::'), handle);
                } else {
                    // TODO: currently there isn't a way to really refer to items of non-path types.
                    // eventually we'd want to support e.g. <&Ty>::item(), which will likely require special handling.
                    // for now, we simply have them in a block scope, which is just a hack to have them essentially be unnameable
                    withUnnamedScope(handle);
                }
                break;
            }
            case 'Trait':
                withNamedScope(stmt.name, () => {
                    lateResolveforItemDefinition(currentPath, tyResolutions, stmt);
                    typeNs.set(currentPath, stmt);
                    typeNs.set(`${currentPath}::Self`, { type: 'TyParam', id: 0, parentItem: stmt });
                    // TODO: once traits can have generics, add generics here and pass the right parentGenericsCount

                    for (const item of stmt.items) {
                        withNamedScope(item.sig.name, () => {
                            valueNs.set(currentPath, { type: 'TraitFn', value: { parentTrait: stmt, sig: item.sig } });
                            visitFnSigInScope(item.sig, stmt, 1);
                        });
                    }
                });
                break;
            default: assertUnreachable(stmt);
        }
    }
    typeNs.set('root', { type: 'Root' });
    let entrypoint: FnDecl | null = null;
    for (const stmt of ast.stmts) {
        if (stmt.type === 'FnDecl' && stmt.sig.name === 'main') {
            entrypoint = stmt;
        }
        visitStmt(stmt);
    }
    if (!entrypoint) {
        throw new Error("'main' function not found");
    }

    for (const [, resolve] of unresolveds) {
        for (const { fromPath, node, path } of resolve) {
            const canonicalPath = `${fromPath}::${path}`;
            if (node.type === 'Pat') {
                const bindingPat: BindingPat = { type: 'Binding' };

                patResolutions.set(node.value, bindingPat);
                processLateResolved(canonicalPath, (unres) => {
                    if (unres.node.value === node.value) {
                        return 'remove';
                    }

                    if (isPathReachableFrom(canonicalPath, unres.fromPath, unres.path)) {
                        if (unres.node.type !== 'Expr') {
                            throw new Error('reference to binding pattern must be an expression node');
                        }

                        valueResolutions.set(unres.node.value, bindingPat);
                        return 'remove';
                    }

                    return 'retain';
                });
            }
        }
    }

    // Go through the unresolveds one last time to report errors.
    for (const [, unres] of unresolveds) {
        for (const { fromPath, path } of unres) {
            console.error(`${fromPath}::${path} cannot be resolved`);
        }
    }

    if (unresolveds.size != 0) {
        throw 'cannot continue due to name resolution errors';
    }

    return {
        breakableResolutions,
        entrypoint,
        impls,
        tyResolutions,
        valueResolutions,
        patResolutions
    }
}
