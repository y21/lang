import fs from 'fs';
import cProcess from 'child_process';

function assertUnreachable(v: never): never {
    throw 'impossible';
}

function todo(what?: string): never {
    throw new Error('Todo: ' + what);
}

type Span = [number, number];

function joinSpan(a: Span, b: Span): Span {
    return [a[0], b[1]];
}

enum TokenType {
    Function,
    Let,
    Return,
    Ident,
    LParen,
    RParen,
    LSquare,
    RSquare,
    LBrace,
    RBrace,
    Colon,
    Assign,
    Semi,
    Comma,
    Number,
    String,
    Plus,
    Minus,
    Star,
    Slash,
    Dot,
    Lt,
    Gt,
}
interface Token {
    ty: TokenType;
    span: Span;
}

function isAlphaStart(c: string) {
    return (c.charCodeAt(0) >= 'a'.charCodeAt(0) && c.charCodeAt(0) <= 'z'.charCodeAt(0))
        || (c.charCodeAt(0) >= 'A'.charCodeAt(0) && c.charCodeAt(0) <= 'Z'.charCodeAt(0));
}

function isDigit(c: string) {
    return (c.charCodeAt(0) >= '0'.charCodeAt(0) && c.charCodeAt(0) <= '9'.charCodeAt(0));
}

function isAlpha(c: string) {
    return isAlphaStart(c) || isDigit(c);
}

function tokenize(src: string): Token[] {
    const tokens: Token[] = [];
    for (let i = 0; i < src.length; i++) {
        let start = i;

        switch (src[i]) {
            case ' ':
            case '\n':
                break;
            case '(': tokens.push({ span: [start, i + 1], ty: TokenType.LParen }); break;
            case ')': tokens.push({ span: [start, i + 1], ty: TokenType.RParen }); break;
            case '[': tokens.push({ span: [start, i + 1], ty: TokenType.LSquare }); break;
            case ']': tokens.push({ span: [start, i + 1], ty: TokenType.RSquare }); break;
            case '{': tokens.push({ span: [start, i + 1], ty: TokenType.LBrace }); break;
            case '}': tokens.push({ span: [start, i + 1], ty: TokenType.RBrace }); break;
            case ':': tokens.push({ span: [start, i + 1], ty: TokenType.Colon }); break;
            case '=': tokens.push({ span: [start, i + 1], ty: TokenType.Assign }); break;
            case ';': tokens.push({ span: [start, i + 1], ty: TokenType.Semi }); break;
            case '.': tokens.push({ span: [start, i + 1], ty: TokenType.Dot }); break;
            case '<': tokens.push({ span: [start, i + 1], ty: TokenType.Lt }); break;
            case '>': tokens.push({ span: [start, i + 1], ty: TokenType.Gt }); break;
            case ',': tokens.push({ span: [start, i + 1], ty: TokenType.Comma }); break;
            case '+': tokens.push({ span: [start, i + 1], ty: TokenType.Plus }); break;
            case '-': tokens.push({ span: [start, i + 1], ty: TokenType.Minus }); break;
            case '*': tokens.push({ span: [start, i + 1], ty: TokenType.Star }); break;
            case '/': {
                if (src[i + 1] === '/') {
                    while (i < src.length && src[i] !== '\n') i++;
                } else {
                    i++;
                    tokens.push({ span: [start, i], ty: TokenType.Slash }); break;
                }
                break;
            }
            case '"':
                i++;
                while (src[i] !== '"') i++;
                tokens.push({ span: [start, i + 1], ty: TokenType.String });
                break;
            default:
                if (isAlphaStart(src[i])) {
                    let ident = '';
                    while (isAlpha(src[i])) ident += src[i++];
                    let span: Span = [start, i];
                    i--;
                    let ty;
                    switch (ident) {
                        case 'function': ty = TokenType.Function; break;
                        case 'let': ty = TokenType.Let; break;
                        case 'return': ty = TokenType.Return; break;
                        default: ty = TokenType.Ident; break;
                    }
                    tokens.push({ span, ty });
                } else if (isDigit(src[i])) {
                    while (isDigit(src[i])) i++;
                    let span: Span = [start, i];
                    i--;
                    tokens.push({ span, ty: TokenType.Number });
                } else {
                    throw 'Unknown token: ' + src[i];
                }
        }
    }
    return tokens;
}

function assert(cond: boolean, msg?: string) {
    if (!cond) {
        if (msg) {
            throw new Error(`Assertion failed: ${msg}`);
        } else {
            throw new Error('Assertion failed');
        }
    }
}
type Expr = { span: Span } & (
    | { type: "Block"; stmts: Stmt[] }
    | { type: "Literal"; ident: string }
    | { type: "FnCall"; args: Expr[]; callee: Expr }
    | { type: "Index"; target: Expr; index: Expr; }
    | { type: "ArrayLiteral"; elements: Expr[] }
    | { type: "Number"; value: number }
    | { type: "String"; value: string }
    | { type: "Assignment"; target: Expr; value: Expr }
    | { type: "Property"; target: Expr; property: string }
    | { type: "Return"; value: Expr }
    | { type: "Binary"; op: TokenType; lhs: Expr; rhs: Expr }
);


type LetDecl = { type: 'LetDecl', name: string, init: Expr };

type FnDecl = {
    type: 'FnDecl', name: string, generics: string[],
    ret: AstTy, body: Expr
};

type Stmt = { span: Span } & ({ type: 'Expr', value: Expr } | LetDecl | FnDecl);
type AstTy = { type: 'Literal', ident: string } | { type: 'ArrayLiteral', elemTy: AstTy };
type Program = { stmts: Stmt[] };
type LeftToRight = 'ltr';
type RightToLeft = 'rtl';
type Associativity = LeftToRight | RightToLeft;

const BINARY_INFIX_PRECEDENCE: { [index: string]: number | undefined } = {
    // Fn calls `x()`
    [TokenType.LParen]: 17,
    // Indexing `x[y]`
    [TokenType.LSquare]: 17,
    [TokenType.Dot]: 17,
    // Multiplicative
    [TokenType.Star]: 12,
    [TokenType.Slash]: 12,
    // Additive
    [TokenType.Plus]: 11,
    [TokenType.Minus]: 11,
    // Assignment x = y
    [TokenType.Assign]: 2
};
const ASSOC: { [index: string]: Associativity | undefined } = {
    [TokenType.LParen]: 'ltr',
    [TokenType.Dot]: 'ltr',
    [TokenType.LSquare]: 'ltr',
    [TokenType.Assign]: 'rtl',
    [TokenType.Plus]: 'ltr',
    [TokenType.Minus]: 'ltr',
    [TokenType.Star]: 'ltr',
    [TokenType.Slash]: 'ltr',
};

function parse(src: string): Program {
    const tokens = tokenize(src);
    const stmts: Stmt[] = [];
    let i = 0;

    function snip(span: Span) {
        return src.substring(span[0], span[1]);
    }

    function expectIdent() {
        const ident = tokens[i++];
        if (ident.ty !== TokenType.Ident) throw 'Expected ident, got ' + TokenType[ident.ty];
        return snip(ident.span);
    }

    function eatToken(ty: TokenType, error = true) {
        const tok = tokens[i];
        if (tok?.ty === ty) {
            i++;
            return true;
        } else if (error) {
            throw new Error(`Expected ${TokenType[ty]}, got ${TokenType[tok.ty]}`);
        } else {
            return false;
        }
    }

    function parseTy(): AstTy {
        let ty: AstTy;
        switch (tokens[i].ty) {
            case TokenType.Ident:
                ty = { type: 'Literal', ident: snip(tokens[i].span) };
                i++;
                break;
            default: throw 'Unknown token for ty: ' + TokenType[tokens[i].ty];
        }

        while (i < tokens.length) {
            if (eatToken(TokenType.LSquare, false)) {
                eatToken(TokenType.RSquare);
                ty = { type: 'ArrayLiteral', elemTy: ty };
            } else {
                break;
            }
        }
        return ty;
    }

    function parseBottomExpr(): Expr {
        let expr: Expr;
        switch (tokens[i].ty) {
            case TokenType.Number: expr = { type: 'Number', span: tokens[i].span, value: +snip(tokens[i].span) }; break;
            case TokenType.String: expr = { type: 'String', span: tokens[i].span, value: snip(tokens[i].span) }; break;
            case TokenType.Ident: expr = { type: 'Literal', span: tokens[i].span, ident: snip(tokens[i].span) }; break;
            default: throw `Invalid token ${TokenType[tokens[i].ty]} at ${tokens[i].span} (expected bottom expression)`;
        }
        i++;
        return expr;
    }

    function parseExpr(minPrecedence: number): Expr {
        // Unary expressions.
        switch (tokens[i].ty) {
            case TokenType.Return: {
                let returnKwSpan = tokens[i].span;
                i++;
                const value = parseRootExpr();
                return { type: 'Return', span: joinSpan(returnKwSpan, value.span), value };
            }
            case TokenType.LBrace: {
                const lbraceSpan = tokens[i].span;
                i++;
                const stmts = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    stmts.push(parseStmt());
                }
                return { type: 'Block', span: joinSpan(lbraceSpan, tokens[i - 1].span), stmts };
            }
        }

        let expr = parseBottomExpr();

        while (i < tokens.length) {
            const op = tokens[i];
            const prec = BINARY_INFIX_PRECEDENCE[op.ty];
            const assoc = ASSOC[op.ty];
            if (prec === undefined || assoc === undefined) {
                return expr;
            }

            // Handle precedence and associativity
            if (minPrecedence >= prec && !(minPrecedence === prec && assoc === 'rtl')) break;

            i++;
            switch (op.ty) {
                case TokenType.Assign: {
                    const rhs = parseExpr(prec);
                    expr = { type: 'Assignment', target: expr, value: rhs, span: joinSpan(expr.span, rhs.span) };
                    break;
                }
                case TokenType.LParen: {
                    let args = [];
                    while (i < tokens.length && tokens[i].ty !== TokenType.RParen) {
                        eatToken(TokenType.Comma, false);
                        args.push(parseRootExpr());
                    }
                    eatToken(TokenType.RParen, true);
                    expr = { type: 'FnCall', callee: expr, args, span: [expr.span[0], tokens[i - 1].span[1]] };
                    break;
                }
                case TokenType.Dot: {
                    let ident = expectIdent();
                    expr = { type: 'Property', target: expr, property: ident, span: [expr.span[0], tokens[i - 1].span[1]] }
                    break;
                }
                case TokenType.Plus:
                case TokenType.Minus:
                case TokenType.Star:
                case TokenType.Slash: {
                    const rhs = parseExpr(prec);
                    expr = { type: 'Binary', op: op.ty, lhs: expr, rhs, span: joinSpan(expr.span, rhs.span) };
                    break;
                }
                default: throw `Unhandled binary/infix operator ${op}`
            }
        }

        return expr;
    }

    let parseRootExpr = () => parseExpr(-1);

    function parseStmt(): Stmt {
        switch (tokens[i].ty) {
            case TokenType.Function: {
                i++;
                const name = expectIdent();
                const generics = [];

                // generics
                if (eatToken(TokenType.Lt, false)) {
                    const name = expectIdent();
                    generics.push(name);
                    eatToken(TokenType.Gt);
                }

                eatToken(TokenType.LParen);
                // TODO: params
                eatToken(TokenType.RParen);

                eatToken(TokenType.Colon);

                const ret = parseTy();
                const body = parseRootExpr();

                return {
                    type: 'FnDecl',
                    span: body.span, // TODO: wrong span
                    name,
                    generics,
                    ret,
                    body
                };
            }
            case TokenType.Let: {
                let letSpan = tokens[i].span;
                i++;
                const name = expectIdent();
                eatToken(TokenType.Assign);
                const init = parseRootExpr();
                eatToken(TokenType.Semi);
                return { span: joinSpan(letSpan, tokens[i - 1].span), type: 'LetDecl', name, init };
            }
            default: {
                const value = parseRootExpr();
                eatToken(TokenType.Semi);
                return { span: [value.span[0], tokens[i - 1].span[1]], type: 'Expr', value };
            }
        }
    }

    while (i < tokens.length) {
        stmts.push(parseStmt());
    }

    return {
        stmts
    };
}


class ResNamespace<T> {
    scopes: (Map<string, T>)[] = [];
    add(name: string, value: T) {
        this.scopes[this.scopes.length - 1].set(name, value);
    }
    find(name: string): T | null {
        for (let i = this.scopes.length - 1; i >= 0; i--) {
            const el = this.scopes[i].get(name);
            if (el) return el;
        }
        return null;
    }
    withScope(f: () => void) {
        this.scopes.push(new Map());
        f();
        this.scopes.pop();
    }
}

enum PrimitiveTy {
    Void,
    Never,
    I32,
}
type TyParamResolution = { type: 'TyParam', id: number, parentFn: FnDecl };
type TypeResolution = TyParamResolution | { type: 'Primitive', kind: PrimitiveTy };
type TypeResolutions = Map<AstTy, TypeResolution>;
type ValueResolution = FnDecl | LetDecl;
type ValueResolutions = Map<Expr, ValueResolution>;
type Resolutions = { tyResolutions: TypeResolutions, valueResolutions: ValueResolutions, entrypoint: FnDecl };

function computeResolutions(ast: Program): Resolutions {
    const tyRes = new ResNamespace<TypeResolution>();
    const valRes = new ResNamespace<ValueResolution>();
    let entrypoint: FnDecl | null = null;

    const tyMap: Map<AstTy, TypeResolution> = new Map();
    const identMap: Map<Expr, ValueResolution> = new Map();

    const registerRes = <K, T>(nskey: string, mapkey: K, ns: ResNamespace<T>, map: Map<K, T>) => {
        const res = ns.find(nskey);
        if (!res) throw `Cannot resolve ${nskey}`;
        map.set(mapkey, res);
    };

    function resolveTy(ty: AstTy) {
        switch (ty.type) {
            case 'Literal': {
                switch (ty.ident) {
                    case 'void': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Void }); break;
                    case 'never': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Never }); break;
                    case 'i32': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I32 }); break;
                    default: registerRes(ty.ident, ty, tyRes, tyMap); break;
                }
                break;
            }
            case 'ArrayLiteral': resolveTy(ty.elemTy); break;
            default: assertUnreachable(ty);
        }
    }

    function resolveStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': resolveFnDecl(stmt); break;
            case 'Expr': resolveExpr(stmt.value); break;
            case 'LetDecl': {
                valRes.add(stmt.name, stmt);
                resolveExpr(stmt.init);
                break;
            }
            default: assertUnreachable(stmt);
        }
    }

    function resolveExpr(expr: Expr) {
        switch (expr.type) {
            case 'Literal': registerRes(expr.ident, expr, valRes, identMap); break;
            case 'Block': for (const stmt of expr.stmts) resolveStmt(stmt); break;
            case 'Return': resolveExpr(expr.value); break;
            case 'ArrayLiteral': for (const e of expr.elements) resolveExpr(e); break;
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
                break;
            case 'Binary':
                resolveExpr(expr.lhs);
                resolveExpr(expr.rhs);
                break;
            default: assertUnreachable(expr);
        }
    }

    function resolveFnDecl(decl: FnDecl) {
        valRes.add(decl.name, decl);
        tyRes.withScope(() => {
            for (let i = 0; i < decl.generics.length; i++) {
                tyRes.add(decl.generics[i], { type: 'TyParam', id: i, parentFn: decl });
            }

            resolveTy(decl.ret);
            resolveExpr(decl.body);
        });
    }

    valRes.withScope(() => {
        for (const stmt of ast.stmts) {
            if (stmt.type === 'FnDecl' && stmt.name === 'main') {
                entrypoint = stmt;
            }
            resolveStmt(stmt);
        }
    });

    if (!entrypoint) {
        throw "'main' function not found";
    }

    return { tyResolutions: tyMap, valueResolutions: identMap, entrypoint };
}

type Ty = { type: 'TyVid', id: number }
    | { type: 'void' }
    | { type: 'never' }
    | { type: 'i32' }
    | { type: 'string' }
    | { type: 'ArrayLiteral', elemTy: Ty }
    | { type: 'TyParam', id: number, parentFn: FnDecl }
    | { type: 'FnDef', decl: FnDecl };

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'UseInArithmeticOperation' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index';
type Constraint = { cause: ConstraintCause, at: Span } & ConstraintType;

type FnLocalState = {
    expectedReturnTy: Ty;
    returnFound: boolean;
    localTypes: Map<LetDecl, Ty>;
};

type TypeckResults = {
    infcx: Infcx,
    loweredTys: Map<AstTy, Ty>,
    exprTys: Map<Expr, Ty>,
    hadErrors: boolean
};

type InfTyVar = { constrainedTy: Ty | null, origin: TyVarOrigin };
type TyVarOrigin = { type: 'Expr', expr: Expr };
type LUBResult = { hadErrors: boolean };

class Infcx {
    tyVars: Array<InfTyVar> = [];
    constraints: Constraint[] = [];
    fnStack: FnLocalState[] = [];

    constructor() { }

    sub(cause: ConstraintCause, at: Span, sub: Ty, sup: Ty) {
        this.constraints.push({ type: 'SubtypeOf', at, cause, sub, sup });
    }

    mkTyVar(origin: TyVarOrigin): Ty {
        const id = this.tyVars.length;
        this.tyVars.push({ constrainedTy: null, origin });
        return { type: 'TyVid', id };
    }

    withFn(expect: Ty, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect, returnFound: false, localTypes: new Map() });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (expectedReturnTy.type !== 'void' && !returnFound) {
            throw `Expected ${expect.type}, got void`;
        }
    }

    registerLocal(decl: LetDecl, ty: Ty) {
        this.fnStack[this.fnStack.length - 1].localTypes.set(decl, ty);
    }

    localTy(decl: LetDecl): Ty | undefined {
        return this.fnStack[this.fnStack.length - 1].localTypes.get(decl);
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


function error(src: string, span: Span, message: string) {
    let lineStart = src.lastIndexOf('\n', span[0]);
    let lineEnd = src.indexOf('\n', span[1]);
    const col = span[0] - lineStart;
    const snipLen = span[1] - span[0];
    const line = src.substring(lineStart, lineEnd);

    console.log('');
    console.log(line);
    console.log(' '.repeat(col - 1) + '\x1b[1;31m' +
        '^'.repeat(snipLen) +
        `  ${message}`);
    console.log('\x1b[0m');
}

function typeck(src: string, ast: Program, res: Resolutions): TypeckResults {
    const infcx = new Infcx();
    const loweredTys = new Map<AstTy, Ty>();
    const exprTys = new Map<Expr, Ty>();

    function lowerTy(ty: AstTy): Ty {
        let lowered = loweredTys.get(ty);
        if (lowered) return lowered;

        function lowerInner(ty: AstTy): Ty {
            switch (ty.type) {
                case 'Literal': {
                    const tyres = res.tyResolutions.get(ty)!;
                    switch (tyres.type) {
                        case 'TyParam': return { type: 'TyParam', id: tyres.id, parentFn: tyres.parentFn };
                        case 'Primitive': switch (tyres.kind) {
                            case PrimitiveTy.Void: return { type: 'void' };
                            case PrimitiveTy.Never: return { type: 'never' };
                            case PrimitiveTy.I32: return { type: 'i32' };
                            default: assertUnreachable(tyres.kind)
                        }
                        default: assertUnreachable(tyres)
                    }
                }
                case 'ArrayLiteral': return { type: 'ArrayLiteral', elemTy: lowerTy(ty.elemTy) };
            }
        }
        lowered = lowerInner(ty);
        loweredTys.set(ty, lowered);
        return lowered;
    }

    function typeckFn(decl: FnDecl) {
        const ret = lowerTy(decl.ret);
        infcx.withFn(ret, () => { typeckExpr(decl.body); });
    }

    function typeckStmt(stmt: Stmt) {
        switch (stmt.type) {
            case 'FnDecl': typeckFn(stmt); break;
            case 'Expr': typeckExpr(stmt.value); break;
            case 'LetDecl': {
                const rety = typeckExpr(stmt.init);
                infcx.registerLocal(stmt, rety);
                break;
            }
            default: assertUnreachable(stmt);
        }
    }

    function typeckExpr(expr: Expr): Ty {
        function inner(expr: Expr): Ty {
            switch (expr.type) {
                case 'Block': for (const stmt of expr.stmts) typeckStmt(stmt); return { type: 'void' };
                case 'Literal': {
                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        case 'FnDecl': return { type: 'FnDef', decl: litres };
                        case 'LetDecl': return infcx.localTy(litres)!;
                        default: assertUnreachable(litres);
                    }
                }
                case 'Return': {
                    const ret = typeckExpr(expr.value);
                    infcx.registerReturn(expr.span, ret);
                    return { type: 'never' };
                }
                case 'ArrayLiteral': {
                    let elemTy: Ty;
                    if (expr.elements.length === 0) {
                        elemTy = infcx.mkTyVar({ type: "Expr", expr });
                    } else {
                        elemTy = typeckExpr(expr.elements[0]);
                        for (let i = 1; i < expr.elements.length; i++) infcx.sub('ArrayLiteral', expr.elements[i].span, typeckExpr(expr.elements[i]), elemTy);
                    }
                    return { type: 'ArrayLiteral', elemTy };
                }
                case 'Assignment': {
                    infcx.sub('Assignment', expr.span, typeckExpr(expr.value), typeckExpr(expr.target));
                    return { type: 'void' };
                }
                case 'Index': {
                    infcx.sub('Index', expr.span, typeckExpr(expr.index), { type: 'i32' });
                    const target = typeckExpr(expr.target);
                    if (target.type === 'ArrayLiteral') {
                        return target.elemTy;
                    } else {
                        // TODO: constraint for tyvar
                        throw `Cannot index into ${target.type}`
                    }
                }
                // TODO: typescript's "as const" can create a literal type?
                case 'Number': return { type: 'i32' };
                case 'String': return { type: 'string' };
                case 'Binary': {
                    infcx.sub('UseInArithmeticOperation', expr.lhs.span, typeckExpr(expr.lhs), { type: 'i32' });
                    infcx.sub('UseInArithmeticOperation', expr.rhs.span, typeckExpr(expr.rhs), { type: 'i32' });
                    return { type: 'i32' };
                }
                default: todo(expr.type);
            }
        }
        const t = inner(expr);
        // Type variables are later inserted when an upper type is computed based on the constraints.
        if (t.type !== 'TyVid') {
            exprTys.set(expr, t);
        }
        return t;
    }

    function computeLUBTypes(): LUBResult {
        const constrainVid = (vid: number, ty: Ty) => {
            infcx.tyVars[vid].constrainedTy = ty;
            exprTys.set(infcx.tyVars[vid].origin.expr, ty);
        };
        let errors = false;

        while (true) {
            for (let i = 0; i < infcx.constraints.length; i++) {
                const constraint = infcx.constraints[i];
                const sub = infcx.tryResolve(constraint.sub);
                const sup = infcx.tryResolve(constraint.sup);

                switch (constraint.type) {
                    case 'SubtypeOf':
                        if (sub.type === 'i32' && sup.type === 'i32') {
                            // OK
                        } else if (sub.type === 'TyVid') {
                            if (sup.type === 'TyVid') {
                                // Can't progress.
                            } else {
                                constrainVid(sub.id, sup);
                            }
                        } else if (sub.type === 'never') {
                            // OK. Never is a subtype of all types.
                        } else {
                            // Error case.

                            let message: string;
                            switch (constraint.cause) {
                                case 'UseInArithmeticOperation':
                                    message = `cannot add '${sub.type}' to '${sup.type}'`;
                                    break;
                                default: message = `${sub.type} is not a subtype of ${sup.type} (reason: '${constraint.cause}')`;
                            }

                            error(src, constraint.at, `type error: ${message}`);
                            errors = true;
                        }
                        break;
                    default: assertUnreachable(constraint.type)
                }
            }
            break;
        }

        return { hadErrors: errors }
    }

    for (const stmt of ast.stmts) {
        typeckStmt(stmt);
    }

    const lub = computeLUBTypes();

    return { infcx, loweredTys, exprTys, hadErrors: lub.hadErrors };
}

type MirValue = { type: 'i32', value: number } | { type: 'Local', value: MirLocalId<true> } | { type: 'Unreachable' };
/**
 * `temporary` indicates whether this local is used for a subexpression.
 * These are trivially in SSA form and are never written to except when initialized.
 */
type MirLocal<temporary extends boolean = boolean> = { ty: Ty, temporary: temporary };
type MirLocalId<temporary extends boolean = boolean> = number;
type MirStmt = { type: 'Assignment', assignee: MirLocalId<false>, value: MirValue } | { type: 'BinOp', op: TokenType, assignee: MirLocalId<true>, lhs: MirValue, rhs: MirValue } | { type: 'Copy', assignee: MirLocalId<true>, local: MirLocalId<false> };
type MirTerminator = { type: 'Return' };
type MirBlock = {
    stmts: MirStmt[];
    terminator: MirTerminator | null;
};
type MirBody = { blocks: MirBlock[], locals: MirLocal[] };

function mangleTy(ty: Ty): string {
    switch (ty.type) {
        case 'never':
        case 'void':
        case 'string':
        case 'i32':
            return ty.type;
        case 'ArrayLiteral':
            return `$array$${mangleTy(ty.elemTy)}`;
        case 'TyParam':
        case 'TyVid':
        case 'FnDef':
            throw new Error(`attempted to mangle ${ty.type}`);
        default: assertUnreachable(ty);
    }
}
function mangleInstFn(decl: FnDecl, args: Ty[]): string {
    let mangled = decl.name;

    assert(decl.generics.length === args.length, `mismatched generic args when mangling ${decl.name}`);
    if (args.length > 0) {
        mangled += '$LT$';

        for (let i = 0; i < args.length; i++) {
            if (i !== 0) {
                mangled += '$$';
            }
            mangled += mangleTy(args[i]);
        }

        mangled += '$GT$';
    }

    return mangled;
}

/**
 * Instantiates a function's MIR with the given generic arguments.
 * 
 *    function f<T>(v: T) {}
 * 
 * calling `astToMir(f, [i32])` will create the MIR body for `function f(v: i32)`, and cache it.
 */
const _mirBodyCache = new Map<string, MirBody>();
function astToMir(src: string, mangledName: string, decl: FnDecl, args: Ty[], res: Resolutions, typeck: TypeckResults): MirBody {
    function lowerMir() {
        if (decl.body.type !== 'Block') throw `${decl.name} did not have a block as its body?`;

        const astLocalToMirLocal = new Map<LetDecl, MirLocalId<false>>();
        const locals: MirLocal[] = [
            // _0 = return place
            { ty: typeck.loweredTys.get(decl.ret)!, temporary: false }
        ];
        const addLocal = <temporary extends boolean = boolean>(ty: Ty, temporary: temporary): MirLocalId<temporary> => {
            locals.push({ ty, temporary });
            return locals.length - 1;
        };
        const returnPlace = locals[0] as MirLocal<false>;
        const returnId = 0 as MirLocalId<false>;
        const blocks: MirBlock[] = [
            {
                stmts: [],
                terminator: null,
            }
        ];
        let block = blocks[0];

        function lowerStmt(stmt: Stmt) {
            switch (stmt.type) {
                case 'FnDecl': break; // Nested bodies are only lowered when explicitly requested
                case 'LetDecl': {
                    const ty = typeck.exprTys.get(stmt.init)!;
                    const local = addLocal(ty, false);
                    astLocalToMirLocal.set(stmt, local);
                    const value = lowerExpr(stmt.init);
                    block.stmts.push({ type: 'Assignment', assignee: local, value });
                    break;
                }
                case 'Expr': lowerExpr(stmt.value); break;
                default: assertUnreachable(stmt);
            }
        }
        function lowerExpr(expr: Expr): MirValue {
            switch (expr.type) {
                case 'Number': return { type: 'i32', value: expr.value };
                case 'Literal': {
                    const id = astLocalToMirLocal.get(res.valueResolutions.get(expr)! as LetDecl)!;
                    const assignee = addLocal(locals[id].ty, true);
                    block.stmts.push({
                        type: 'Copy',
                        assignee,
                        local: id
                    });
                    return { type: 'Local', value: assignee };
                }
                case 'Return': {
                    const ret = lowerExpr(expr.value);
                    block.stmts.push({ type: 'Assignment', assignee: returnId, value: ret });
                    block.terminator = { type: 'Return' };
                    let newBlock = { stmts: [], terminator: null };
                    blocks.push(newBlock);
                    block = newBlock;
                    return { type: 'Unreachable' };
                }
                case 'Binary': {
                    const lhs = lowerExpr(expr.lhs);
                    const rhs = lowerExpr(expr.rhs);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'BinOp', assignee: res, lhs, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                default: todo(`Unhandled expr ${expr.type}`);
            }
        }

        for (const stmt of decl.body.stmts) {
            lowerStmt(stmt);
        }

        return {
            locals,
            blocks
        };
    }

    let mir = _mirBodyCache.get(mangledName);
    if (!mir) {
        mir = lowerMir();
        _mirBodyCache.set(mangledName, mir);
    }
    return mir;
}

function codegen(src: string, ast: Program, res: Resolutions, typeck: TypeckResults) {
    function llTy(ty: Ty): string {
        switch (ty.type) {
            case 'i32': return 'i32';
            case 'void': return 'void';
            case 'TyParam': throw new Error('uninstantiated type parameter in llir lowering');
            case 'string':
            case 'FnDef':
            case 'ArrayLiteral':
                todo(ty.type);
            case 'TyVid':
            case 'never':
                throw new Error(`${ty.type} should not appear in llir lowering`);
        }
    }

    function mirLocal<temporary extends boolean>(mir: MirBody, id: MirLocalId<temporary>): MirLocal<temporary> {
        return mir.locals[id] as MirLocal<temporary>;
    }

    function llValue(val: MirValue): string {
        switch (val.type) {
            case 'Local': return `%l.${val.value}`;
            case 'i32': return val.value.toString();
            case 'Unreachable': return 'poison';
        }
    }

    function llValTy(mir: MirBody, val: MirValue): string {
        switch (val.type) {
            case 'Local': {
                const local = mirLocal(mir, val.value);
                if (!local.temporary) {
                    return `${llTy(local.ty)}*`
                } else {
                    return llTy(local.ty);
                }
            }
            case 'i32': return 'i32';
            case 'Unreachable': todo('unreachable ty');
        }
    }

    function codegenFn(decl: FnDecl, args: Ty[]) {
        const mangledName = mangleInstFn(decl, args);

        let _temps = 0;
        let tempLocal = () => _temps++;
        const mir = astToMir(src, mangledName, decl, args, res, typeck);
        const getLocal = <temporary extends boolean>(id: MirLocalId<temporary>): MirLocal<temporary> => {
            return mir.locals[id] as MirLocal<temporary>;
        };

        const ret = typeck.loweredTys.get(decl.ret)!;
        assert(mir.locals[0].ty === ret, 'return type and return local\'s type must match');

        let output = `define ${llTy(ret)} @${mangledName}() {\n`;
        let writeBB = (name: string) => output += name + ':\n';

        // Prologue: alloca locals for explicit, real locals
        // (temporary locals are created on the fly)
        writeBB('prologue');
        for (let i = 0; i < mir.locals.length; i++) {
            const local = mir.locals[i];
            if (!local.temporary) {
                output += `%l.${i} = alloca ${llTy(local.ty)}\n`;
            }
        }
        output += 'br label %bb.0\n';

        // Begin codegening real blocks
        for (let i = 0; i < mir.blocks.length; i++) {
            const block = mir.blocks[i];
            if (block.stmts.length === 0) {
                continue;
            }

            output += '\n';
            writeBB(`bb.${i}`);

            for (let j = 0; j < block.stmts.length; j++) {
                const stmt = block.stmts[j];
                switch (stmt.type) {
                    case 'Assignment': {
                        const local = mirLocal(mir, stmt.assignee);
                        output += `store ${llValTy(mir, stmt.value)} ${llValue(stmt.value)}, ${llTy(local.ty)}* %l.${stmt.assignee}\n`;
                        break;
                    }
                    case 'BinOp': {
                        let binOp: string;
                        switch (stmt.op) {
                            case TokenType.Plus: binOp = 'add'; break;
                            default: todo('BinOp ' + stmt.op);
                        }
                        output += `%l.${stmt.assignee} = ${binOp} ${llValTy(mir, stmt.lhs)} ${llValue(stmt.lhs)}, ${llValue(stmt.rhs)}\n`;
                        break;
                    }
                    case 'Copy': {
                        const ty = llTy(getLocal(stmt.local).ty);
                        output += `%l.${stmt.assignee} = load ${ty}, ${ty}* %l.${stmt.local}\n`;
                        break;
                    }
                    default: assertUnreachable(stmt);
                }
            }

            // Process terminator
            const terminator = block.terminator;
            if (terminator) {
                switch (terminator.type) {
                    case 'Return':
                        const temp = tempLocal();
                        output += `%ret.${temp} = load ${llTy(ret)}, ${llTy(ret)}* %l.0\n`;
                        output += `ret ${llTy(ret)} %ret.${temp}`;
                        break;
                    default: assertUnreachable(terminator.type)
                }
            }
        }


        output += '\n}';

        return output;
    }

    // TODO: validate entrypoint fn? like no generics etc?
    return codegenFn(res.entrypoint, []);
}

function timed<T>(what: string, f: () => T): T {
    console.time(what);
    const res = f();
    console.timeEnd(what);
    return res;
}

const src = fs.readFileSync('./input', 'utf8');
const ast = timed('parse', () => parse(src));
const resolutions = timed('name res', () => computeResolutions(ast));
const tyres = timed('typeck', () => typeck(src, ast, resolutions));
const llir = timed('llir/mir codegen', () => codegen(src, ast, resolutions, tyres));

const llpath = `/tmp/tmpir${Date.now()}.ll`;
fs.writeFileSync(llpath, llir);
// TODO: don't use -Wno-override-module
timed('clang', () => cProcess.spawnSync(`clang -Wno-override-module ${llpath}`, {
    shell: true,
    stdio: 'inherit'
}));

console.log();
console.log('\x1b[1;32mcompilation succeeded\x1b[0m');
