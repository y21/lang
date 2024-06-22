import fs from 'fs';
import cProcess from 'child_process';
import { inspect as _inspect } from 'util';

function assertUnreachable(v: never): never {
    throw 'impossible';
}

function todo(what?: string): never {
    throw new Error('Todo: ' + what);
}

type OptLevel = '-O0' | '-O1' | '-O2' | '-O3' | '-O';
type CliOptions = {
    path: string,
    /**
     * When this is true, skip the `clang` step and just print the LLVM IR (the very last IR we generate) to the console.
     * Currently only used for tests
     */
    printLlirOnly: boolean;
    optLevel: OptLevel,
    verbose: boolean,
    timings: boolean;
    colors: boolean;
};

function parseOptions(): CliOptions {
    let path: string | null = null;
    let optLevel: OptLevel = '-O0';
    let verbose = false;
    let printLlirOnly = false;
    let timings = true;
    let colors = true;
    const args = process.argv.slice(2).values();

    let opt: IteratorResult<string>;
    while (!(opt = args.next()).done) {
        switch (opt.value) {
            case '-O3':
            case '-O2':
            case '-O1':
            case '-O0':
            case '-O': optLevel = opt.value; break;
            case '--print-llir-only': printLlirOnly = true; break;
            case '--no-timings': timings = false; break;
            case '--verbose': verbose = true; break;
            case '--no-colors': colors = false; break;
            default:
                if (path) {
                    throw new Error('cannot specify an input path twice');
                }
                path = opt.value;
                break;
        }
    }

    path ||= 'input';

    return { path, optLevel, verbose, printLlirOnly, timings, colors };
}
const options = parseOptions();

function inspect(v: any): string {
    return _inspect(v, { depth: Infinity, colors: options.colors });
}

type Span = [number, number];

function joinSpan(a: Span, b: Span): Span {
    return [a[0], b[1]];
}

// zero-based
type SpanInfo = { fromLine: number, fromCol: number, toLine: number, toCol: number };
function spanInfo(src: string, span: Span): SpanInfo {
    let prevLineStart = 0;
    let line = 0;
    while (prevLineStart < src.length) {
        const nextNewLine = src.indexOf('\n', prevLineStart);
        assert(nextNewLine > -1);
        let fromLine: number, fromCol: number, toLine: number | null = null, toCol: number | null = null;
        if (nextNewLine > span[0]) {
            fromLine = line;
            fromCol = span[0] - prevLineStart;

            while (prevLineStart < src.length) {
                const nextNewLine = src.indexOf('\n', prevLineStart);
                assert(nextNewLine > -1);
                if (nextNewLine > span[1]) {
                    toLine = line;
                    toCol = span[1] - prevLineStart;
                    break;
                }
                prevLineStart = nextNewLine + 1;
                line++;
            }

            if (toCol === null || toLine === null) {
                // span end points to the end of the file
                toLine = line;
                toCol = src.length - prevLineStart;
            }

            return { fromCol, fromLine, toCol, toLine };
        }

        prevLineStart = nextNewLine + 1;
        line++;
    }
    throw new Error('malformed span');
}

function ppSpan(src: string, span: Span): string {
    const inf = spanInfo(src, span);
    return `${inf.fromLine + 1}:${inf.fromCol + 1} ${inf.toLine + 1}:${inf.toCol + 1}`;
}

enum TokenType {
    Function,
    Let,
    Return,
    Type,
    Constructible,
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
    Mut,
    Number,
    String,
    Plus,
    Minus,
    Star,
    Slash,
    Dot,
    Lt,
    Gt,
    And,
    Or,
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
            case '&': tokens.push({ span: [start, i + 1], ty: TokenType.And }); break;
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
                        case 'mut': ty = TokenType.Mut; break;
                        case 'type': ty = TokenType.Type; break;
                        case 'constructible': ty = TokenType.Constructible; break;
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
    | { type: 'AddrOf', pointee: Expr, mtb: Mutability }
    | { type: 'Deref', pointee: Expr }
    | { type: 'Record', fields: RecordFields<Expr> }
);


type LetDecl = { type: 'LetDecl', name: string, init: Expr };

type FnDecl = {
    type: 'FnDecl',
    name: string,
    generics: Generics,
    parameters: FnParameter[],
    ret: AstTy,
    body: Expr
};
type FnParameter = { name: string, ty: AstTy };
type Generics = string[];
type TyAliasDecl = { type: 'TyAlias', name: string, generics: Generics, constructibleIn: Path<AstTy>[], alias: AstTy };
type GenericArg<Ty> = { type: 'Type', ty: Ty };
type PathSegment<Ty> = { ident: string; args: GenericArg<Ty>[] };
type Path<Ty> = { segments: PathSegment<Ty>[] };
type Stmt = { span: Span } & ({ type: 'Expr', value: Expr } | LetDecl | FnDecl | TyAliasDecl);
type Mutability = 'imm' | 'mut';
type RecordFields<Ty> = ([string, Ty])[];
type AstTy = { type: 'Path', value: Path<AstTy> }
    | { type: 'Array', elemTy: AstTy, len: number }
    | { type: 'Pointer', mtb: Mutability, pointeeTy: AstTy }
    | { type: 'Record', fields: RecordFields<AstTy> }
    | { type: 'Alias', alias: AstTy, constructibleIn: Path<never>[] };
type Program = { stmts: Stmt[] };
type LeftToRight = 'ltr';
type RightToLeft = 'rtl';
type Associativity = LeftToRight | RightToLeft;

const UNARY_PRECEDENCE: { [index: string]: number | undefined } = {
    // Somewhere between indexing/dot and multiplicative
    [TokenType.And]: 15,
    [TokenType.Star]: 15
};

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
                const ident = snip(tokens[i++].span);
                const args: GenericArg<AstTy>[] = [];
                if (eatToken(TokenType.Lt, false)) {
                    while (!eatToken(TokenType.Gt, false)) {
                        eatToken(TokenType.Comma, false);
                        args.push({ type: 'Type', ty: parseTy() });
                    }
                }
                const segment: PathSegment<AstTy> = {
                    args,
                    ident
                };

                ty = { type: 'Path', value: { segments: [segment] } };
                break;
            default: throw 'Unknown token for ty: ' + TokenType[tokens[i].ty];
            case TokenType.LBrace:
                i++;
                const fields: RecordFields<AstTy> = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    eatToken(TokenType.Comma, false);
                    const key = expectIdent();
                    eatToken(TokenType.Colon, true);
                    const value = parseTy();
                    fields.push([key, value]);
                }
                ty = { type: 'Record', fields };
                break;
        }

        while (i < tokens.length) {
            if (eatToken(TokenType.LSquare, false)) {
                const len = tokens[i++];
                if (len.ty !== TokenType.Number) throw new Error('array must have a length component');
                eatToken(TokenType.RSquare, true);
                ty = { type: 'Array', elemTy: ty, len: +snip(len.span) };
            } else if (eatToken(TokenType.Star, false)) {
                const mtb: Mutability = tokens[i].ty === TokenType.Mut ? (i++, 'mut') : 'imm';
                ty = { type: 'Pointer', mtb, pointeeTy: ty };
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
            case TokenType.Dot: {
                const span = tokens[i].span;
                i++;
                eatToken(TokenType.LBrace);
                const fields: RecordFields<Expr> = [];

                while (!eatToken(TokenType.RBrace, false)) {
                    eatToken(TokenType.Comma, false);
                    const ident = expectIdent();
                    eatToken(TokenType.Colon);
                    const value = parseRootExpr();
                    fields.push([ident, value]);
                }
                return { span: joinSpan(span, tokens[i - 1].span), type: 'Record', fields };
            }
            default: throw `Invalid token ${TokenType[tokens[i].ty]} at ${tokens[i].span} (expected bottom expression)`;
        }
        i++;
        return expr;
    }

    function parseExpr(minPrecedence: number): Expr {
        // Unary expressions.
        let expr: Expr;
        switch (tokens[i].ty) {
            case TokenType.Return: {
                let returnKwSpan = tokens[i++].span;
                const value = parseRootExpr();
                return { type: 'Return', span: joinSpan(returnKwSpan, value.span), value };
            }
            case TokenType.LBrace: {
                const lbraceSpan = tokens[i++].span;
                const stmts = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    stmts.push(parseStmt());
                }
                return { type: 'Block', span: joinSpan(lbraceSpan, tokens[i - 1].span), stmts };
            }
            case TokenType.And: {
                // Unary &
                const andSpan = tokens[i++].span;
                const pointee = parseExpr(UNARY_PRECEDENCE[TokenType.And]!);

                expr = { type: 'AddrOf', mtb: 'imm', pointee, span: joinSpan(andSpan, pointee.span) };
                break;
            }
            case TokenType.Star: {
                // Dereference
                const starSpan = tokens[i++].span;
                const pointee = parseExpr(UNARY_PRECEDENCE[TokenType.Star]!);
                expr = { type: 'Deref', pointee, span: joinSpan(starSpan, pointee.span) };
                break;
            }
            default:
                expr = parseBottomExpr();
        }


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

    // Assumes the current token is '<' in case of generics present.
    function parseGenericsList(): string[] {
        const generics: string[] = [];
        if (eatToken(TokenType.Lt, false)) {
            while (!eatToken(TokenType.Gt, false)) {
                eatToken(TokenType.Comma, false);
                const name = expectIdent();
                generics.push(name);
            }
        }
        return generics;
    }

    let parseRootExpr = () => parseExpr(-1);

    function parseStmt(): Stmt {
        switch (tokens[i].ty) {
            case TokenType.Function: {
                i++;
                const name = expectIdent();
                const generics = parseGenericsList();
                const parameters: FnParameter[] = [];

                eatToken(TokenType.LParen);
                while (!eatToken(TokenType.RParen, false)) {
                    eatToken(TokenType.Comma, false);
                    const name = expectIdent();
                    eatToken(TokenType.Colon);
                    const ty = parseTy();
                    parameters.push({ name, ty });
                }

                eatToken(TokenType.Colon);

                const ret = parseTy();
                const body = parseRootExpr();

                return {
                    type: 'FnDecl',
                    span: body.span, // TODO: wrong span
                    name,
                    generics,
                    parameters,
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
            case TokenType.Type: {
                const tySpan = tokens[i].span;
                i++;
                const name = expectIdent();
                const generics = parseGenericsList();
                const constructibleIn: Path<never>[] = [];

                if (eatToken(TokenType.Constructible, false)) {
                    eatToken(TokenType.LParen);
                    while (!eatToken(TokenType.RParen, false)) {
                        eatToken(TokenType.Comma, false);
                        constructibleIn.push({ segments: [{ args: [], ident: expectIdent() }] });
                    }
                }

                eatToken(TokenType.Assign);
                const alias = parseTy();
                eatToken(TokenType.Semi);
                return { span: [tySpan[0], tokens[i - 1].span[1]], type: 'TyAlias', name, alias, constructibleIn, generics };
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
type TyParamResolution = { type: 'TyParam', id: number, parentItem: FnDecl | TyAliasDecl };
type TypeResolution = TyParamResolution | { type: 'Primitive', kind: PrimitiveTy } | TyAliasDecl;
type TypeResolutions = Map<AstTy, TypeResolution>;
type ValueResolution = FnDecl | LetDecl | ({ type: 'FnParam', param: FnParameter });
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
            case 'Path': {
                if (ty.value.segments.length !== 1) {
                    throw new Error('path must have one segment');
                }
                for (const arg of ty.value.segments[0].args) resolveTy(arg.ty);

                const segment = ty.value.segments[0];
                switch (segment.ident) {
                    case 'void': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Void }); break;
                    case 'never': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.Never }); break;
                    case 'i32': tyMap.set(ty, { type: "Primitive", kind: PrimitiveTy.I32 }); break;
                    default: registerRes(segment.ident, ty, tyRes, tyMap); break;
                }
                break;
            }
            case 'Array': resolveTy(ty.elemTy); break;
            case 'Pointer': resolveTy(ty.pointeeTy); break;
            case 'Record':
                for (const [, v] of ty.fields) resolveTy(v);
                break;
            case 'Alias':
                resolveTy(ty.alias); break;
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
            case 'TyAlias': {
                tyRes.add(stmt.name, stmt);
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
            default: assertUnreachable(expr);
        }
    }

    function resolveFnDecl(decl: FnDecl) {
        valRes.add(decl.name, decl);
        valRes.withScope(() => {
            tyRes.withScope(() => {
                for (let i = 0; i < decl.generics.length; i++) {
                    tyRes.add(decl.generics[i], { type: 'TyParam', id: i, parentItem: decl });
                }

                for (const param of decl.parameters) {
                    valRes.add(param.name, { type: 'FnParam', param });
                    resolveTy(param.ty);
                }

                resolveTy(decl.ret);
                resolveExpr(decl.body);
            });
        });
    }

    valRes.withScope(() => {
        tyRes.withScope(() => {
            for (const stmt of ast.stmts) {
                if (stmt.type === 'FnDecl' && stmt.name === 'main') {
                    entrypoint = stmt;
                }
                resolveStmt(stmt);
            }
        });
    });

    if (!entrypoint) {
        throw "'main' function not found";
    }

    return { tyResolutions: tyMap, valueResolutions: identMap, entrypoint };
}

type RecordType = { type: 'Record', fields: RecordFields<Ty> };
type Ty = ({ flags: TypeFlags }) & ({ type: 'TyVid', id: number }
    | { type: 'void' }
    | { type: 'never' }
    | { type: 'i32' }
    | { type: 'string' }
    | { type: 'Array', elemTy: Ty, len: number }
    | { type: 'TyParam', id: number, parentItem: FnDecl | TyAliasDecl }
    | { type: 'FnDef', decl: FnDecl }
    | { type: 'Pointer', mtb: Mutability, pointee: Ty }
    | RecordType
    | { type: 'Alias', decl: TyAliasDecl, alias: Ty, args: Ty[] });

type TypeFlags = number;
const TYPARAM_MASK = 0b01;
const TYVID_MASK = 0b10;
const EMPTY_FLAGS = 0;
function hasTyParam(ty: Ty): boolean {
    return (ty.flags & TYPARAM_MASK) !== 0;
}
function withoutTyParam(flags: TypeFlags): TypeFlags {
    return flags & ~TYPARAM_MASK;
}
function hasTyVid(ty: Ty): boolean {
    return (ty.flags & TYVID_MASK) !== 0;
}
function removeTyVid(ty: Ty): Ty {
    ty.flags &= ~TYVID_MASK;
    return ty;
}

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'UseInArithmeticOperation' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index' | 'FnArgument';
type Constraint = { cause: ConstraintCause, at: Span } & ConstraintType;

type FnLocalState = {
    expectedReturnTy: Ty;
    returnFound: boolean;
    localTypes: Map<LetDecl | FnParameter, Ty>;
};

type TypeckResults = {
    infcx: Infcx,
    loweredTys: Map<AstTy, Ty>,
    instantiatedFnSigs: Map<Expr, InstantiatedFnSig>,
    exprTys: Map<Expr, Ty>,
    hadErrors: boolean
};

type InstantiatedFnSig = {
    parameters: Ty[],
    ret: Ty,
    args: Ty[]
};

type InfTyVar = {
    constrainedTy: Ty | null,
    origin: TyVarOrigin,
    // When constraining this inference variable to a concrete type, then we may need to insert new types into the `exprTys` map
    deferredExprs: Expr[],
    // Same as with `deferredExprs`, but will replace any affected inference variables in this `InstantiatedFnSig`
    dereferredInsts: InstantiatedFnSig[]
};
type TyVarOrigin = { span: Span } & ({ type: 'Expr' } | { type: 'GenericArg' });
type LUBResult = { hadErrors: boolean };

class Infcx {
    tyVars: Array<InfTyVar> = [];
    constraints: Constraint[] = [];
    fnStack: FnLocalState[] = [];
    exprTys = new Map<Expr, Ty>();

    constructor() { }

    sub(cause: ConstraintCause, at: Span, sub: Ty, sup: Ty) {
        this.constraints.push({ type: 'SubtypeOf', at, cause, sub, sup });
    }

    mkTyVar(origin: TyVarOrigin): Ty {
        const id = this.tyVars.length;
        this.tyVars.push({ constrainedTy: null, deferredExprs: [], dereferredInsts: [], origin });
        return { type: 'TyVid', flags: EMPTY_FLAGS, id };
    }

    mkTyVarExt(origin: TyVarOrigin, deferredExprs: Expr[], dereferredInsts: InstantiatedFnSig[]): Ty {
        const id = this.tyVars.length;
        this.tyVars.push({ constrainedTy: null, deferredExprs, dereferredInsts, origin });
        return { type: 'TyVid', flags: EMPTY_FLAGS, id };
    }

    withFn(expect: Ty, localTypes: Map<LetDecl | FnParameter, Ty>, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect, returnFound: false, localTypes });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (expectedReturnTy.type !== 'void' && !returnFound) {
            throw `Expected ${expect.type}, got void`;
        }
    }

    registerLocal(decl: LetDecl, ty: Ty) {
        this.fnStack[this.fnStack.length - 1].localTypes.set(decl, ty);
    }

    localTy(decl: LetDecl | FnParameter): Ty | undefined {
        return this.fnStack[this.fnStack.length - 1].localTypes.get(decl);
    }

    registerReturn(at: Span, ty: Ty) {
        const fs = this.fnStack[this.fnStack.length - 1];
        fs.returnFound = true;
        const sup = fs.expectedReturnTy;
        this.sub('Return', at, ty, sup);
    }

    // For type aliases, instantiates and returns the aliased type. E.g.
    //
    //     type X<T> = { v: T }
    //
    // Calling `normalize(X<i32>)` returns `{ v: i32 }`.
    // For any other kind of type, this just returns it unchanged.
    normalize(ty: Ty): Ty {
        while (ty.type === 'Alias') {
            ty = instantiateTy(ty.alias, ty.args);
        }

        return ty;
    }

    deferExprTy(ty: { type: 'TyVid', id: number }, expr: Expr) {
        this.tyVars[ty.id].deferredExprs.push(expr);
    }

    deferInstSig(ty: { type: 'TyVid', id: number }, sig: InstantiatedFnSig) {
        this.tyVars[ty.id].dereferredInsts.push(sig);
    }

    tryResolve(ty: Ty): Ty {
        if (ty.type === 'TyVid' && this.tyVars[ty.id].constrainedTy) {
            return this.tyVars[ty.id].constrainedTy!;
        }
        return ty;
    }
}

/**
 * Pretty prints a type. This is *exclusively* for error reporting.
 */
function ppTy(ty: Ty): string {
    switch (ty.type) {
        case 'i32':
        case 'never':
        case 'string':
        case 'void':
            return ty.type;
        case 'Array':
            return `${ppTy(ty.elemTy)}[${ty.len}]`;
        case 'Pointer':
            return `${ppTy(ty.pointee)}*`
        case 'TyParam': return ty.parentItem.generics[ty.id];
        case 'TyVid': return `?${ty.id}t`;
        case 'FnDef': return `fn ${ty.decl.name}(...)`;
        case 'Record': {
            let out = '{';
            for (let i = 0; i < ty.fields.length; i++) {
                if (i !== 0) {
                    out += ',';
                }
                out += `${ty.fields[i][0]}: ${ppTy(ty.fields[i][1])}`;
            }
            return out + '}';
        }
        case 'Alias': return ppTy(ty.alias);
    }
}

function error(src: string, span: Span, message: string) {
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
}

// creates a new type with type parameters replaced with the provided args
function instantiateTy(ty: Ty, args: Ty[]): Ty {
    // Fast path: type flags can instantly tell us if this type doesn't have any type parameters
    if (!hasTyParam(ty)) return ty;

    switch (ty.type) {
        case 'Alias': {
            let flags = EMPTY_FLAGS;
            const instArgs: Ty[] = [];
            for (const arg of ty.args) {
                const inst = instantiateTy(arg, args);
                flags |= withoutTyParam(inst.flags);
                instArgs.push(inst);
            }
            return {
                ...ty,
                flags,
                args: instArgs,
            };
        }
        case 'TyVid':
        case 'i32':
        case 'never':
        case 'string':
        case 'void':
            // simple cases: nothing to instantiate
            return ty;
        case 'TyParam':
            assert(ty.id < args.length, 'type parameter index out of bounds');
            return args[ty.id];
        case 'Array': {
            const elemTy = instantiateTy(ty, args);
            return { ...ty, flags: withoutTyParam(elemTy.flags), elemTy };
        }
        case 'FnDef': throw new Error('attempted to instantiate FnDef'); break;
        case 'Pointer': {
            const pointee = instantiateTy(ty.pointee, args);
            return { ...ty, flags: withoutTyParam(pointee.flags), pointee };
        }
        case 'Record': {
            let flags = EMPTY_FLAGS;
            const fields: RecordFields<Ty> = [];

            for (const [key, value] of ty.fields) {
                const ty = instantiateTy(value, args);
                flags |= withoutTyParam(ty.flags);
                fields.push([key, ty]);
            }

            return { flags, type: 'Record', fields: fields };
        }
    }
}

function typeck(src: string, ast: Program, res: Resolutions): TypeckResults {
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
                            case PrimitiveTy.Void: return { type: 'void', flags: EMPTY_FLAGS };
                            case PrimitiveTy.Never: return { type: 'never', flags: EMPTY_FLAGS };
                            case PrimitiveTy.I32: return { type: 'i32', flags: EMPTY_FLAGS };
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
                case 'Alias': throw new Error('cannot lower type aliases directly');
                default: assertUnreachable(ty);
            }
        }
        lowered = lowerInner(ty);
        loweredTys.set(ty, lowered);
        return lowered;
    }

    function typeckFn(decl: FnDecl) {
        const ret = lowerTy(decl.ret);
        const locals = new Map();
        infcx.withFn(ret, locals, () => { typeckExpr(decl.body); });
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
            case 'TyAlias': break;
            default: assertUnreachable(stmt);
        }
    }

    function typeckExpr(expr: Expr): Ty {
        function inner(expr: Expr): Ty {
            switch (expr.type) {
                case 'Block': for (const stmt of expr.stmts) typeckStmt(stmt); return { type: 'void', flags: 0 };
                case 'Literal': {
                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        case 'FnDecl': return { type: 'FnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'LetDecl': return infcx.localTy(litres)!;
                        case 'FnParam': return lowerTy(litres.param.ty);
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
                        elemTy = infcx.mkTyVar({ type: "Expr", span: expr.span });
                    } else {
                        elemTy = typeckExpr(expr.elements[0]);
                        for (let i = 1; i < expr.elements.length; i++) infcx.sub('ArrayLiteral', expr.elements[i].span, typeckExpr(expr.elements[i]), elemTy);
                    }
                    return { type: 'Array', flags: elemTy.flags, elemTy, len: expr.elements.length };
                }
                case 'Assignment': {
                    infcx.sub('Assignment', expr.span, typeckExpr(expr.value), typeckExpr(expr.target));
                    return { type: 'void', flags: EMPTY_FLAGS };
                }
                case 'Index': {
                    infcx.sub('Index', expr.span, typeckExpr(expr.index), { type: 'i32', flags: EMPTY_FLAGS });
                    const target = typeckExpr(expr.target);
                    if (target.type === 'Array') {
                        return target.elemTy;
                    } else {
                        // TODO: constraint for tyvar
                        throw `Cannot index into ${target.type}`
                    }
                }
                // TODO: typescript's "as const" can create a literal type?
                case 'Number': return { type: 'i32', flags: EMPTY_FLAGS };
                case 'String': return { type: 'string', flags: EMPTY_FLAGS };
                case 'Binary': {
                    infcx.sub('UseInArithmeticOperation', expr.lhs.span, typeckExpr(expr.lhs), { type: 'i32', flags: EMPTY_FLAGS });
                    infcx.sub('UseInArithmeticOperation', expr.rhs.span, typeckExpr(expr.rhs), { type: 'i32', flags: EMPTY_FLAGS });
                    return { type: 'i32', flags: EMPTY_FLAGS };
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
                        if (callee.type !== 'FnDef') {
                            throw new Error('callee must be a FnDef');
                        }

                        // HACK: create the signature with dummy data so that we have an object reference to stick into the ty var
                        const sig: InstantiatedFnSig = {
                            parameters: [],
                            ret: { type: 'void', flags: EMPTY_FLAGS },
                            args: []
                        };

                        for (let i = 0; i < callee.decl.generics.length; i++) {
                            const tv = infcx.mkTyVarExt({ type: 'GenericArg', span: expr.span }, [], [sig]);
                            sig.args.push(tv);
                        }

                        // with `genericArgs` created we can fix up the signature
                        for (const param of callee.decl.parameters) {
                            const ty = lowerTy(param.ty);
                            sig.parameters.push(instantiateTy(ty, sig.args));
                        }
                        sig.ret = instantiateTy(lowerTy(callee.decl.ret), sig.args);

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
                    const target = infcx.normalize(typeckExpr(expr.target));
                    if (target.type !== 'Record') {
                        throw new Error(`property access requires record type, got ${ppTy(target)}`);
                    }
                    const field = target.fields.find(([k]) => k === expr.property);
                    if (!field) {
                        throw new Error(`field '${expr.property}' not found on type ${ppTy(target)}`);
                    }
                    return field[1];
                default: assertUnreachable(expr);
            }
        }
        const t = inner(expr);
        if (t.type === 'TyVid') {
            // Type variables are later inserted when the least-upper type is computed based on the constraints.
            infcx.deferExprTy(t, expr);
        } else {
            infcx.exprTys.set(expr, t);
        }
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

            const resolve = (ty: Ty): Ty => {
                return ty.type === 'TyVid' && ty.id === vid ? infcx.tyVars[vid].constrainedTy! : ty;
            };

            for (const expr of infcx.tyVars[vid].deferredExprs) {
                infcx.exprTys.set(expr, ty);
            }
            for (const sig of infcx.tyVars[vid].dereferredInsts) {
                for (let i = 0; i < sig.args.length; i++) {
                    sig.args[i] = resolve(sig.args[i]);
                }
                for (let i = 0; i < sig.parameters.length; i++) {
                    sig.parameters[i] = resolve(sig.parameters[i]);
                }
                sig.ret = resolve(sig.ret);
            }
            madeProgress = true;
        };

        while (madeProgress) {
            madeProgress = false;
            for (let i = infcx.constraints.length - 1; i >= 0; i--) {
                const constraint = infcx.constraints.pop()!;
                const sub = infcx.tryResolve(constraint.sub);
                const sup = infcx.tryResolve(constraint.sup);

                function subFields(sub: Ty & RecordType, sup: Ty & RecordType) {
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
                                infcx.constraints.push({ at: constraint.at, cause: constraint.cause, sub: subf[1], sup: supf[1], type: 'SubtypeOf' });
                            }
                        }
                        madeProgress = true;
                    }
                }

                switch (constraint.type) {
                    case 'SubtypeOf':
                        if (sub.type === 'i32' && sup.type === 'i32') {
                            // OK
                        } else if (sub.type === 'Record' && sup.type === 'Record') {
                            subFields(sub, sup);
                        } else if (sub.type === 'TyParam' && sup.type === 'TyParam' && sub.id === sup.id) {
                            // OK
                        } else if (sub.type === 'Record' && sup.type === 'Alias') {
                            // TODO: also check args
                            const nsup = infcx.normalize(sup);
                            if (nsup.type === 'Record') {
                                if (
                                    sup.decl.constructibleIn.length > 0
                                    // Can only unify if the constraint was added in any of the specified functions.
                                    // TODO: actually check this. figure out how to get the parentFn here
                                    && !sup.decl.constructibleIn.some((v) => true)
                                ) {
                                    error(src, constraint.at, `error: '${sup.decl.name}' cannot be constructed here`);
                                }
                                subFields(sub, nsup);
                            }
                        } else if (sub.type === 'Alias' && sup.type === 'Alias') {
                            // TODO: check constructibleIn for both aliases
                            infcx.constraints.push({ type: 'SubtypeOf', sub: infcx.normalize(sub), sup: infcx.normalize(sup), at: constraint.at, cause: constraint.cause });
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
                            infcx.constraints.push(constraint);
                        }
                        else if (sub.type === 'never') {
                            // OK. Never is a subtype of all types.
                        } else {
                            // Error case.

                            let message: string;
                            switch (constraint.cause) {
                                case 'UseInArithmeticOperation':
                                    message = `cannot add ${sub.type} to ${sup.type}`;
                                    break;
                                default: message = `${ppTy(sub)} is not a subtype of ${ppTy(sup)} (reason: '${constraint.cause}')`;
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
                    error(src, tyvar.origin.span, `type error: unconstrained type variable created here`)
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

    return { infcx, loweredTys, exprTys: infcx.exprTys, instantiatedFnSigs, hadErrors: lub.hadErrors };
}

type MirValue = { type: 'i32', value: number }
    | { type: 'Local', value: MirLocalId<true> }
    | { type: 'Unreachable' }
    | { type: 'FnDef', value: FnDecl }
    | { type: 'Record', value: RecordFields<MirValue> };
/**
 * `temporary` indicates whether this local is used for a subexpression.
 * These are trivially in SSA form and are never written to except when initialized.
 */
type MirLocal<temporary extends boolean = boolean> = { ty: Ty, temporary: temporary };
type MirLocalId<temporary extends boolean = boolean> = number;
type Projection = { type: 'Field', property: string } | { type: 'Deref' };
type MirPlace<temporary extends boolean = boolean> = { base: MirLocalId<temporary>, projections: Projection[] };
type MirStmt = { type: 'Assignment', assignee: MirLocalId<false>, value: MirValue }
    | { type: 'BinOp', op: TokenType, assignee: MirLocalId<true>, lhs: MirValue, rhs: MirValue }
    | { type: 'Copy', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'AddrOfLocal', assignee: MirLocalId<true>, local: MirLocalId<false> };
type MirTerminator = { type: 'Return' }
    | { type: 'Call', assignee: MirLocalId<true>, args: MirValue[], decl: FnDecl, sig: InstantiatedFnSig, target: MirBlockId };
type MirBlock = {
    stmts: MirStmt[];
    terminator: MirTerminator | null;
};
type MirBlockId = number;
type MirBody = { blocks: MirBlock[], parameters: MirLocalId<false>[], locals: MirLocal[] };

function mangleTy(ty: Ty): string {
    switch (ty.type) {
        case 'never':
        case 'void':
        case 'string':
        case 'i32':
            return ty.type;
        case 'Array':
            return `$array$${ty.len}$${mangleTy(ty.elemTy)}`;
        case 'TyParam':
        case 'TyVid':
        case 'FnDef':
            throw new Error(`attempted to mangle ${ty.type}`);
        case 'Pointer':
            return `$ptr$${ty.mtb}$${mangleTy(ty.pointee)}`;
        case 'Alias':
            let out = mangleTy(ty.alias);
            if (ty.args.length > 0) {
                out += '$LT$';
                for (let i = 0; i < ty.args.length; i++) {
                    if (i !== 0) out += '$$';
                    out += mangleTy(ty.args[i]);
                }
                out += '$RT$';
            }
            return out;
        case 'Record': todo('mangle record ty');
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
    function lowerMir(): MirBody {
        if (decl.body.type !== 'Block') throw `${decl.name} did not have a block as its body?`;

        const astLocalToMirLocal = new Map<LetDecl | FnParameter, MirLocalId<false>>();
        const locals: MirLocal[] = [];
        const addLocal = <temporary extends boolean = boolean>(ty: Ty, temporary: temporary): MirLocalId<temporary> => {
            ty = instantiateTy(ty, args);
            locals.push({ ty, temporary });
            return locals.length - 1;
        };
        // _0 = return place
        assert(addLocal(typeck.loweredTys.get(decl.ret)!, false) === 0);
        const returnPlace = locals[0] as MirLocal<false>;
        const returnId = 0 as MirLocalId<false>;
        const blocks: MirBlock[] = [
            {
                stmts: [],
                terminator: null,
            }
        ];
        let block = blocks[0];

        const parameters = [];
        for (const param of decl.parameters) {
            const local = addLocal(typeck.loweredTys.get(param.ty)!, false);
            parameters.push(local);
            astLocalToMirLocal.set(param, local);
        }

        /**
         * If the given value is a place, assigns a copy of it to a local and returns that local.
         * Otherwise returns the value unchanged.
         */
        function asValue(val: ({ type: 'Place' } & MirPlace<boolean>) | MirValue, ty: Ty): MirValue {
            if (val.type === 'Place') {
                // Trivial case: base is already a non-temporary local with no projections. E.g. simply `x`
                if (!locals[val.base].temporary && val.projections.length === 0) return { type: 'Local', value: val.base };

                const res = addLocal(ty, true);
                block.stmts.push({
                    type: 'Copy',
                    assignee: res,
                    place: val
                });
                return { type: 'Local', value: res };
            } else {
                return val;
            }
        }

        function lowerStmt(stmt: Stmt) {
            switch (stmt.type) {
                case 'FnDecl': break; // Nested bodies are only lowered when explicitly requested
                case 'LetDecl': {
                    const ty = typeck.exprTys.get(stmt.init)!;
                    const local = addLocal(ty, false);
                    astLocalToMirLocal.set(stmt, local);
                    const value = asValue(lowerExpr(stmt.init), ty);
                    block.stmts.push({ type: 'Assignment', assignee: local, value });
                    break;
                }
                case 'Expr': lowerExpr(stmt.value); break;
                case 'TyAlias': break;
                default: assertUnreachable(stmt);
            }
        }
        function lowerExpr(expr: Expr): MirValue | ({ type: 'Place' } & MirPlace) {
            switch (expr.type) {
                case 'Number': return { type: 'i32', value: expr.value };
                case 'Literal': {
                    const resolution = res.valueResolutions.get(expr)!;
                    switch (resolution.type) {
                        case 'FnDecl': {
                            return {
                                type: 'FnDef',
                                value: resolution
                            };
                        };
                        case 'FnParam':
                        case 'LetDecl': {
                            const id = astLocalToMirLocal.get(resolution.type === 'LetDecl' ? resolution : resolution.param)!;
                            const assignee = addLocal(locals[id].ty, true);
                            block.stmts.push({
                                type: 'Copy',
                                assignee,
                                place: { base: id, projections: [] }
                            });

                            return { type: 'Local', value: assignee };
                        }
                        default: assertUnreachable(resolution);
                    }
                }
                case 'Return': {
                    const ret = asValue(lowerExpr(expr.value), typeck.exprTys.get(expr.value)!);
                    block.stmts.push({ type: 'Assignment', assignee: returnId, value: ret });
                    block.terminator = { type: 'Return' };
                    let newBlock = { stmts: [], terminator: null };
                    blocks.push(newBlock);
                    block = newBlock;
                    return { type: 'Unreachable' };
                }
                case 'Binary': {
                    const lhs = asValue(lowerExpr(expr.lhs), typeck.exprTys.get(expr.lhs)!);
                    const rhs = asValue(lowerExpr(expr.rhs), typeck.exprTys.get(expr.rhs)!);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'BinOp', assignee: res, lhs, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'AddrOf': {
                    switch (expr.pointee.type) {
                        case 'Literal':
                            const lres = res.valueResolutions.get(expr.pointee);
                            if (lres?.type === 'LetDecl') {
                                const res = addLocal(typeck.exprTys.get(expr.pointee)!, true);
                                block.stmts.push({ type: 'AddrOfLocal', assignee: res, local: astLocalToMirLocal.get(lres)! });
                                return { type: 'Local', value: res };
                            } else {
                                throw new Error(`cannot take address of non-local variable`);
                            }
                        // TODO: we can const-promote number literals
                        default: throw new Error(`cannot take address of ${expr.pointee.type}`);
                    }
                }
                case 'Deref': {
                    const pointee = lowerExpr(expr.pointee);
                    if (pointee.type !== 'Place') {
                        throw new Error('deref pointee must be a place');
                    }
                    pointee.projections.push({ type: 'Deref' });
                    return pointee;
                }
                case 'FnCall': {
                    const callee = lowerExpr(expr.callee);
                    if (callee.type !== 'FnDef') {
                        throw new Error('callee must be a FnDef');
                    }
                    const sig = typeck.instantiatedFnSigs.get(expr)!;
                    const res = addLocal(sig.ret, true);

                    const args = expr.args.map(v => asValue(lowerExpr(v), typeck.exprTys.get(v)!));

                    const targetBlock = blocks.length;
                    blocks.push({ stmts: [], terminator: null });

                    block.terminator = { type: 'Call', args, assignee: res, decl: callee.value, sig, target: targetBlock };
                    block = blocks[targetBlock];

                    return { type: 'Local', value: res };
                }
                case 'Property': {
                    const val = lowerExpr(expr.target);
                    if (val.type === 'Place') {
                        val.projections.push({ type: 'Field', property: expr.property });
                        return val;
                    } else {
                        let base: MirLocalId;
                        if (val.type !== 'Local') {
                            throw new Error('property base must be a local');
                        } else {
                            base = val.value;
                        }
                        return {
                            type: 'Place',
                            base: base,
                            projections: [{ type: 'Field', property: expr.property }]
                        }
                    }
                }
                case 'Record': {
                    const fields: RecordFields<MirValue> = expr.fields.map(([key, expr]) => {
                        return [key, asValue(lowerExpr(expr), typeck.exprTys.get(expr)!)];
                    });
                    return {
                        type: 'Record',
                        value: fields
                    }
                }
                default: todo(`Unhandled expr ${expr.type}`);
            }
        }

        for (const stmt of decl.body.stmts) {
            lowerStmt(stmt);
        }

        return {
            locals,
            blocks,
            parameters
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
    const _codegenCache = new Set<string>();
    let fnSection = '';

    function llTy(ty: Ty): string {
        switch (ty.type) {
            case 'i32': return 'i32';
            case 'void': return 'void';
            case 'Pointer':
                return `${llTy(ty.pointee)}*`;
            case 'TyParam': throw new Error('uninstantiated type parameter in llir lowering');
            case 'string':
            case 'FnDef':
            case 'Array':
            case 'Alias':
                todo(ty.type);
            case 'Record': return '{' + ty.fields.map(v => llTy(v[1])).join(', ') + '}';
            case 'TyVid':
            case 'never':
                throw new Error(`${ty.type} should not appear in llir lowering`);
        }
    }

    function mirLocal<temporary extends boolean>(mir: MirBody, id: MirLocalId<temporary>): MirLocal<temporary> {
        return mir.locals[id] as MirLocal<temporary>;
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
            case 'FnDef': throw new Error('FnDef values need to be treated specially');
            case 'Record': return '{' + val.value.map(v => llValTy(mir, v[1])).join(', ') + '}';
        }
    }

    function renameAliases(mir: MirBody) {
        const aliasGraph = new Map<MirLocalId, MirLocalId>();
        function processStmtOrTerm(s: MirStmt | MirTerminator) {
            function patchObjKey<K extends string>(o: Record<K, MirLocalId>, p: K) {
                while (aliasGraph.has(o[p])) {
                    o[p] = aliasGraph.get(o[p])!;
                }
            }
            function patchValue(val: MirValue) {
                if (val.type === 'Local') patchObjKey(val, 'value');
            }
            switch (s.type) {
                case 'AddrOfLocal': aliasGraph.set(s.assignee, s.local); break;
                case 'Assignment': patchObjKey(s, 'assignee'); patchValue(s.value); break;
                case 'BinOp':
                    patchObjKey(s, 'assignee');
                    patchValue(s.lhs);
                    patchValue(s.rhs);
                    break;
                case 'Copy':
                    patchObjKey(s, 'assignee');
                    patchObjKey(s.place, 'base');
                    break;
                case 'Return': break;
                case 'Call':
                    s.args.forEach(patchValue);
                    break;
                default: assertUnreachable(s);
            }
        }
        for (const block of mir.blocks) {
            for (const stmt of block.stmts) processStmtOrTerm(stmt);
            if (block.terminator) processStmtOrTerm(block.terminator);
        }
    }

    function codegenFn(decl: FnDecl, args: Ty[]) {
        function inner(decl: FnDecl, args: Ty[]) {

            let _temps = 0;
            let tempLocal = () => _temps++;
            const mir = astToMir(src, mangledName, decl, args, res, typeck);
            renameAliases(mir);

            const getLocal = <temporary extends boolean>(id: MirLocalId<temporary>): MirLocal<temporary> => {
                return mirLocal(mir, id);
            };

            const ret = mir.locals[0].ty;

            const parameterList = mir.parameters.map((id) => `${llTy(getLocal(id).ty)} %lt.${id}`).join(', ');

            let output = `define ${llTy(ret)} @${mangledName}(${parameterList}) {\n`;

            function compileValueToLocal(val: MirValue): string {
                switch (val.type) {
                    case 'Local': return `%l.${val.value}`;
                    case 'i32': return val.value.toString();
                    case 'Unreachable': return 'poison';
                    case 'FnDef': throw new Error('FnDef values need to be treated specially');
                    case 'Record': {
                        // compile {x: 1i32, y: 2i64} to:
                        //
                        // %t1 = alloca {i32, i64}
                        // %p1 = getelementptr {i32, i64}, {i32, i64}* %t1, i32 0, i32 0
                        // store i32 1, i32* %p1
                        // %p1 = getelementptr {i32, i64}, {i32, i64}* %t1, i32 0, i32 1
                        // store i32 2, i32* %p1
                        // %t3 = load %t1
                        // return %t3
                        const tyS = llValTy(mir, val);
                        const tmp = `%t.${tempLocal()}`;
                        // note: write it to a temporary string first and then append it later, since we might potentially have interleaving writes to `output`
                        // during calls to `compileValueToLocal`
                        let tmpOut = '';
                        tmpOut += `${tmp} = alloca ${tyS}\n`;
                        for (let i = 0; i < val.value.length; i++) {
                            const ptrLocal = `%p.${tempLocal()}`;
                            const valueS = compileValueToLocal(val.value[i][1]);
                            const valTyS = llValTy(mir, val.value[i][1]);
                            tmpOut += `${ptrLocal} = getelementptr ${tyS}, ${tyS}* ${tmp}, i32 0, i32 ${i}\n`;
                            tmpOut += `store ${valTyS} ${valueS}, ${valTyS}* ${ptrLocal}\n`;
                        }
                        const loadLocal = `%t.${tempLocal()}`;
                        tmpOut += `${loadLocal} = load ${tyS}, ${tyS}* ${tmp}\n`;
                        output += tmpOut;
                        return loadLocal;
                    }
                }
            }

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
            // Also copy the SSA parameters into alloca'd locals
            for (const param of mir.parameters) {
                const local = getLocal(param);
                output += `store ${llTy(local.ty)} %lt.${param}, ${llTy(local.ty)}* %l.${param}\n`;
            }

            output += 'br label %bb.0\n';

            // Begin codegening real blocks
            for (let i = 0; i < mir.blocks.length; i++) {
                const block = mir.blocks[i];
                if (block.stmts.length === 0 && block.terminator === null) {
                    continue;
                }

                output += '\n';
                writeBB(`bb.${i}`);

                for (let j = 0; j < block.stmts.length; j++) {
                    const stmt = block.stmts[j];
                    switch (stmt.type) {
                        case 'Assignment': {
                            const local = getLocal(stmt.assignee);
                            const valS = compileValueToLocal(stmt.value);
                            output += `store ${llValTy(mir, stmt.value)} ${valS}, ${llTy(local.ty)}* %l.${stmt.assignee}\n`;
                            break;
                        }
                        case 'BinOp': {
                            let binOp: string;
                            switch (stmt.op) {
                                case TokenType.Plus: binOp = 'add'; break;
                                case TokenType.Minus: binOp = 'sub'; break;
                                case TokenType.Star: binOp = 'mul'; break;
                                default: todo('BinOp ' + stmt.op);
                            }
                            const lhsS = compileValueToLocal(stmt.lhs);
                            const rhsS = compileValueToLocal(stmt.rhs);
                            output += `%l.${stmt.assignee} = ${binOp} ${llValTy(mir, stmt.lhs)} ${lhsS}, ${rhsS}\n`;
                            break;
                        }
                        case 'Copy': {
                            const rawBase = mir.locals[stmt.place.base];

                            let finalLocal: string;
                            let finalTy = rawBase.ty;
                            if (rawBase.temporary) {
                                // This could be e.g.:
                                //     _ = f().v.x  where f(): {v:{x:i32}}
                                // 
                                // _1 = f()
                                // _2 = copy {base: _1 /* {v:{x:i32}} */, projections: ['v', 'x']}
                                //
                                // We generally want to codegen these projections as a series of GEP, which requires a pointer operand
                                // so we alloca a new variable that we store the base in.
                                const baseId = `%t.${tempLocal()}`;
                                output += `${baseId} = alloca ${llTy(rawBase.ty)}\n`;
                                output += `store ${llTy(rawBase.ty)} %l.${stmt.place.base}, ${llTy(rawBase.ty)}* ${baseId}\n`;
                                finalLocal = baseId;
                            } else {
                                // If it's not a temporary, then the base is most likely a local variable.
                                // In any case, `temporary = false` means that it must be alloca'd, so there is no need to do the above,
                                // as we already have a pointer that we can GEP into.
                                finalLocal = `%l.${stmt.place.base}`;
                            }

                            // For the above example f().v.x:
                            //
                            // ; process base:
                            // _1 = f(): {v:{x:i32}}
                            // _2 = alloca {v:{x:i32}}
                            // store _1 -> _2
                            //
                            // ; process projections:
                            // _3 = getelementptr {v:{x:i32}}, _2, 0, 0      ; _3 = {x: i32}*
                            // _4 = getelementptr {x:i32}, _3, 0, 0          ; _4 = i32*
                            //
                            // _4 gives us the final pointer to the last projected place, the `i32`,
                            // which we can finally copy into the assignee.

                            for (const projection of stmt.place.projections) {
                                if (projection.type === 'Deref') todo('deref projections');

                                const oldBase = finalLocal;
                                const oldTy = finalTy;
                                finalLocal = `%t.${tempLocal()}`;
                                if (oldTy.type !== 'Record') {
                                    throw new Error('projection target must be a record type');
                                }
                                const oldTyS = llTy(oldTy);

                                const projectedIndex = oldTy.fields.findIndex(v => v[0] === projection.property);
                                finalTy = oldTy.fields[projectedIndex][1];
                                output += `${finalLocal} = getelementptr ${oldTyS}, ${oldTyS}* ${oldBase}, i32 0, i32 ${projectedIndex}\n`;
                            }

                            output += `%l.${stmt.assignee} = load ${llTy(finalTy)}, ${llTy(finalTy)}* ${finalLocal}\n`;
                            break;
                        }
                        case 'AddrOfLocal': throw new Error('AddrOfLocal should be handled in renameAliases');
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
                            output += `ret ${llTy(ret)} %ret.${temp}\n`;
                            break;
                        case 'Call':
                            const calleeMangled = mangleInstFn(terminator.decl, terminator.sig.args);
                            codegenFn(terminator.decl, terminator.sig.args);
                            // NB: don't write to `output` here before the `argList` mapping, since that may compile values
                            const argList = terminator.args.map(arg => `${llValTy(mir, arg)} ${compileValueToLocal(arg)}`).join(', ');
                            output += `%l.${terminator.assignee} = call ${llTy(terminator.sig.ret)} @${calleeMangled}(${argList})\n`;
                            output += `br label %bb.${terminator.target}\n`;
                            break;
                        default: assertUnreachable(terminator)
                    }
                }
            }

            output += '\n}\n\n';

            return output;
        }

        const mangledName = mangleInstFn(decl, args);
        if (_codegenCache.has(mangledName)) return;
        _codegenCache.add(mangledName);
        const code = inner(decl, args)
        fnSection += code;
    }

    // TODO: validate entrypoint fn? like no generics etc?
    codegenFn(res.entrypoint, []);
    return fnSection;
}

function timed<T>(what: string, f: () => T): T {
    if (options.timings) {
        console.time(what);
        const res = f();
        console.timeEnd(what);
        return res;
    } else {
        return f();
    }
}

const src = fs.readFileSync(options.path, 'utf8');
const ast = timed('parse', () => parse(src));
const resolutions = timed('name res', () => computeResolutions(ast));
const tyres = timed('typeck', () => typeck(src, ast, resolutions));
if (options.verbose) {
    tyres.exprTys.forEach((v, k) => console.log(`expr @ ${ppSpan(src, k.span)} => ${ppTy(v)}`));
    console.log();
}
const llir = timed('llir/mir codegen', () => codegen(src, ast, resolutions, tyres));

if (options.printLlirOnly) {
    console.log(llir);
} else {
    const llpath = `/tmp/tmpir${Date.now()}.ll`;
    fs.writeFileSync(llpath, llir);
    // TODO: don't use -Wno-override-module
    timed('clang', () => cProcess.spawnSync(`clang ${options.optLevel} -Wno-override-module ${llpath}`, {
        shell: true,
        stdio: 'inherit'
    }));
    fs.unlinkSync(llpath);
}

