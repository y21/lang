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
    Extern,
    Fn,
    Let,
    Return,
    If,
    For,
    While,
    Type,
    True,
    False,
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
    EqEq,
    Not,
    NotEq,
    Semi,
    Comma,
    Mut,
    Underscore,
    Number,
    String,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Dot,
    Lt,
    Le,
    Gt,
    Ge,
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
    return isAlphaStart(c) || isDigit(c) || c === '_';
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
            case '_': tokens.push({ span: [start, i + 1], ty: TokenType.Underscore }); break;
            case ')': tokens.push({ span: [start, i + 1], ty: TokenType.RParen }); break;
            case '[': tokens.push({ span: [start, i + 1], ty: TokenType.LSquare }); break;
            case ']': tokens.push({ span: [start, i + 1], ty: TokenType.RSquare }); break;
            case '{': tokens.push({ span: [start, i + 1], ty: TokenType.LBrace }); break;
            case '}': tokens.push({ span: [start, i + 1], ty: TokenType.RBrace }); break;
            case '%': tokens.push({ span: [start, i + 1], ty: TokenType.Percent }); break;
            case ':': tokens.push({ span: [start, i + 1], ty: TokenType.Colon }); break;
            case '!':
                if (src[i + 1] === '=') {
                    tokens.push({ span: [start, i + 2], ty: TokenType.NotEq });
                    i++;
                } else {
                    tokens.push({ span: [start, i + 1], ty: TokenType.Not });
                }
                break;
            case '=':
                if (src[i + 1] === '=') {
                    tokens.push({ span: [start, i + 2], ty: TokenType.EqEq });
                    i++;
                } else {
                    tokens.push({ span: [start, i + 1], ty: TokenType.Assign });
                }
                break;
            case ';': tokens.push({ span: [start, i + 1], ty: TokenType.Semi }); break;
            case '.': tokens.push({ span: [start, i + 1], ty: TokenType.Dot }); break;
            case '<':
                if (src[i + 1] === '=') {
                    tokens.push({ span: [start, i + 2], ty: TokenType.Le });
                    i++;
                } else {
                    tokens.push({ span: [start, i + 1], ty: TokenType.Lt });
                }
                break;
            case '>':
                if (src[i + 1] === '=') {
                    tokens.push({ span: [start, i + 2], ty: TokenType.Ge });
                    i++;
                } else {
                    tokens.push({ span: [start, i + 1], ty: TokenType.Gt });
                }
                break;
            case ',': tokens.push({ span: [start, i + 1], ty: TokenType.Comma }); break;
            case '+': tokens.push({ span: [start, i + 1], ty: TokenType.Plus }); break;
            case '-': tokens.push({ span: [start, i + 1], ty: TokenType.Minus }); break;
            case '*': tokens.push({ span: [start, i + 1], ty: TokenType.Star }); break;
            case '&': tokens.push({ span: [start, i + 1], ty: TokenType.And }); break;
            case '/': {
                if (src[i + 1] === '/') {
                    while (i < src.length && src[i] !== '\n') i++;
                } else {
                    tokens.push({ span: [start, i + 1], ty: TokenType.Slash }); break;
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
                        case 'extern': ty = TokenType.Extern; break;
                        case 'fn': ty = TokenType.Fn; break;
                        case 'let': ty = TokenType.Let; break;
                        case 'return': ty = TokenType.Return; break;
                        case 'mut': ty = TokenType.Mut; break;
                        case 'type': ty = TokenType.Type; break;
                        case 'constructible': ty = TokenType.Constructible; break;
                        case 'true': ty = TokenType.True; break;
                        case 'false': ty = TokenType.False; break;
                        case 'if': ty = TokenType.If; break;
                        case 'for': ty = TokenType.For; break;
                        case 'while': ty = TokenType.While; break;
                        default: ty = TokenType.Ident; break;
                    }
                    tokens.push({ span, ty });
                } else if (isDigit(src[i])) {
                    while (isDigit(src[i]) || src[i] === 'i' || src[i] === 'u') i++;
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
type BinaryOp =
    | TokenType.Plus
    | TokenType.Minus
    | TokenType.Star
    | TokenType.Slash
    | TokenType.EqEq
    | TokenType.NotEq
    | TokenType.Lt
    | TokenType.Le
    | TokenType.Gt
    | TokenType.Ge
    | TokenType.Percent;

type UnaryOp = TokenType.Not;

type Expr = { span: Span } & (
    | { type: "Block"; stmts: Stmt[] }
    | { type: "Literal"; ident: string, args: AstTy[] | null }
    | { type: "FnCall"; args: Expr[]; callee: Expr }
    | { type: "Index"; target: Expr; index: Expr }
    | { type: "ArrayLiteral"; elements: Expr[] }
    | { type: "ArrayRepeat"; element: Expr; count: number }
    | { type: "Number"; value: number; suffix: IntTy }
    | { type: "Bool"; value: boolean }
    | { type: "String"; value: string }
    | { type: "Assignment"; target: Expr; value: Expr }
    | { type: "Property"; target: Expr; property: string | number }
    | { type: "Return"; value: Expr }
    | { type: "Unary"; op: UnaryOp; rhs: Expr }
    | {
        type: "Binary";
        op: BinaryOp;
        lhs: Expr;
        rhs: Expr;
    }
    | { type: "AddrOf"; pointee: Expr; mtb: Mutability }
    | { type: "Deref"; pointee: Expr }
    | { type: "Record"; fields: RecordFields<Expr> }
    | { type: "If"; condition: Expr; then: Expr; else: Expr | null }
    | { type: "While"; condition: Expr; body: Expr }
    | { type: "Tuple", elements: Expr[] }
);

type LetDecl = { type: 'LetDecl', name: string, ty: AstTy | null, init: Expr };

type AstFnSignature = {
    name: string,
    generics: Generics,
    parameters: FnParameter[],
    ret?: AstTy,
};
type FnDecl = {
    type: 'FnDecl',
    sig: AstFnSignature,
    body: Expr
};
type ExternFnDecl = {
    type: 'ExternFnDecl'
    abi: 'C' | 'intrinsic',
    sig: AstFnSignature
};
type FnParameter = { name: string, ty: AstTy };
type Generics = string[];
type TyAliasDecl = { type: 'TyAlias', name: string, generics: Generics, constructibleIn: Path<AstTy>[], alias: AstTy };
type GenericArg<Ty> = { type: 'Type', ty: Ty };
type PathSegment<Ty> = { ident: string; args: GenericArg<Ty>[] };
type Path<Ty> = { segments: PathSegment<Ty>[] };
type Stmt = { span: Span } & ({ type: 'Expr', value: Expr } | LetDecl | FnDecl | TyAliasDecl | ExternFnDecl);
type Mutability = 'imm' | 'mut';
type RecordFields<Ty> = ([string, Ty])[];
type AstTy = { type: 'Path', value: Path<AstTy> }
    | { type: 'Array', elemTy: AstTy, len: number }
    | { type: 'Tuple', elements: AstTy[] }
    | { type: 'Pointer', mtb: Mutability, pointeeTy: AstTy }
    | { type: 'Record', fields: RecordFields<AstTy> }
    | { type: 'Alias', alias: AstTy, constructibleIn: Path<never>[] }
    | { type: 'Infer' };
type Program = { stmts: Stmt[] };
type LeftToRight = 'ltr';
type RightToLeft = 'rtl';
type Associativity = LeftToRight | RightToLeft;

function genericsOfDecl(decl: FnDecl | TyAliasDecl | ExternFnDecl): Generics {
    if (decl.type === 'TyAlias') return decl.generics;
    else return decl.sig.generics;
}

const UNARY_PRECEDENCE: { [index: string]: number | undefined } = {
    // Somewhere between indexing/dot and multiplicative
    [TokenType.And]: 15,
    [TokenType.Star]: 15,
    [TokenType.Not]: 15,
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
    [TokenType.Percent]: 12,
    // Additive
    [TokenType.Plus]: 11,
    [TokenType.Minus]: 11,
    [TokenType.Lt]: 9,
    [TokenType.Le]: 9,
    [TokenType.Gt]: 9,
    [TokenType.Ge]: 9,
    [TokenType.EqEq]: 8,
    [TokenType.NotEq]: 8,
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
    [TokenType.Percent]: 'ltr',
    [TokenType.Not]: 'ltr',
    [TokenType.Lt]: 'ltr',
    [TokenType.Le]: 'ltr',
    [TokenType.Gt]: 'ltr',
    [TokenType.Ge]: 'ltr',
    [TokenType.EqEq]: 'ltr',
    [TokenType.NotEq]: 'ltr',
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
        if (ident.ty !== TokenType.Ident) throw new Error('Expected ident, got ' + TokenType[ident.ty]);
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
            case TokenType.LParen: {
                i++;
                if (eatToken(TokenType.RParen, false)) {
                    // Empty tuple type.
                    ty = { type: 'Tuple', elements: [] };
                    break;
                }

                const tty = parseTy();
                if (eatToken(TokenType.RParen, false)) {
                    // (<ty>) is not a tuple but rather grouping
                    ty = tty;
                } else {
                    // (<ty>,)
                    // (<ty>,<ty>,...)
                    eatToken(TokenType.Comma, true);
                    const elements: AstTy[] = [tty];
                    while (!eatToken(TokenType.RParen, false)) {
                        if (elements.length > 1) {
                            eatToken(TokenType.Comma, true);
                        }
                        elements.push(parseTy());
                    }
                    ty = { type: 'Tuple', elements };
                }
                break;
            }
            case TokenType.Underscore: i++; return { type: 'Infer' };
            default: throw 'Unknown token for ty: ' + TokenType[tokens[i].ty];
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
            case TokenType.Number: {
                const suffixes: [string, Ty][] = [
                    ['u8', U8],
                    ['u16', U16],
                    ['u32', U32],
                    ['u64', U64],
                    ['i8', I8],
                    ['i16', I16],
                    ['i32', I32],
                    ['i64', I64],
                ];
                let fullSnip = snip(tokens[i].span);
                let foundSuffix = suffixes.find((suffix) => fullSnip.endsWith(suffix[0]));
                if (foundSuffix) {
                    const unsuffixSpan: Span = [tokens[i].span[0], tokens[i].span[1] - foundSuffix[0].length]
                    const unsuffixSnip = +snip(unsuffixSpan);
                    if (!Number.isInteger(unsuffixSnip)) {
                        throw new Error(`${unsuffixSnip} is not an integer`);
                    }

                    expr = { type: 'Number', span: unsuffixSpan, suffix: (foundSuffix[1] as { type: 'int', value: IntTy }).value, value: unsuffixSnip };
                } else {
                    expr = { type: 'Number', span: tokens[i].span, suffix: { signed: true, bits: 32, }, value: +snip(tokens[i].span) };
                }
                break;
            }
            case TokenType.String: expr = { type: 'String', span: tokens[i].span, value: snip([tokens[i].span[0] + 1, tokens[i].span[1] - 1]) }; break;
            case TokenType.Ident:
                let ident = snip(tokens[i].span);
                let args: AstTy[] | null;
                if (tokens[i + 1].ty === TokenType.Colon && tokens[i + 2].ty === TokenType.Colon) {
                    i += 3;
                    eatToken(TokenType.Lt, true);
                    args = [];
                    while (!eatToken(TokenType.Gt, false)) {
                        if (args.length > 0) eatToken(TokenType.Comma, true);
                        args.push(parseTy());
                    }
                    i--;
                } else {
                    args = null;
                }
                expr = { type: 'Literal', span: tokens[i].span, ident, args }; break;
            case TokenType.True: expr = { type: 'Bool', span: tokens[i].span, value: true }; break;
            case TokenType.False: expr = { type: 'Bool', span: tokens[i].span, value: false }; break;
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
            case TokenType.LSquare: {
                const span = tokens[i].span;
                i++;
                const elements: Expr[] = [];
                while (!eatToken(TokenType.RSquare, false)) {
                    if (elements.length > 0) eatToken(TokenType.Comma);
                    elements.push(parseRootExpr());

                    if (elements.length === 1 && eatToken(TokenType.Semi, false)) {
                        // We have something like `[expr;`: this is an array repeat expression
                        const count = parseRootExpr();
                        if (count.type !== 'Number') {
                            throw new Error(`array repeat expression must be a number, got ${count.type}`);
                        }
                        eatToken(TokenType.RSquare);
                        return { type: 'ArrayRepeat', count: count.value, element: elements[0], span: joinSpan(span, tokens[i - 1].span) };
                    }
                }
                return { type: 'ArrayLiteral', elements, span: joinSpan(span, tokens[i - 1].span) };
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
                expr = { type: 'Return', span: joinSpan(returnKwSpan, value.span), value };
                break;
            }
            case TokenType.LBrace: {
                const lbraceSpan = tokens[i++].span;
                const stmts = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    stmts.push(parseStmt());
                }
                expr = { type: 'Block', span: joinSpan(lbraceSpan, tokens[i - 1].span), stmts };
                break;
            }
            case TokenType.LParen: {
                // Either tuple type or grouping, depending on if the expression is followed by a comma
                const lparenSpan = tokens[i++].span;
                if (tokens[i].ty === TokenType.RParen) {
                    i++;
                    expr = { type: 'Tuple', elements: [], span: joinSpan(lparenSpan, tokens[i - 1].span) };
                    break;
                }

                const first = parseRootExpr();
                if (eatToken(TokenType.Comma, false)) {
                    const elements = [first];
                    while (!eatToken(TokenType.RParen, false)) {
                        if (elements.length > 1) {
                            eatToken(TokenType.Comma, true);
                        }
                        elements.push(parseRootExpr());
                    }
                    expr = { type: 'Tuple', elements, span: joinSpan(lparenSpan, tokens[i - 1].span) };
                } else {
                    eatToken(TokenType.RParen);
                    expr = first;
                }
                break;
            }
            case TokenType.If: {
                const ifSpan = tokens[i++].span;
                const condition = parseRootExpr();
                const body = parseBlockExpr();
                // TODO: else
                expr = { type: 'If', condition, then: body, else: null, span: joinSpan(ifSpan, tokens[i - 1].span) };
                break;
            }
            case TokenType.While: {
                const whileSpan = tokens[i++].span;
                const condition = parseRootExpr();
                const body = parseBlockExpr();
                expr = { type: 'While', body, condition, span: joinSpan(whileSpan, tokens[i - 1].span) };
                break;
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
            case TokenType.Not: {
                // Unary !
                const notSpan = tokens[i++].span;
                const rhs = parseExpr(UNARY_PRECEDENCE[TokenType.Not]!);
                expr = { type: 'Unary', op: TokenType.Not, rhs, span: joinSpan(notSpan, rhs.span) };
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
                    let property: string | number;
                    switch (tokens[i].ty) {
                        case TokenType.Ident: property = snip(tokens[i++].span); break;
                        case TokenType.Number: property = +snip(tokens[i++].span); break;
                        default: throw new Error('property must be a string or number');
                    }
                    expr = { type: 'Property', target: expr, property, span: [expr.span[0], tokens[i - 1].span[1]] }
                    break;
                }
                case TokenType.Plus:
                case TokenType.Minus:
                case TokenType.Star:
                case TokenType.EqEq:
                case TokenType.NotEq:
                case TokenType.Lt:
                case TokenType.Le:
                case TokenType.Gt:
                case TokenType.Ge:
                case TokenType.Slash:
                case TokenType.Percent: {
                    const rhs = parseExpr(prec);
                    expr = { type: 'Binary', op: op.ty, lhs: expr, rhs, span: joinSpan(expr.span, rhs.span) };
                    break;
                }
                case TokenType.LSquare: {
                    const index = parseRootExpr();
                    eatToken(TokenType.RSquare);
                    expr = { type: 'Index', index, span: joinSpan(expr.span, tokens[i - 1].span), target: expr };
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

    let parseBlockExpr = () => {
        const expr = parseRootExpr();
        if (expr.type !== 'Block') throw new Error(`expected block expression, got ${expr.type}`);
        return expr;
    };
    let parseRootExpr = () => parseExpr(-1);

    /**
     * Parses `fn foo(x: i32, y: i32): i32`, without an associated block.
     */
    function parseFnSignature(): AstFnSignature {
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

        const ret = eatToken(TokenType.Colon, false) ? parseTy() : undefined;

        return {
            name,
            generics,
            parameters,
            ret,
        };
    }

    function parseStmt(): Stmt {
        const startSpan = tokens[i].span;
        switch (tokens[i].ty) {
            case TokenType.Extern: {
                i++;
                const abi = parseRootExpr();
                if (abi.type !== 'String' || (abi.value !== 'C' && abi.value !== 'intrinsic')) {
                    throw new Error('extern abi must be a string and "C" or "intrinsic"');
                }

                eatToken(TokenType.Fn, true);
                const sig = parseFnSignature();
                eatToken(TokenType.Semi, true);

                return {
                    type: 'ExternFnDecl',
                    sig,
                    abi: abi.value,
                    span: joinSpan(startSpan, tokens[i - 1].span)
                };
            }
            case TokenType.Fn: {
                i++;
                const sig = parseFnSignature();
                const body = parseRootExpr();

                return {
                    type: 'FnDecl',
                    body,
                    span: joinSpan(startSpan, tokens[i - 1].span),
                    sig
                };
            }
            case TokenType.Let: {
                let letSpan = tokens[i].span;
                i++;
                const name = expectIdent();
                let ty: AstTy | null = null;
                if (eatToken(TokenType.Colon, false)) {
                    ty = parseTy();
                }
                eatToken(TokenType.Assign);
                const init = parseRootExpr();
                eatToken(TokenType.Semi);
                return { span: joinSpan(letSpan, tokens[i - 1].span), ty, type: 'LetDecl', name, init };
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

type IntrinsicName = 'bitcast' | 'ext' | 'trunc';
type Intrinsic = ({ abi: 'intrinsic' }) & ExternFnDecl;

function mkIntrinsic(name: IntrinsicName, generics: Generics, parameters: FnParameter[], ret: AstTy): Intrinsic {
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
    mkIntrinsic('bitcast', ['T', 'U'], [{ name: 'v', ty: identPathTy('T') }], identPathTy('U')),
    mkIntrinsic('ext', ['T', 'U'], [{ name: 'v', ty: identPathTy('T') }], identPathTy('U')),
    mkIntrinsic('trunc', ['T', 'U'], [{ name: 'v', ty: identPathTy('T') }], identPathTy('U'))
];
type TyParamResolution = { type: 'TyParam', id: number, parentItem: FnDecl | TyAliasDecl | ExternFnDecl };
type TypeResolution = TyParamResolution | { type: 'Primitive', kind: PrimitiveTy } | TyAliasDecl;
type TypeResolutions = Map<AstTy, TypeResolution>;
type ValueResolution = FnDecl | LetDecl | ExternFnDecl | ({ type: 'FnParam', param: FnParameter });
type ValueResolutions = Map<Expr, ValueResolution>;
type Resolutions = { tyResolutions: TypeResolutions, valueResolutions: ValueResolutions, entrypoint: FnDecl };

function computeResolutions(ast: Program): Resolutions {
    const tyRes = new ResNamespace<TypeResolution>();
    const valRes = new ResNamespace<ValueResolution>();
    let entrypoint: FnDecl | null = null;

    const tyMap: Map<AstTy, TypeResolution> = new Map();
    const identMap: Map<Expr, ValueResolution> = new Map();

    const withAllScopes = (f: () => void) => {
        tyRes.withScope(() => {
            valRes.withScope(() => {
                f();
            });
        })
    };

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
                break;
            }
            case 'Array': resolveTy(ty.elemTy); break;
            case 'Pointer': resolveTy(ty.pointeeTy); break;
            case 'Record':
                for (const [, v] of ty.fields) resolveTy(v);
                break;
            case 'Alias':
                resolveTy(ty.alias); break;
            case 'Infer': break;
            case 'Tuple': for (const elem of ty.elements) resolveTy(elem); break;
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
                resolveExpr(stmt.init);
                if (stmt.ty) {
                    resolveTy(stmt.ty);
                }
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
            case 'Literal':
                registerRes(expr.ident, expr, valRes, identMap);
                if (expr.args) {
                    for (const arg of expr.args) resolveTy(arg);
                }
                break;
            case 'Block': for (const stmt of expr.stmts) resolveStmt(stmt); break;
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
                resolveExpr(expr.body);
                resolveExpr(expr.condition);
                break;
            case 'Unary':
                resolveExpr(expr.rhs);
                break;
            case 'Tuple':
                for (const element of expr.elements) {
                    resolveExpr(element);
                }
                break;
            default: assertUnreachable(expr);
        }
    }

    function resolveFnSig(sig: AstFnSignature, item: FnDecl | ExternFnDecl) {
        for (let i = 0; i < sig.generics.length; i++) {
            tyRes.add(sig.generics[i], { type: 'TyParam', id: i, parentItem: item });
        }

        for (const param of sig.parameters) {
            valRes.add(param.name, { type: 'FnParam', param });
            resolveTy(param.ty);
        }

        if (sig.ret) {
            resolveTy(sig.ret);
        }
    }

    function resolveFnDecl(decl: FnDecl) {
        if (INTRINSICS.some(ins => ins.sig.name === decl.sig.name)) {
            throw new Error(`function cannot have name '${decl.sig.name}' because it is the name of an intrinsic`);
        }
        valRes.add(decl.sig.name, decl);
        withAllScopes(() => {
            resolveFnSig(decl.sig, decl);
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

    return { tyResolutions: tyMap, valueResolutions: identMap, entrypoint };
}

type RecordType = { type: 'Record', fields: RecordFields<Ty> };
type Bits = 8 | 16 | 32 | 64;
type IntTy = { signed: boolean, bits: Bits };
type Ty = ({ flags: TypeFlags }) & ({ type: 'TyVid', id: number }
    | { type: 'Tuple', elements: Ty[] }
    | { type: 'never' }
    | { type: 'bool' }
    | { type: 'int', value: IntTy }
    | { type: 'str' }
    | { type: 'Array', elemTy: Ty, len: number }
    | { type: 'TyParam', id: number, parentItem: FnDecl | TyAliasDecl | ExternFnDecl }
    | { type: 'FnDef', decl: FnDecl }
    | { type: 'ExternFnDef', decl: ExternFnDecl }
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
function withoutTyVid(flags: TypeFlags): TypeFlags {
    return flags & ~TYVID_MASK;
}
function hasTyVid(ty: Ty): boolean {
    return (ty.flags & TYVID_MASK) !== 0;
}
function removeTyVid(ty: Ty): Ty {
    ty.flags &= ~TYVID_MASK;
    return ty;
}
const I8: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 8 } };
const I16: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 16 } };
const I32: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 32 } };
const I64: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 64 } };
const U8: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 8 } };
const U16: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 16 } };
const U32: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 32 } };
const U64: Ty = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 64 } };
const UNIT: Ty = { type: 'Tuple', flags: EMPTY_FLAGS, elements: [] };
const BOOL: Ty = { type: 'bool', flags: EMPTY_FLAGS };

function isUnit(ty: Ty): boolean {
    return ty.type === 'Tuple' && ty.elements.length === 0;
}

type ConstraintType = { type: 'SubtypeOf', sub: Ty, sup: Ty }
type ConstraintCause = 'Binary' | 'Assignment' | 'Return' | 'ArrayLiteral' | 'Index' | 'FnArgument' | 'UseInCondition' | 'Unary';
type Constraint = { cause: ConstraintCause, at: Span, depth: number } & ConstraintType;
const MAX_CONSTRAINT_DEPTH = 200;

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
};
type TyVarOrigin = ({ type: 'Expr', expr: Expr } | { type: 'GenericArg', span: Span });
function tyVarOriginSpan(origin: TyVarOrigin): Span {
    switch (origin.type) {
        case 'Expr': return origin.expr.span;
        case 'GenericArg': return origin.span;
    }
}
type LUBResult = { hadErrors: boolean };

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

    withFn(expect: Ty | undefined, localTypes: Map<LetDecl | FnParameter, Ty>, f: () => void) {
        this.fnStack.push({ expectedReturnTy: expect || UNIT, returnFound: false, localTypes });
        f();
        const { expectedReturnTy, returnFound } = this.fnStack.pop()!;
        if (!isUnit(expectedReturnTy) && !returnFound) {
            throw `Expected ${expectedReturnTy.type}, got ()`;
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

    tryResolve(ty: Ty): Ty {
        if (ty.type === 'TyVid' && this.tyVars[ty.id].constrainedTy) {
            return this.tyVars[ty.id].constrainedTy!;
        }
        return ty;
    }
}

function returnTy(sig: AstFnSignature, typeck: TypeckResults): Ty {
    return sig.ret ? typeck.loweredTys.get(sig.ret)! : UNIT;
}

/**
 * Pretty prints a type. This is *exclusively* for error reporting.
 */
function ppTy(ty: Ty): string {
    switch (ty.type) {
        case 'int':
            return (ty.value.signed ? 'i' : 'u') + ty.value.bits;
        case 'never':
        case 'bool':
        case 'str':
            return ty.type;
        case 'Array':
            return `${ppTy(ty.elemTy)}[${ty.len}]`;
        case 'Pointer':
            return `${ppTy(ty.pointee)}*`
        case 'TyParam': return genericsOfDecl(ty.parentItem)[ty.id];
        case 'TyVid': return `?${ty.id}t`;
        case 'FnDef':
            return `fn ${ty.decl.sig.name}(...)`;
        case 'ExternFnDef':
            return `extern "${ty.decl.abi}" fn ${ty.decl.sig.name}(...)`;
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
        case 'Alias':
            return `${ty.decl.name}<${ty.args.map(ty => ppTy(ty)).join(', ')}>`;
        case 'Tuple': return `(${ty.elements.map(ppTy).join(', ')})`
    }
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
                flags |= inst.flags;
                instArgs.push(inst);
            }
            return {
                ...ty,
                flags,
                args: instArgs,
            };
        }
        case 'TyVid':
        case 'int':
        case 'never':
        case 'str':
        case 'bool':
            // simple cases: nothing to instantiate
            return ty;
        case 'TyParam':
            assert(ty.id < args.length, 'type parameter index out of bounds');
            return args[ty.id];
        case 'Array': {
            const elemTy = instantiateTy(ty, args);
            return { ...ty, flags: elemTy.flags, elemTy };
        }
        case 'FnDef':
        case 'ExternFnDef':
            throw new Error('attempted to instantiate FnDef');
        case 'Pointer': {
            const pointee = instantiateTy(ty.pointee, args);
            return { ...ty, flags: pointee.flags, pointee };
        }
        case 'Record': {
            let flags = EMPTY_FLAGS;
            const fields: RecordFields<Ty> = [];

            for (const [key, value] of ty.fields) {
                const ty = instantiateTy(value, args);
                flags |= ty.flags;
                fields.push([key, ty]);
            }

            return { flags, type: 'Record', fields: fields };
        }
        case 'Tuple': {
            let flags = EMPTY_FLAGS;
            const elements: Ty[] = [];

            for (const element of ty.elements) {
                const ty = instantiateTy(element, args);
                flags |= ty.flags;
                elements.push(ty);
            }

            return { type: 'Tuple', flags, elements };
        }
    }
}

// For type aliases, instantiates and returns the aliased type. E.g.
//
//     type X<T> = { v: T }
//
// Calling `normalize(X<i32>)` returns `{ v: i32 }`.
// For any other kind of type, this just returns it unchanged.
function normalize(ty: Ty): Ty {
    while (ty.type === 'Alias') {
        ty = instantiateTy(ty.alias, ty.args);
    }

    return ty;
}

function forEachExprInStmt(stmt: Stmt, f: (e: Expr) => void) {
    switch (stmt.type) {
        case 'Expr': forEachExpr(stmt.value, f); break;
        case 'FnDecl': forEachExpr(stmt.body, f); break;
        case 'LetDecl': forEachExpr(stmt.init, f); break;
        case 'TyAlias': break;
    }
}

function forEachExpr(expr: Expr, f: (e: Expr) => void) {
    f(expr);

    switch (expr.type) {
        case 'Literal':
        case 'Number':
        case 'Bool':
        case 'String': break;
        case 'Block': for (const stmt of expr.stmts) forEachExprInStmt(stmt, f); break;
        case 'Return': forEachExpr(expr.value, f); break;
        case 'ArrayLiteral': for (const elem of expr.elements) forEachExpr(elem, f); break;
        case 'ArrayRepeat': forEachExpr(expr.element, f); break;
        case 'Assignment':
            forEachExpr(expr.target, f);
            forEachExpr(expr.value, f);
            break;
        case 'Index':
            forEachExpr(expr.target, f);
            forEachExpr(expr.index, f);
            break;
        case 'Binary':
            forEachExpr(expr.lhs, f);
            forEachExpr(expr.rhs, f);
            break;
        case 'AddrOf': forEachExpr(expr.pointee, f); break;
        case 'Deref': forEachExpr(expr.pointee, f); break;
        case 'Record':
            for (const [, field] of expr.fields) {
                forEachExpr(field, f)
            }
            break;
        case 'FnCall':
            forEachExpr(expr.callee, f);
            for (const arg of expr.args) forEachExpr(arg, f);
            break;
        case 'Property':
            forEachExpr(expr.target, f);
            break;
        case 'If':
            forEachExpr(expr.condition, f);
            forEachExpr(expr.then, f);
            if (expr.else) {
                forEachExpr(expr.else, f);
            }
            break;
        case 'While':
            forEachExpr(expr.condition, f);
            forEachExpr(expr.body, f);
            break;
        case 'Unary':
            forEachExpr(expr.rhs, f);
            break;
        case 'Tuple':
            for (const element of expr.elements) {
                forEachExpr(element, f);
            }
            break;
        default: assertUnreachable(expr);
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
                default: assertUnreachable(ty);
            }
        }
        lowered = lowerInner(ty);
        loweredTys.set(ty, lowered);
        return lowered;
    }

    function typeckFn(decl: FnDecl) {
        const ret = decl.sig.ret && lowerTy(decl.sig.ret);
        const locals = new Map();
        infcx.withFn(ret, locals, () => { typeckExpr(decl.body); });
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

    function typeckExpr(expr: Expr): Ty {
        function inner(expr: Expr): Ty {
            switch (expr.type) {
                case 'Block': for (const stmt of expr.stmts) typeckStmt(stmt); return UNIT;
                case 'Literal': {
                    const litres = res.valueResolutions.get(expr)!;
                    switch (litres.type) {
                        // TODO: is EMPTY_FLAGS correct here..?
                        case 'FnDecl': return { type: 'FnDef', flags: EMPTY_FLAGS, decl: litres };
                        case 'ExternFnDecl': return { type: 'ExternFnDef', flags: EMPTY_FLAGS, decl: litres };
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
                case 'String': return { type: 'Pointer', mtb: 'imm', flags: EMPTY_FLAGS, pointee: { type: 'str', flags: EMPTY_FLAGS } };
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

                        if (expr.callee.type === 'Literal' && expr.callee.args !== null) {
                            sig.args = expr.callee.args.map(ty => {
                                return ty.type === 'Infer'
                                    ? infcx.mkTyVar({ type: 'GenericArg', span: expr.span })
                                    : lowerTy(ty)
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

type MirValue = { type: 'int', ity: IntTy, value: number }
    | { type: 'bool', value: boolean }
    | { type: 'str', value: string }
    | { type: 'Local', value: MirLocalId<true> }
    | { type: 'Unreachable' }
    | { type: 'FnDef', value: FnDecl }
    | { type: 'ExternFnDef', value: ExternFnDecl }
    | { type: 'Record', value: RecordFields<MirValue> }
    | { type: 'Tuple', value: MirValue[] };

const UNIT_MIR: MirValue = { type: 'Tuple', value: [] };

/**
 * `temporary` indicates whether this local is used for a subexpression.
 * These are trivially in SSA form and are never written to except when initialized.
 */
type MirLocal<temporary extends boolean = boolean> = { ty: Ty, temporary: temporary };
type MirLocalId<temporary extends boolean = boolean> = number;
type Projection = { type: 'Field', property: string | number } | { type: 'Index', index: MirValue } | { type: 'Deref' };
type MirPlace<temporary extends boolean = boolean> = { base: MirLocalId<temporary>, projections: Projection[] };
type MirStmt = { type: 'Assignment', assignee: MirPlace, value: MirValue }
    | { type: 'BinOp', op: BinaryOp, assignee: MirLocalId<true>, lhs: MirValue, lhsTy: Ty, rhs: MirValue }
    | { type: 'Unary', op: UnaryOp, assignee: MirLocalId<true>, rhs: MirValue }
    | { type: 'Copy', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'AddrOf', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'Bitcast', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Ext', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Trunc', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'InitArrayLit', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, values: MirValue[] }
    | { type: 'InitArrayRepeat', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, value: MirValue, count: number };
type MirTerminator = { type: 'Return' }
    | { type: 'Call', assignee: MirLocalId<true>, args: MirValue[], decl: FnDecl | ExternFnDecl, sig: InstantiatedFnSig, target: MirBlockId }
    | { type: 'Conditional', condition: MirValue, then: MirBlockId, else: MirBlockId }
    | { type: 'Jump', target: MirBlockId };
type MirBlock = {
    stmts: MirStmt[];
    terminator: MirTerminator | null;
};
type MirBlockId = number;
type MirBody = { blocks: MirBlock[], parameters: MirLocalId<false>[], locals: MirLocal[] };

function mangleTy(ty: Ty): string {
    switch (ty.type) {
        case 'never':
        case 'str':
        case 'bool':
            return ty.type;
        case 'int':
            return (ty.value.signed ? 'i' : 'u') + ty.value.bits;
        case 'Array':
            return `$array$${ty.len}$${mangleTy(ty.elemTy)}`;
        case 'TyParam':
        case 'TyVid':
        case 'FnDef':
        case 'ExternFnDef':
            throw new Error(`attempted to mangle ${ty.type}`);
        case 'Pointer':
            return `$ptr$${ty.mtb}$${mangleTy(ty.pointee)}`;
        case 'Alias': {
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
        }
        case 'Record': todo('mangle record ty');
        case 'Tuple': {
            let out = '$LP$';
            for (let i = 0; i < ty.elements.length; i++) {
                if (i !== 0) out += '$$';
                out += mangleTy(ty.elements[i]);
            }
            out += '$RP$';
            return out;
        }
        default: assertUnreachable(ty);
    }
}
function mangleInstFn(decl: FnDecl, args: Ty[]): string {
    let mangled = decl.sig.name;

    assert(decl.sig.generics.length === args.length, `mismatched generic args when mangling ${decl.sig.name}`);
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
 *    fn f<T>(v: T) {}
 * 
 * calling `astToMir(f, [i32])` will create the MIR body for `function f(v: i32)`, and cache it.
 */
const _mirBodyCache = new Map<string, MirBody>();
function astToMir(src: string, mangledName: string, decl: FnDecl, args: Ty[], resolutions: Resolutions, typeck: TypeckResults): MirBody {
    function lowerMir(): MirBody {
        if (decl.body.type !== 'Block') throw `${decl.sig.name} did not have a block as its body?`;

        const astLocalToMirLocal = new Map<LetDecl | FnParameter, MirLocalId<false>>();
        const locals: MirLocal[] = [];
        const addLocal = <temporary extends boolean = boolean>(ty: Ty, temporary: temporary): MirLocalId<temporary> => {
            ty = instantiateTy(ty, args);
            locals.push({ ty, temporary });
            return locals.length - 1;
        };
        const addBlock = (): MirBlockId => {
            blocks.push({ stmts: [], terminator: null });
            return blocks.length - 1;
        };
        const retTy = decl.sig.ret && typeck.loweredTys.get(decl.sig.ret)!;
        const hasSignificantReturn = retTy && !isUnit(retTy);
        if (hasSignificantReturn) {
            // _0 = return place
            assert(addLocal(retTy, false) === 0);
        }
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
        for (const param of decl.sig.parameters) {
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
        function requireAsPlace(val: ({ type: 'Place' } & MirPlace<boolean>) | MirValue): { type: 'Place' } & MirPlace<boolean> {
            let place = val.type === 'Local'
                ? { type: 'Place', base: val.value, projections: [] } as ({ type: 'Place' } & MirPlace<boolean>)
                : val;

            if (place.type === 'Place') {
                return place;
            } else {
                throw new Error(`place was expected, got ${place.type}`);
            }
        }

        function lowerStmt(stmt: Stmt) {
            switch (stmt.type) {
                case 'FnDecl': break; // Nested bodies are only lowered when explicitly requested
                case 'ExternFnDecl':
                    // Extern fns don't have a body, nothing needs to be lowered
                    // TODO: we might want to at the very least validate intrinsic signatures
                    break;
                case 'LetDecl': {
                    const ty = typeck.exprTys.get(stmt.init)!;
                    const local = addLocal(ty, false);
                    astLocalToMirLocal.set(stmt, local);
                    const value = asValue(lowerExpr(stmt.init), ty);
                    block.stmts.push({ type: 'Assignment', assignee: { base: local, projections: [] }, value });
                    break;
                }
                case 'Expr': lowerExpr(stmt.value); break;
                case 'TyAlias': break;
                default: assertUnreachable(stmt);
            }
        }

        function lowerReturnValue(value: MirValue): MirValue {
            if (hasSignificantReturn) {
                block.stmts.push({ type: 'Assignment', assignee: { base: returnId, projections: [] }, value });
                block.terminator = { type: 'Return' };
            } else {
                block.terminator = { type: 'Return' };
            }
            let newBlock = { stmts: [], terminator: null };
            blocks.push(newBlock);
            block = newBlock;
            return { type: 'Unreachable' };
        }

        type LowerExprResult = MirValue | ({ type: 'Place' } & MirPlace);

        function lowerExpr(expr: Expr): LowerExprResult {
            switch (expr.type) {
                case 'Number': return { type: 'int', ity: expr.suffix, value: expr.value };
                case 'String': return { type: 'str', value: expr.value };
                case 'Literal': {
                    const resolution = resolutions.valueResolutions.get(expr)!;
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
                            return { type: 'Place', base: id, projections: [] };
                        }
                        case 'ExternFnDecl': return { type: 'ExternFnDef', value: resolution };
                        default: assertUnreachable(resolution);
                    }
                }
                case 'Return': {
                    const ret = asValue(lowerExpr(expr.value), typeck.exprTys.get(expr.value)!);
                    return lowerReturnValue(ret);
                }
                case 'Binary': {
                    const lhsTy = typeck.exprTys.get(expr.lhs)!;
                    const lhs = asValue(lowerExpr(expr.lhs), lhsTy);
                    const rhs = asValue(lowerExpr(expr.rhs), typeck.exprTys.get(expr.rhs)!);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'BinOp', assignee: res, lhs, lhsTy, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'Unary': {
                    const rhs = asValue(lowerExpr(expr.rhs), typeck.exprTys.get(expr.rhs)!);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'Unary', assignee: res, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'AddrOf': {
                    const pointee = requireAsPlace(lowerExpr(expr.pointee));
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'AddrOf', assignee: res, place: pointee });
                    return { type: 'Local', value: res };
                }
                case 'Assignment': {
                    let assignee = requireAsPlace(lowerExpr(expr.target));

                    const value = asValue(lowerExpr(expr.value), typeck.exprTys.get(expr.value)!);
                    block.stmts.push({
                        type: 'Assignment',
                        assignee,
                        value
                    });
                    return UNIT_MIR;
                }
                case 'Deref': {
                    let pointee = requireAsPlace(lowerExpr(expr.pointee));
                    pointee.projections.push({ type: 'Deref' });
                    return pointee;
                }
                case 'FnCall': {
                    function instantiateFnSig(sig: InstantiatedFnSig, args: Ty[]): InstantiatedFnSig {
                        return {
                            args: sig.args.map(ty => instantiateTy(ty, args)),
                            parameters: sig.parameters.map(ty => instantiateTy(ty, args)),
                            ret: instantiateTy(sig.ret, args)
                        }
                    }
                    const sig = instantiateFnSig(typeck.instantiatedFnSigs.get(expr)!, args);

                    // calls to intrinsics are special cased
                    if (expr.callee.type === 'Literal') {
                        const res = resolutions.valueResolutions.get(expr.callee)!;
                        if (res.type === 'ExternFnDecl' && res.abi === 'intrinsic') {
                            const transmutableIntrinsic = (type: 'Bitcast' | 'Ext' | 'Trunc'): LowerExprResult => {
                                const fromTy = instantiateTy(sig.parameters[0], args);
                                const toTy = instantiateTy(sig.ret, args);
                                const assignee = addLocal(toTy, true);
                                const value = asValue(lowerExpr(expr.args[0]), fromTy);

                                block.stmts.push({ type, assignee, from_ty: fromTy, to_ty: toTy, value });
                                return { type: 'Local', value: assignee };
                            }

                            switch (res.sig.name) {
                                case 'bitcast': return transmutableIntrinsic('Bitcast');
                                case 'ext': return transmutableIntrinsic('Ext');
                                case 'trunc': return transmutableIntrinsic('Trunc');
                                default: throw new Error(`unknown intrinsic: ${res.sig.name}`);
                            }
                        }
                    }

                    const callee = lowerExpr(expr.callee);
                    if (callee.type !== 'FnDef' && callee.type !== 'ExternFnDef') {
                        throw new Error('callee must be a FnDef or ExternFnDef');
                    }
                    const res = addLocal(sig.ret, true);

                    const callArgs = expr.args.map(v => asValue(lowerExpr(v), typeck.exprTys.get(v)!));

                    const targetBlock = blocks.length;
                    blocks.push({ stmts: [], terminator: null });

                    block.terminator = { type: 'Call', args: callArgs, assignee: res, decl: callee.value, sig, target: targetBlock };
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
                case 'Index': {
                    const target = requireAsPlace(lowerExpr(expr.target));
                    const index = asValue(lowerExpr(expr.index), typeck.exprTys.get(expr.index)!);
                    target.projections.push({ type: 'Index', index });
                    return target;
                }
                case 'ArrayLiteral':
                case 'ArrayRepeat': {
                    const exprTy = typeck.exprTys.get(expr)!;
                    if (exprTy.type !== 'Array') {
                        throw new Error('array literal did not produce array type');
                    }

                    const assignee = addLocal(exprTy, true);
                    if (expr.type === 'ArrayLiteral') {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayLit',
                            ty: exprTy,
                            values: expr.elements.map(e => asValue(lowerExpr(e), typeck.exprTys.get(e)!))
                        });
                    } else {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayRepeat',
                            ty: exprTy,
                            count: expr.count,
                            value: asValue(lowerExpr(expr.element), typeck.exprTys.get(expr.element)!)
                        });
                    }
                    return { type: 'Local', value: assignee };
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
                case 'Bool': return { type: 'bool', value: expr.value };
                case 'If': {
                    const condition = asValue(lowerExpr(expr.condition), BOOL);
                    const joinedBlock = addBlock();
                    const thenBlock = addBlock();
                    block.terminator = { type: 'Conditional', else: joinedBlock, then: thenBlock, condition };

                    block = blocks[thenBlock];
                    lowerExpr(expr.then);
                    block.terminator = { type: 'Jump', target: joinedBlock };

                    block = blocks[joinedBlock];
                    return UNIT_MIR;
                }
                case 'While':
                    const conditionBlock = addBlock();
                    const bodyBlock = addBlock();
                    const joinedBlock = addBlock();
                    block.terminator = { type: 'Jump', target: conditionBlock };
                    block = blocks[conditionBlock];

                    const condition = asValue(lowerExpr(expr.condition), BOOL);
                    block.terminator = { type: 'Conditional', condition, then: bodyBlock, else: joinedBlock };

                    block = blocks[bodyBlock];
                    lowerExpr(expr.body);
                    block.terminator = { type: 'Jump', target: conditionBlock };

                    block = blocks[joinedBlock];
                    return UNIT_MIR;
                case 'Block': {
                    for (const stmt of expr.stmts) {
                        lowerStmt(stmt);
                    }
                    return UNIT_MIR;
                }
                case 'Tuple': {
                    const elements: MirValue[] = expr.elements.map(expr => {
                        return asValue(lowerExpr(expr), typeck.exprTys.get(expr)!);
                    });
                    return { type: 'Tuple', value: elements };
                }
                default: assertUnreachable(expr);
            }
        }

        for (const stmt of decl.body.stmts) {
            lowerStmt(stmt);
        }

        if (!hasSignificantReturn) {
            // append implicit `ret void` statement for default return fns
            assert(block.terminator === null);
            lowerReturnValue(UNIT_MIR);
        }

        return {
            locals,
            blocks,
            parameters,
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
    const _externDeclarations = new Set<string>();
    let declareSection = '';
    const addExternDecl = (name: string, mkSig: () => string) => {
        if (!_externDeclarations.has(name)) {
            _externDeclarations.add(name);
            declareSection += mkSig();
        }
    };
    let fnSection = '';
    let constSection = '';
    let constCount = 0;
    let nextConstId = () => `@ct.${constCount++}`;

    function llTy(ty: Ty): string {
        switch (ty.type) {
            case 'bool': return 'i1';
            case 'int': return `i${ty.value.bits}`;
            case 'str': throw new Error('cannot directly lower str type');
            case 'Pointer':
                if (ty.pointee.type === 'str') {
                    return '{i8*, i64}';
                } else {
                    return `${llTy(ty.pointee)}*`;
                }
            case 'ExternFnDef': throw new Error('extern fn in llir lowering');
            case 'TyParam': throw new Error('uninstantiated type parameter in llir lowering');
            case 'Array':
                return `[${ty.len} x ${llTy(ty.elemTy)}]`;
            case 'FnDef':
                todo(ty.type);
            case 'Alias':
                return llTy(normalize(ty));
            case 'Record': return '{' + ty.fields.map(v => llTy(v[1])).join(', ') + '}';
            case 'Tuple': return '{' + ty.elements.map(llTy).join(', ') + '}';
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
            case 'int': return `i${val.ity.bits}`;
            case 'str': return '{i8*, i64}';
            case 'bool': return 'i1';
            case 'Unreachable': todo('unreachable ty');
            case 'FnDef':
            case 'ExternFnDef': throw new Error(val.type + ' values need to be treated specially');
            case 'Record': return '{' + val.value.map(v => llValTy(mir, v[1])).join(', ') + '}';
            case 'Tuple': return '{' + val.value.map(v => llValTy(mir, v)).join(', ') + '}';
        }
    }

    function codegenFn(decl: FnDecl, args: Ty[]) {
        function inner(decl: FnDecl, args: Ty[]) {

            let _temps = 0;
            let tempLocal = () => _temps++;
            let tempBlock = tempLocal;
            const mir = astToMir(src, mangledName, decl, args, res, typeck);

            const getLocal = <temporary extends boolean>(id: MirLocalId<temporary>): MirLocal<temporary> => {
                return mirLocal(mir, id);
            };

            const parameterList = mir.parameters.map((id) => `${llTy(getLocal(id).ty)} %lt.${id}`).join(', ');
            const rawRetTy = decl.sig.ret ? typeck.loweredTys.get(decl.sig.ret)! : UNIT;
            // only "significant" (= non-unit) types get a return place
            const retTy = !isUnit(rawRetTy) ? mir.locals[0].ty : UNIT;

            let output = `define ${isUnit(retTy) ? 'void' : llTy(retTy)} @${mangledName}(${parameterList}) {\n`;

            function compileValueToLocal(val: MirValue): string {
                switch (val.type) {
                    case 'Local': return `%l.${val.value}`;
                    case 'int':
                    case 'bool': return val.value.toString();
                    case 'str':
                        const ctId = nextConstId();
                        const ctTy = `[${val.value.length} x i8]`;
                        constSection += `${ctId} = private constant ${ctTy} c"${val.value}"\n`;
                        return `{i8* bitcast(${ctTy}* ${ctId} to i8*), i64 ${val.value.length}}`;
                    case 'Unreachable': return 'poison';
                    case 'FnDef':
                    case 'ExternFnDef': throw new Error(val.type + ' values need to be treated specially');
                    case 'Record':
                    case 'Tuple': {
                        // in the codegen stage, records and tuples are almost identical, so we can largely handle them the same here...
                        //
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
                            const valueS = compileValueToLocal(
                                val.type === 'Record' ?
                                    val.value[i][1]
                                    : val.value[i]
                            );
                            const valTyS = llValTy(
                                mir,
                                val.type === 'Record'
                                    ? val.value[i][1]
                                    : val.value[i]
                            );
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

            function compilePlaceExpr(place: MirPlace): { finalTy: Ty, finalLocal: string } {
                const rawBase = mir.locals[place.base];

                let finalLocal: string;
                let finalTy = normalize(rawBase.ty);
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
                    output += `${baseId} = alloca ${llTy(finalTy)}\n`;
                    output += `store ${llTy(finalTy)} %l.${place.base}, ${llTy(finalTy)}* ${baseId}\n`;
                    finalLocal = baseId;
                } else {
                    // If it's not a temporary, then the base is most likely a local variable.
                    // In any case, `temporary = false` means that it must be alloca'd, so there is no need to do the above,
                    // as we already have a pointer that we can GEP into.
                    finalLocal = `%l.${place.base}`;
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

                for (const projection of place.projections) {
                    const oldBase = finalLocal;
                    const oldTy = finalTy;
                    const oldTyS = llTy(oldTy);
                    finalLocal = `%t.${tempLocal()}`;
                    switch (projection.type) {
                        case 'Field': {
                            let projectedIndex: number;
                            switch (oldTy.type) {
                                case 'Record':
                                    projectedIndex = oldTy.fields.findIndex(v => v[0] === projection.property);
                                    finalTy = normalize(oldTy.fields[projectedIndex][1]);
                                    break;
                                case 'Tuple':
                                    if (typeof projection.property !== 'number') {
                                        throw new Error('non-numeric projection on tuple');
                                    }
                                    projectedIndex = projection.property;
                                    finalTy = normalize(oldTy.elements[projectedIndex]);
                                    break;
                                default:
                                    throw new Error('projection target must be a record or tuple type');
                            }

                            output += `${finalLocal} = getelementptr ${oldTyS}, ${oldTyS}* ${oldBase}, i32 0, i32 ${projectedIndex}\n`;
                            break;
                        }
                        case 'Deref': {
                            output += `${finalLocal} = load ${oldTyS}, ${oldTyS}* ${oldBase}\n`;
                            if (oldTy.type !== 'Pointer') throw new Error('dereferencing non-ptr');
                            finalTy = normalize(oldTy.pointee);
                            break;
                        }
                        case 'Index': {
                            if (finalTy.type !== 'Array') {
                                throw new Error('index target must be an array');
                            }
                            const index = compileValueToLocal(projection.index);
                            // TODO: bounds checks
                            output += `${finalLocal} = getelementptr ${oldTyS}, ${oldTyS}* ${oldBase}, i32 0, i32 ${index}\n`;
                            finalTy = finalTy.elemTy;
                            break;
                        }
                        default: assertUnreachable(projection);
                    }
                }

                return { finalTy, finalLocal };
            }

            function compileTemporaryLoop(
                preLoop: () => void,
                header: () => string /* local of the i1 condition */,
                body: () => void,
            ) {
                const headerBlock = `bt.${tempBlock()}`;
                const bodyBlock = `bt.${tempBlock()}`;
                const exitBlock = `bt.${tempBlock()}`;
                preLoop();

                output += `br label %${headerBlock}\n`;
                output += `${headerBlock}:\n`;
                const conditionLocal = header();
                output += `br i1 ${conditionLocal}, label %${bodyBlock}, label %${exitBlock}\n`;

                output += `${bodyBlock}:\n`;
                body();
                output += `br label %${headerBlock}\n`
                output += `${exitBlock}:\n`;
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
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.assignee);
                            const valS = compileValueToLocal(stmt.value);
                            output += `store ${llValTy(mir, stmt.value)} ${valS}, ${llTy(finalTy)}* ${finalLocal}\n`;
                            break;
                        }
                        case 'BinOp': {
                            let signed = stmt.lhsTy.type === 'int' && stmt.lhsTy.value.signed;
                            let binOp: string;
                            switch (stmt.op) {
                                case TokenType.Plus: binOp = 'add'; break;
                                case TokenType.Minus: binOp = 'sub'; break;
                                case TokenType.Star: binOp = 'mul'; break;
                                case TokenType.Slash: binOp = signed ? 'sdiv' : 'udiv'; break;
                                case TokenType.Percent: binOp = signed ? 'srem' : 'urem'; break;
                                case TokenType.Lt: binOp = 'icmp ' + (signed ? 'slt' : 'ult'); break;
                                case TokenType.Le: binOp = 'icmp ' + (signed ? 'sle' : 'ule'); break;
                                case TokenType.Gt: binOp = 'icmp ' + (signed ? 'sgt' : 'ugt'); break;
                                case TokenType.Ge: binOp = 'icmp ' + (signed ? 'sge' : 'uge'); break;
                                case TokenType.EqEq: binOp = 'icmp eq'; break;
                                case TokenType.NotEq: binOp = 'icmp ne'; break;
                                default: assertUnreachable(stmt);
                            }
                            const lhsS = compileValueToLocal(stmt.lhs);
                            const rhsS = compileValueToLocal(stmt.rhs);
                            output += `%l.${stmt.assignee} = ${binOp} ${llValTy(mir, stmt.lhs)} ${lhsS}, ${rhsS}\n`;
                            break;
                        }
                        case 'Copy': {
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.place);
                            output += `%l.${stmt.assignee} = load ${llTy(finalTy)}, ${llTy(finalTy)}* ${finalLocal}\n`;
                            break;
                        }
                        case 'AddrOf': {
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.place);
                            // Since we already compile place expressions to GEPs and `finalLocal` already is the pointer that we need,
                            // simply emit an identity bitcast
                            output += `%l.${stmt.assignee} = bitcast ${llTy(finalTy)}* ${finalLocal} to ${llTy(finalTy)}*\n`;
                            break;
                        }
                        case 'Bitcast':
                            // compile bitcast<i64, i8*>(0) to
                            //
                            // %tmp = alloca i64
                            // store i64 0, i64* %tmp
                            // %tmp.1 = bitcast i64* %tmp to i8**
                            // %res = load i8*, i8** %tmp.1
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const castSource = compileValueToLocal(stmt.value);
                            const castSourcePtr = `%t.${tempLocal()}`;
                            output += `${castSourcePtr} = alloca ${fromTyS}\n`;
                            output += `store ${fromTyS} ${castSource}, ${fromTyS}* ${castSourcePtr}\n`;
                            const bitcastPtr = `%t.${tempLocal()}`;
                            output += `${bitcastPtr} = bitcast ${fromTyS}* ${castSourcePtr} to ${toTyS}*\n`;
                            output += `%l.${stmt.assignee} = load ${toTyS}, ${toTyS}* ${bitcastPtr}\n`;
                            break
                        case 'Unary':
                            switch (stmt.op) {
                                case TokenType.Not:
                                    const rhs = compileValueToLocal(stmt.rhs);
                                    output += `%l.${stmt.assignee} = xor i1 ${rhs}, true\n`
                                    break;
                                default: assertUnreachable(stmt);
                            }
                            break;
                        case 'Ext': {
                            if (stmt.from_ty.type !== 'int' || stmt.to_ty.type !== 'int') {
                                throw new Error('ext intrinsic only works on int types');
                            }
                            let instruction = stmt.from_ty.value.signed ? 'sext' : 'zext';
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const valueS = compileValueToLocal(stmt.value);
                            output += `%l.${stmt.assignee} = ${instruction} ${fromTyS} ${valueS} to ${toTyS}\n`;
                            break;
                        }
                        case 'Trunc': {
                            if (stmt.from_ty.type !== 'int' || stmt.to_ty.type !== 'int') {
                                throw new Error('trunc intrinsic only works on int types');
                            }
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const valueS = compileValueToLocal(stmt.value);
                            output += `%l.${stmt.assignee} = trunc ${fromTyS} ${valueS} to ${toTyS}\n`;
                            break;
                        }
                        case 'InitArrayRepeat': {
                            const arrayLocal = `%t.${tempLocal()}`;
                            const counterLocal = `%t.${tempLocal()}`;
                            const arrayTyS = llTy(stmt.ty);
                            const valTyS = llTy(stmt.ty.elemTy);
                            const count = stmt.count;
                            const value = compileValueToLocal(stmt.value);

                            // TODO: we can special case with a memset for {i,u}8-32; it accepts up to an int
                            // For now, just generate a loop that initializes each element.
                            compileTemporaryLoop(
                                () => {
                                    output += `${arrayLocal} = alloca ${arrayTyS}\n`
                                    output += `${counterLocal} = alloca i32\n`;
                                },
                                () => {
                                    const loadTemp = `%t.${tempLocal()}`;
                                    const conditionTemp = `%t.${tempLocal()}`;
                                    output += `${loadTemp} = load i32, i32* ${counterLocal}\n`
                                    output += `${conditionTemp} = icmp ult i32 ${loadTemp}, ${count}\n`;
                                    return conditionTemp;
                                },
                                () => {
                                    const ptrLocal = `%t.${tempLocal()}`;
                                    const curCounterLocal = `%t.${tempLocal()}`;
                                    const addLocal = `%t.${tempLocal()}`;
                                    output += `${curCounterLocal} = load i32, i32* ${counterLocal}\n`
                                    output += `${ptrLocal} = getelementptr ${arrayTyS}, ${arrayTyS}* ${arrayLocal}, i32 0, i32 ${curCounterLocal}\n`;
                                    output += `store ${valTyS} ${value}, ${valTyS}* ${ptrLocal}\n`;
                                    output += `${addLocal} = add i32 ${curCounterLocal}, 1\n`;
                                    output += `store i32 ${addLocal}, i32* ${counterLocal}\n`;
                                },
                            );

                            // Array local is fully initialized. Finally, load it.
                            output += `%l.${stmt.assignee} = load ${arrayTyS}, ${arrayTyS}* ${arrayLocal}\n`;

                            break;
                        }
                        case 'InitArrayLit': {
                            const arrayLocal = `%t.${tempLocal()}`;
                            const arrayTyS = llTy(stmt.ty);
                            const valTyS = llTy(stmt.ty.elemTy);
                            output += `${arrayLocal} = alloca ${arrayTyS}\n`;
                            for (let i = 0; i < stmt.values.length; i++) {
                                const val = compileValueToLocal(stmt.values[i]);
                                const ptrLocal = `%t.${tempLocal()}`;
                                output += `${ptrLocal} = getelementptr ${arrayTyS}, ${arrayTyS}* ${arrayLocal}, i32 0, i32 ${i}\n`;
                                output += `store ${valTyS} ${val}, ${valTyS}* ${ptrLocal}\n`;
                            }
                            output += `%l.${stmt.assignee} = load ${arrayTyS}, ${arrayTyS}* ${arrayLocal}\n`;
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
                            if (isUnit(retTy)) {
                                output += 'ret void\n';
                            } else {
                                const tyS = llTy(retTy);
                                const temp = tempLocal();
                                output += `%ret.${temp} = load ${tyS}, ${tyS}* %l.0\n`;
                                output += `ret ${tyS} %ret.${temp}\n`;
                            }
                            break;
                        case 'Call':
                            const parameterList = terminator.sig.parameters.map((ty) => llTy(ty)).join(', ');
                            let mangledName: string;
                            switch (terminator.decl.type) {
                                case 'FnDecl': {
                                    const calleeMangled = mangleInstFn(terminator.decl, terminator.sig.args);
                                    codegenFn(terminator.decl, terminator.sig.args);
                                    // NB: don't write to `output` here before the `argList` mapping, since that may compile values
                                    mangledName = calleeMangled;
                                    break;
                                }
                                case 'ExternFnDecl': {
                                    addExternDecl(terminator.decl.sig.name, () => {
                                        const ret = returnTy(terminator.decl.sig, typeck)!;
                                        return `declare ${isUnit(ret) ? 'void' : llTy(ret)} @${terminator.decl.sig.name}(${parameterList})\n`;
                                    });
                                    mangledName = terminator.decl.sig.name;
                                    break;
                                }
                                default: assertUnreachable(terminator.decl);
                            }

                            const argList = terminator.args.map(arg => `${llValTy(mir, arg)} ${compileValueToLocal(arg)}`).join(', ');
                            if (isUnit(terminator.sig.ret)) {
                                // Annoying hack: we generally codegen functions that return unit as `void()*`, however
                                // we also generally treat ZSTs as equivalent to `{}` and old versions of LLVM error on
                                // `call {} @fnThatReturnsVoid()`.
                                // So just bitcast void()* to {}()*
                                output += `%l.${terminator.assignee} = call {} bitcast(void(${parameterList})* @${mangledName} to {}(${parameterList})*)(${argList})\n`;
                            } else {
                                output += `%l.${terminator.assignee} = call ${llTy(terminator.sig.ret)} @${mangledName}(${argList})\n`;
                            }
                            output += `br label %bb.${terminator.target}\n`;
                            break;
                        case 'Conditional': {
                            const condition = compileValueToLocal(terminator.condition);
                            output += `br i1 ${condition}, label %bb.${terminator.then}, label %bb.${terminator.else}\n`
                            break;
                        }
                        case 'Jump': {
                            output += `br label %bb.${terminator.target}\n`;
                            break;
                        }
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
    return declareSection + '\n' + constSection + '\n' + fnSection;
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

(function () {
    const src = fs.readFileSync(options.path, 'utf8');
    const ast = timed('parse', () => parse(src));
    const resolutions = timed('name res', () => computeResolutions(ast));
    const tyres = timed('typeck', () => typeck(src, ast, resolutions));
    if (options.verbose) {
        tyres.exprTys.forEach((v, k) => console.log(`expr @ ${ppSpan(src, k.span)} => ${ppTy(v)}`));
        console.log();
    }
    if (tyres.hadErrors) {
        return;
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
})();
