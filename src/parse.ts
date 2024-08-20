import * as path from 'path';
import { SourceMap, File, Span, joinSpan, ppSpan, addFileToSourceMap, spanFromFile } from "./span";
import { TokenType, tokenCanContinuePattern } from "./token";
import { tokenize } from "./tokenize";
import { I16, I32, I64, I8, IntTy, Ty, U16, U32, U64, U8 } from "./ty";
import { assert } from './util';
import { bug, err } from './error';

export type BinaryOp =
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
    | TokenType.Percent
    | TokenType.AndAnd
    | TokenType.OrOr;

export type UnaryOp = TokenType.Not | TokenType.Minus;;

export type AssignmentKind = TokenType.Assign
    | TokenType.AddAssign
    | TokenType.SubAssign
    | TokenType.MulAssign
    | TokenType.DivAssign
    | TokenType.RemAssign;

export type Expr = { span: Span } & (
    | { type: "Block"; stmts: Stmt[], tailExpr: Expr | null }
    | { type: "Path"; path: Path<AstTy> }
    | { type: "FnCall"; args: Expr[]; callee: Expr }
    | { type: "Index"; target: Expr; index: Expr }
    | { type: "ArrayLiteral"; elements: Expr[] }
    | { type: "ArrayRepeat"; element: Expr; count: number }
    | { type: "Number"; value: number; suffix: IntTy | null }
    | { type: "Bool"; value: boolean }
    | { type: "String"; value: string }
    | { type: 'ByteCharacter', value: string }
    | { type: "Assignment"; op: AssignmentKind, target: Expr; value: Expr }
    | { type: "Property"; deref: boolean /* target*.prop */, target: Expr; property: string | number }
    | { type: "MethodCall", deref: boolean /* recv*.prop(); */, target: Expr, path: PathSegment<AstTy>, args: Expr[] }
    | { type: "Return"; value: Expr }
    | { type: 'Break' }
    | { type: 'Continue' }
    | { type: 'Match', scrutinee: Expr, arms: AstArm[] }
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
    | { type: "If"; condition: Expr; then: { type: 'Block' } & Expr; else: ({ type: 'If' | 'Block' } & Expr) | null }
    | { type: "While"; condition: Expr; body: Expr }
    | { type: "Tuple", elements: Expr[] }
);

export type LetDecl = { type: 'LetDecl', name: string, ty: AstTy | null, init: Expr | null };

export type AstFnSignature = {
    name: string,
    generics: Generics,
    parameters: FnParameter[],
    ret?: AstTy,
};
export type FnDecl = {
    type: 'FnDecl',
    sig: AstFnSignature,
    body: Expr,
    parent: Impl | null
};
export type ExternFnDecl = {
    type: 'ExternFnDecl'
    abi: 'C' | 'intrinsic',
    sig: AstFnSignature
};
export type FnParameter = { type: 'Receiver', ptr: Mutability | null } | { type: 'Parameter', name: string, ty: AstTy };
export type Generics = string[];
export type TyAliasDecl = { type: 'TyAlias', name: string, generics: Generics, constructibleIn: Path<AstTy>[], alias: AstTy };
export type GenericArg<Ty> = { type: 'Type', ty: Ty };
export type PathSegment<Ty> = { ident: string; args: GenericArg<Ty>[] };
export type Path<Ty> = { segments: PathSegment<Ty>[] };
export type ImplItem = {
    type: 'Fn',
    decl: FnDecl,
};
export type Impl = {
    type: 'Impl',
    selfTy: AstTy,
    // stores an `AstTy` only so we can store it as a key in the resolver's tyMap
    ofTrait: ({ type: 'Path' } & AstTy) | null,
    generics: Generics,
    items: ImplItem[]
};
export type ModType = 'Outlined' | 'Inline';
export type Mod = {
    type: 'Mod',
    modType: ModType
    name: string,
    items: Stmt[]
};
export type TraitItem = { type: 'Fn', sig: AstFnSignature };
export type Trait = {
    type: 'Trait',
    name: string,
    items: TraitItem[]
};
// `use x as y` => `{path: "x", alias: "y"}`
// `use x::y` => `{path: "x::y", alias: null}`
export type UseDecl = { type: 'Use', path: Path<never>, alias: string | null };
export type Stmt = { span: Span } & (
    | { type: 'Expr', value: Expr }
    | LetDecl
    | FnDecl
    | TyAliasDecl
    | ExternFnDecl
    | UseDecl
    | Impl
    | Mod
    | Trait
);
export type Mutability = 'imm' | 'mut';
export type RecordFields<Ty> = ([string, Ty])[];
export type AstVariant = { name: string };
export type AstEnum = { type: 'Enum', name: string, variants: AstVariant[] };
export type VariantId = number;
export type AstTy = { span: Span } & ({ type: 'Path', value: Path<AstTy> }
    | { type: 'Array', elemTy: AstTy, len: number }
    | { type: 'Tuple', elements: AstTy[] }
    | { type: 'Pointer', mtb: Mutability, pointeeTy: AstTy }
    | { type: 'Record', fields: RecordFields<AstTy> }
    | AstEnum
    | { type: 'Alias', alias: AstTy, constructibleIn: Path<never>[] }
    | { type: 'Infer' });
export type Module = { stmts: Stmt[] };
export type LeftToRight = 'ltr';
export type RightToLeft = 'rtl';
export type Associativity = LeftToRight | RightToLeft;


// #[key (= value)?]
export type Attribute = {
    key: string,
    value?: Expr
};

export type Pat = { span: Span } & (
    | { type: 'Number', value: number }
    | { type: 'String', value: string }
    | { type: 'Path', path: Path<AstTy> }
    // pat..
    | { type: 'RangeFrom', from: Pat }
    // ..pat
    | { type: 'RangeTo', to: Pat }
    // pat..pat
    | { type: 'Range', from: Pat, to: Pat }
);

export type AstArm = { pat: Pat, body: Expr };

export function genericsOfDecl(decl: FnDecl | TyAliasDecl | ExternFnDecl | Impl | Trait): Generics {
    switch (decl.type) {
        case 'TyAlias':
        case 'Impl':
            return decl.generics;
        case 'ExternFnDecl':
        case 'FnDecl':
            return decl.sig.generics;
        case 'Trait': return [];
    }
}

const UNARY_PRECEDENCE: { [index: string]: number | undefined } = {
    // Somewhere between indexing/dot and multiplicative
    [TokenType.And]: 15,
    [TokenType.Star]: 15,
    [TokenType.Not]: 15,
    [TokenType.Minus]: 15,
    [TokenType.DotDot]: 7,
};

// Patterns and expressions share the same precedence for symbols in here
const BINARY_INFIX_PRECEDENCE: { [index: string]: number | undefined } = {
    // Fn calls `x()`
    [TokenType.LParen]: 17,
    // Indexing `x[y]`
    [TokenType.LSquare]: 17,
    [TokenType.Dot]: 17,
    [TokenType.StarDot]: 17,
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
    // Ranges
    [TokenType.DotDot]: 7,
    [TokenType.AndAnd]: 6,
    [TokenType.OrOr]: 5,
    // Assignment x = y
    [TokenType.Assign]: 2,
    [TokenType.AddAssign]: 2,
    [TokenType.SubAssign]: 2,
    [TokenType.MulAssign]: 2,
    [TokenType.DivAssign]: 2,
    [TokenType.RemAssign]: 2,
};
const ASSOC: { [index: string]: Associativity | undefined } = {
    [TokenType.LParen]: 'ltr',
    [TokenType.Dot]: 'ltr',
    [TokenType.LSquare]: 'ltr',
    [TokenType.StarDot]: 'ltr',
    [TokenType.Assign]: 'rtl',
    [TokenType.AddAssign]: 'rtl',
    [TokenType.SubAssign]: 'rtl',
    [TokenType.MulAssign]: 'rtl',
    [TokenType.DivAssign]: 'rtl',
    [TokenType.RemAssign]: 'rtl',
    [TokenType.Plus]: 'ltr',
    [TokenType.Minus]: 'ltr',
    [TokenType.Star]: 'ltr',
    [TokenType.Slash]: 'ltr',
    [TokenType.Percent]: 'ltr',
    [TokenType.DotDot]: 'ltr',
    [TokenType.Not]: 'ltr',
    [TokenType.Lt]: 'ltr',
    [TokenType.Le]: 'ltr',
    [TokenType.Gt]: 'ltr',
    [TokenType.Ge]: 'ltr',
    [TokenType.EqEq]: 'ltr',
    [TokenType.NotEq]: 'ltr',
    [TokenType.AndAnd]: 'ltr',
    [TokenType.OrOr]: 'ltr',
};

function isBlockLike(expr: Expr): boolean {
    return expr.type === 'Block'
        || expr.type === 'If'
        || expr.type === 'Match'
        || expr.type === 'While';
}

enum ParseContext {
    Statement,
    Subexpression
}

export type AttrMap = Map<Stmt, Attribute[]>;

export function parse(sm: SourceMap, attrs: AttrMap, file: File): Module {
    const tokens = tokenize(sm, file);
    const stmts: Stmt[] = [];
    let i = 0;
    // When parsing the `#[path]` attribute, assign its value to this variable so it can be accessed in `parseStmt`
    // so that `mod` parsing can access it
    let currentPathAttr: string | null = null;

    function snip(span: Span) {
        return sm.source.substring(span[0], span[1]);
    }

    function expectIdent() {
        const ident = tokens[i++];
        if (ident.ty !== TokenType.Ident) {
            err(tokens[i - 1].span, 'expected ident, got ' + TokenType[ident.ty]);
        }
        return snip(ident.span);
    }

    function eatToken(ty: TokenType, error = true) {
        const tok = tokens[i];
        if (tok?.ty === ty) {
            i++;
            return true;
        } else if (error) {
            err(tok.span, `expected ${TokenType[ty]}, got ${TokenType[tok.ty]}`);
        } else {
            return false;
        }
    }

    function parseAttributes(): Attribute[] {
        const attrs: Attribute[] = [];

        while (eatToken(TokenType.Hash, false)) {
            eatToken(TokenType.LSquare);
            const key = expectIdent();
            let value: Expr | undefined = undefined;
            if (eatToken(TokenType.Assign, false)) {
                value = parseRootStmtExpr();
            }
            attrs.push({ key, value });
            eatToken(TokenType.RSquare);
        }

        return attrs;
    }

    function parseRootPat(): Pat {
        return parsePat(-1);
    }

    function parsePat(minPrecedence: number): Pat {
        let pat: Pat;
        const unaryStartSpan = tokens[i].span;
        switch (tokens[i].ty) {
            case TokenType.LParen: {
                const innerPat = parseRootPat();
                // TODO: tuple pattern
                eatToken(TokenType.RParen);
                pat = innerPat;
            }
            case TokenType.DotDot: {
                const to = parsePat(UNARY_PRECEDENCE[TokenType.DotDot]!);
                pat = { type: 'RangeTo', to, span: joinSpan(unaryStartSpan, to.span) };
                break;
            }
            default:
                pat = parseBottomPat();
        }

        while (i < tokens.length) {
            const op = tokens[i];
            const prec = BINARY_INFIX_PRECEDENCE[op.ty];
            const assoc = ASSOC[op.ty];
            if (prec === undefined || assoc === undefined) {
                return pat;
            }

            if (minPrecedence >= prec && !(minPrecedence === prec && assoc === 'rtl')) break;

            switch (op.ty) {
                case TokenType.DotDot: {
                    i++;
                    if (tokenCanContinuePattern(tokens[i].ty)) {
                        // full range
                        const to = parsePat(prec);
                        pat = { type: 'Range', from: pat, to, span: joinSpan(pat.span, to.span) };
                    } else {
                        // fromRange..
                        pat = { type: 'RangeFrom', from: pat, span: joinSpan(pat.span, op.span) };
                    }
                    break;
                }
                default: bug(op.span, `unknown binary/infix operator for pattern: ${op}`);
            }
        }

        return pat;
    }

    function parseBottomPat(): Pat {
        // NOTE: keep token.ts/tokenCanContinuePattern in sync with this
        const expr = parseBottomExpr();
        switch (expr.type) {
            case 'Number': return { type: 'Number', value: expr.value, span: expr.span };
            case 'String': return { type: 'String', value: expr.value, span: expr.span };
            case 'Path': return { type: 'Path', path: expr.path, span: expr.span };
            default: err(expr.span, `${expr.type} cannot be used in pattern position`);
        }
    }

    function parseTyPath<Ty>(reifySegment: (_: PathSegment<AstTy>) => PathSegment<Ty>): Path<Ty> {
        const eatDoubleColon = () => {
            if (tokens[i].ty === TokenType.Colon && tokens[i + 1].ty === TokenType.Colon) {
                i += 2;
                return true;
            } else {
                return false;
            }
        }

        const segments: PathSegment<Ty>[] = [];
        do {
            const ident = expectIdent();
            const args: GenericArg<AstTy>[] = [];
            if (eatToken(TokenType.Lt, false)) {
                while (!eatToken(TokenType.Gt, false)) {
                    eatToken(TokenType.Comma, false);
                    args.push({ type: 'Type', ty: parseTy() });
                }
            }
            segments.push(reifySegment({ ident, args }));
        } while (eatDoubleColon());

        return { segments };
    }

    let aliasTyName: string | null = null;
    function parseTy(): AstTy {
        // We only allow `type X = enum {}`, i.e. the enum must be the direct aliased type, so reset it here.
        let enclosingAlias = aliasTyName;
        aliasTyName = null;

        let ty: AstTy;
        switch (tokens[i].ty) {
            case TokenType.Ident: {
                const startSpan = tokens[i].span;
                ty = { type: 'Path', value: parseTyPath(x => x), span: joinSpan(startSpan, tokens[i].span) };
                break;
            }
            case TokenType.LBrace: {
                const lbraceSpan = tokens[i++].span;
                const fields: RecordFields<AstTy> = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    eatToken(TokenType.Comma, false);
                    const key = expectIdent();
                    eatToken(TokenType.Colon, true);
                    const value = parseTy();
                    fields.push([key, value]);
                }
                ty = { type: 'Record', fields, span: joinSpan(lbraceSpan, tokens[i].span) };
                break;
            }
            case TokenType.LParen: {
                const lparenSpan = tokens[i++].span;
                if (eatToken(TokenType.RParen, false)) {
                    // Empty tuple type.
                    ty = { type: 'Tuple', elements: [], span: joinSpan(lparenSpan, tokens[i].span) };
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
                    ty = { type: 'Tuple', elements, span: joinSpan(lparenSpan, tokens[i].span) };
                }
                break;
            }
            case TokenType.Underscore: i++; return { type: 'Infer', span: tokens[i - 1].span };
            case TokenType.Enum:
                const startSpan = tokens[i++].span;
                let name: string | null = null;
                if (tokens[i].ty === TokenType.Ident) {
                    name = snip(tokens[i++].span);
                } else if (enclosingAlias !== null) {
                    name = enclosingAlias;
                } else {
                    err(tokens[i].span, 'anonymous enum must be a direct alias');
                }

                eatToken(TokenType.LBrace);
                const variants: AstVariant[] = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    if (variants.length > 0) eatToken(TokenType.Comma);
                    variants.push({ name: expectIdent() });
                }
                ty = { type: 'Enum', name, variants, span: joinSpan(startSpan, tokens[i].span) };
                break;
            default: err(tokens[i].span, 'unknown token for ty: ' + TokenType[tokens[i].ty]);
        }

        while (i < tokens.length) {
            if (eatToken(TokenType.LSquare, false)) {
                const len = tokens[i++];
                if (len.ty !== TokenType.Number) err(tokens[i - 1].span, 'array must have a length component');
                eatToken(TokenType.RSquare, true);
                ty = { type: 'Array', elemTy: ty, len: +snip(len.span), span: joinSpan(ty.span, tokens[i].span) };
            } else if (eatToken(TokenType.Star, false)) {
                const mtb: Mutability = tokens[i].ty === TokenType.Mut ? (i++, 'mut') : 'imm';
                ty = { type: 'Pointer', mtb, pointeeTy: ty, span: joinSpan(ty.span, tokens[i].span) };
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
                        err(unsuffixSpan, `${unsuffixSnip} is not an integer`);
                    }

                    expr = { type: 'Number', span: unsuffixSpan, suffix: (foundSuffix[1] as { type: 'int', value: IntTy }).value, value: unsuffixSnip };
                } else {
                    expr = { type: 'Number', span: tokens[i].span, suffix: null, value: +snip(tokens[i].span) };
                }
                break;
            }
            case TokenType.String: expr = { type: 'String', span: tokens[i].span, value: snip([tokens[i].span[0] + 1, tokens[i].span[1] - 1]) }; break;
            case TokenType.Ident:
                // foo
                // foo::<bar>
                // foo::<>::bar
                // foo::<>::bar::<baz>
                const segments: PathSegment<AstTy>[] = [
                    { ident: snip(tokens[i].span), args: [] }
                ];
                i++;

                let lastWasGenericArgs = false;
                while (tokens[i].ty === TokenType.Colon && tokens[i + 1].ty === TokenType.Colon) {
                    i += 2;
                    if (eatToken(TokenType.Lt, false)) {
                        if (lastWasGenericArgs) {
                            err(tokens[i - 1].span, 'cannot specify generic arguments on path twice');
                        }
                        lastWasGenericArgs = true;
                        const args: GenericArg<AstTy>[] = [];
                        while (!eatToken(TokenType.Gt, false)) {
                            if (args.length > 0) {
                                eatToken(TokenType.Comma);
                            }
                            args.push({ ty: parseTy(), type: 'Type' });
                        }
                        segments[segments.length - 1].args = args;
                    } else {
                        lastWasGenericArgs = false;

                        const ident = expectIdent();
                        segments.push({ ident, args: [] });
                    }
                }
                i--;
                // TODO: this span is just wrong
                expr = { type: 'Path', span: tokens[i].span, path: { segments } };
                break;
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
                    const value = parseRootSubexpr();
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
                    elements.push(parseRootSubexpr());

                    if (elements.length === 1 && eatToken(TokenType.Semi, false)) {
                        // We have something like `[expr;`: this is an array repeat expression
                        const count = parseRootSubexpr();
                        if (count.type !== 'Number') {
                            err(count.span, `array repeat expression must be a number, got ${count.type}`);
                        }
                        eatToken(TokenType.RSquare);
                        return { type: 'ArrayRepeat', count: count.value, element: elements[0], span: joinSpan(span, tokens[i - 1].span) };
                    }
                }
                return { type: 'ArrayLiteral', elements, span: joinSpan(span, tokens[i - 1].span) };
            }
            case TokenType.Break: return { type: 'Break', span: tokens[i++].span };
            case TokenType.Continue: return { type: 'Continue', span: tokens[i++].span };
            case TokenType.Match: {
                const startSpan = tokens[i].span;
                i++;
                const scrutinee = parseRootSubexpr();
                eatToken(TokenType.LBrace);

                // parse arms
                const arms: AstArm[] = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    if (arms.length > 0) {
                        const lastArm = arms[arms.length - 1];
                        if (lastArm.body.type !== 'Block') {
                            // Allow e.g.
                            //   pat => {}
                            //   pat => {}
                            // but do require commas for:
                            //   pat => return,
                            //   pat => return
                            eatToken(TokenType.Comma);
                        }
                    }
                    const pat = parseRootPat();
                    eatToken(TokenType.FatArrow);
                    const body = parseRootSubexpr();
                    arms.push({ pat, body });
                }

                return { type: 'Match', span: joinSpan(startSpan, tokens[i - 1].span), scrutinee, arms };
            }
            case TokenType.ByteChar: {
                let char = snip(tokens[i].span).slice(2, -1);
                // Rewrite escapes, e.g. \n into a literal newline
                if (char[0] === '\\') {
                    switch (char[1]) {
                        case 'n':
                            if (char.length > 2) {
                                err(tokens[i].span, 'byte char literal can only contain one byte');
                            }
                            char = '\n';
                            break;
                        default: err(tokens[i].span, 'unknown escape sequence: ' + char[1]);
                    }
                } else if (char.length > 1) {
                    err(tokens[i].span, 'byte char literal can only contain one byte');
                }
                assert(char.length === 1, 'multibyte byte char literal after rewrite?');

                expr = { type: 'ByteCharacter', span: tokens[i].span, value: char };
                break;
            }
            default: err(tokens[i].span, `invalid token ${TokenType[tokens[i].ty]} (expected bottom expression)`);
        }
        i++;
        return expr;
    }

    // Parses a block expression. Assumes that if we don't require lbraces, the previous token was the lbrace.
    function parseBlockExpr(requireLbrace: boolean): Expr & { type: 'Block' } {
        let lbraceSpan: Span;
        if (requireLbrace) {
            lbraceSpan = tokens[i].span;
            eatToken(TokenType.LBrace);
        } else {
            lbraceSpan = tokens[i - 1].span;
        }

        const stmts = [];
        let tailExpr: Expr | null = null;
        while (!eatToken(TokenType.RBrace, false)) {
            const stmt = parseStmtOrTailExpr();
            if (stmt.type === 'TailExpr') {
                tailExpr = stmt.value;
                break;
            } else {
                stmts.push(stmt);
            }
        }
        return { type: 'Block', span: joinSpan(lbraceSpan, tokens[i - 1].span), stmts, tailExpr };
    };

    let parseRootSubexpr = () => parseExpr(-1, ParseContext.Subexpression);
    let parseRootStmtExpr = () => parseExpr(-1, ParseContext.Statement);

    function parseExpr(minPrecedence: number, ctxt: ParseContext): Expr {
        // Unary expressions.
        let expr: Expr;
        switch (tokens[i].ty) {
            case TokenType.Return: {
                let returnKwSpan = tokens[i++].span;
                const value = parseRootSubexpr();
                expr = { type: 'Return', span: joinSpan(returnKwSpan, value.span), value };
                break;
            }
            case TokenType.LBrace: expr = parseBlockExpr(true); break;
            case TokenType.LParen: {
                // Either tuple type or grouping, depending on if the expression is followed by a comma
                const lparenSpan = tokens[i++].span;
                if (tokens[i].ty === TokenType.RParen) {
                    i++;
                    expr = { type: 'Tuple', elements: [], span: joinSpan(lparenSpan, tokens[i - 1].span) };
                    break;
                }

                const first = parseRootSubexpr();
                if (eatToken(TokenType.Comma, false)) {
                    const elements = [first];
                    while (!eatToken(TokenType.RParen, false)) {
                        if (elements.length > 1) {
                            eatToken(TokenType.Comma, true);
                        }
                        elements.push(parseRootSubexpr());
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
                const condition = parseRootSubexpr();
                const body = parseBlockExpr(true);
                let _else: Expr | null = null;
                if (eatToken(TokenType.Else, false)) {
                    // This seems like a bit of a hack: we parse in a statement context
                    // so that we don't parse `if ... else { 0 } + 1` as `else ({ 0 } + 1)`
                    _else = parseRootStmtExpr();
                    if (_else.type !== 'Block' && _else.type !== 'If') {
                        err(_else.span, 'else expression must be a block or another chained `if` expression');
                    }
                }
                expr = { type: 'If', condition, then: body, else: _else, span: joinSpan(ifSpan, tokens[i - 1].span) };
                break;
            }
            case TokenType.While: {
                const whileSpan = tokens[i++].span;
                const condition = parseRootSubexpr();
                const body = parseBlockExpr(true);
                expr = { type: 'While', body, condition, span: joinSpan(whileSpan, tokens[i - 1].span) };
                break;
            }
            case TokenType.And: {
                // Unary &
                const andSpan = tokens[i++].span;
                const pointee = parseExpr(UNARY_PRECEDENCE[TokenType.And]!, ParseContext.Subexpression);

                expr = { type: 'AddrOf', mtb: 'imm', pointee, span: joinSpan(andSpan, pointee.span) };
                break;
            }
            case TokenType.Star: {
                // Dereference
                const starSpan = tokens[i++].span;
                const pointee = parseExpr(UNARY_PRECEDENCE[TokenType.Star]!, ParseContext.Subexpression);
                expr = { type: 'Deref', pointee, span: joinSpan(starSpan, pointee.span) };
                break;
            }
            case TokenType.Not: {
                // Unary !
                const notSpan = tokens[i++].span;
                const rhs = parseExpr(UNARY_PRECEDENCE[TokenType.Not]!, ParseContext.Subexpression);
                expr = { type: 'Unary', op: TokenType.Not, rhs, span: joinSpan(notSpan, rhs.span) };
                break;
            }
            case TokenType.Minus: {
                // Unary -
                const minusSpan = tokens[i++].span;
                const rhs = parseExpr(UNARY_PRECEDENCE[TokenType.Minus]!, ParseContext.Subexpression);
                expr = { type: 'Unary', op: TokenType.Minus, rhs, span: joinSpan(minusSpan, rhs.span) };
                break;
            }
            default:
                expr = parseBottomExpr();
        }

        if (ctxt === ParseContext.Statement && isBlockLike(expr)) {
            return expr;
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
                case TokenType.Assign:
                case TokenType.AddAssign:
                case TokenType.SubAssign:
                case TokenType.MulAssign:
                case TokenType.DivAssign:
                case TokenType.RemAssign: {
                    const rhs = parseExpr(prec, ParseContext.Subexpression);
                    expr = { type: 'Assignment', op: op.ty, target: expr, value: rhs, span: joinSpan(expr.span, rhs.span) };
                    break;
                }
                case TokenType.LParen: {
                    let args = [];
                    while (i < tokens.length && tokens[i].ty !== TokenType.RParen) {
                        eatToken(TokenType.Comma, false);
                        args.push(parseRootSubexpr());
                    }
                    eatToken(TokenType.RParen, true);
                    expr = { type: 'FnCall', callee: expr, args, span: [expr.span[0], tokens[i - 1].span[1]] };
                    break;
                }
                case TokenType.Dot:
                case TokenType.StarDot: {
                    // x.y and x*.y are identical parsing wise for the most part

                    let property: string | number;
                    const propertySpan = tokens[i].span;
                    switch (tokens[i].ty) {
                        case TokenType.Ident: property = snip(tokens[i++].span); break;
                        case TokenType.Number: property = +snip(tokens[i++].span); break;
                        default: err(propertySpan, 'property must be a string or number');
                    }

                    // After the 'property', if we see :: or ( then this is a method call.
                    let genericArgs: GenericArg<AstTy>[] = [];
                    switch (tokens[i].ty) {
                        case TokenType.Colon: {
                            i++;
                            eatToken(TokenType.Colon);
                            eatToken(TokenType.Lt);
                            while (!eatToken(TokenType.Gt, false)) {
                                if (genericArgs.length > 0) {
                                    eatToken(TokenType.Comma);
                                }
                                genericArgs.push({ type: 'Type', ty: parseTy() });
                            }
                            eatToken(TokenType.LParen);
                            // back to ')' because we immediately increment it again due to fallthrough
                            i--;
                        }
                        case TokenType.LParen: {
                            i++;
                            const args: Expr[] = [];
                            while (!eatToken(TokenType.RParen, false)) {
                                args.push(parseRootSubexpr());
                            }
                            if (typeof property !== 'string') {
                                err(propertySpan, 'method call property cannot be a number');
                            }

                            expr = {
                                type: 'MethodCall',
                                args,
                                path: { args: genericArgs, ident: property },
                                deref: op.ty === TokenType.StarDot,
                                target: expr, span: joinSpan(expr.span, tokens[i - 1].span)
                            };
                            break;
                        }
                        default:
                            expr = {
                                type: 'Property',
                                target: expr,
                                property,
                                span: [expr.span[0], tokens[i - 1].span[1]],
                                deref: op.ty === TokenType.StarDot,
                            }
                    }

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
                case TokenType.Percent:
                case TokenType.AndAnd:
                case TokenType.OrOr: {
                    const rhs = parseExpr(prec, ParseContext.Subexpression);
                    expr = { type: 'Binary', op: op.ty, lhs: expr, rhs, span: joinSpan(expr.span, rhs.span) };
                    break;
                }
                case TokenType.LSquare: {
                    const index = parseRootSubexpr();
                    eatToken(TokenType.RSquare);
                    expr = { type: 'Index', index, span: joinSpan(expr.span, tokens[i - 1].span), target: expr };
                    break;
                }
                default: bug(op.span, `unknown binary/infix operator for expression: ${op}`);
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
            if (tokens[i].ty === TokenType.Ident && snip(tokens[i].span) === 'self') {
                i++;
                // Receiver.
                let ptr = eatToken(TokenType.Star, false);
                parameters.push({ type: 'Receiver', ptr: ptr ? 'imm' : null });
            } else {
                const name = expectIdent();
                eatToken(TokenType.Colon);
                const ty = parseTy();
                parameters.push({ type: 'Parameter', name, ty });
            }
        }

        const ret = eatToken(TokenType.Colon, false) ? parseTy() : undefined;

        return {
            name,
            generics,
            parameters,
            ret,
        };
    }

    function parseStmtOrTailExpr(): Stmt | { type: 'TailExpr', value: Expr } {
        const startSpan = tokens[i].span;
        switch (tokens[i].ty) {
            case TokenType.Extern: {
                i++;
                const abi = parseRootSubexpr();
                if (abi.type !== 'String' || (abi.value !== 'C' && abi.value !== 'intrinsic')) {
                    err(abi.span, 'extern abi must be a string and "C" or "intrinsic"');
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
                const body = parseRootStmtExpr();

                return {
                    type: 'FnDecl',
                    body,
                    span: joinSpan(startSpan, tokens[i - 1].span),
                    parent: null,
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
                let init: Expr | null = null;
                if (eatToken(TokenType.Assign, false)) {
                    init = parseRootSubexpr();
                }
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
                aliasTyName = name;
                const alias = parseTy();
                aliasTyName = null;
                eatToken(TokenType.Semi);
                return { span: [tySpan[0], tokens[i - 1].span[1]], type: 'TyAlias', name, alias, constructibleIn, generics };
            }
            case TokenType.Mod: {
                const modKwSpan = tokens[i++].span;
                const name = expectIdent();
                if (eatToken(TokenType.LBrace, false)) {
                    // Inline.
                    const items: Stmt[] = [];
                    while (!eatToken(TokenType.RBrace, false)) {
                        const stmt = parseStmt();
                        items.push(stmt);
                    }

                    return { type: 'Mod', modType: 'Inline', items, name, span: joinSpan(modKwSpan, tokens[i - 1].span) }
                } else {
                    // Outlined in its own file.
                    eatToken(TokenType.Semi);

                    let normPath: string;
                    if (currentPathAttr) {
                        normPath = path.join(path.dirname(file.path), currentPathAttr);
                    } else if (file.isRoot) {
                        normPath = path.join(path.dirname(file.path), name + '.chg');
                    } else {
                        normPath = path.join(path.dirname(file.path), path.basename(file.path, '.chg'), name + '.chg');
                    }

                    const modFile = addFileToSourceMap(sm, normPath, false);
                    const { stmts } = parse(sm, attrs, modFile);
                    return {
                        type: 'Mod',
                        modType: 'Outlined',
                        items: stmts,
                        name,
                        span: spanFromFile(modFile)
                    };
                }
            }
            case TokenType.Impl: {
                const implKwSpan = tokens[i].span;
                i++;
                const generics = parseGenericsList();
                let selfTy: AstTy = parseTy();
                let ofTrait: { type: 'Path' } & AstTy | null = null;
                if (eatToken(TokenType.For, false)) {
                    // impl Trait **for** Type
                    // We incorrectly parsed the trait reference as a type, but that's okay, paths are also types, so unwrap the path here
                    // and reparse the next thing as a type.
                    if (selfTy.type !== 'Path') {
                        err(selfTy.span, 'trait reference in impl must be a path');
                    }
                    ofTrait = selfTy;
                    selfTy = parseTy();
                }
                eatToken(TokenType.LBrace);

                const items: ImplItem[] = [];
                let impl: { span: Span } & Impl = { type: 'Impl', items, selfTy, generics, ofTrait, span: implKwSpan };
                while (!eatToken(TokenType.RBrace, false)) {
                    // Parse associated items.
                    const sp = tokens[i].span;
                    const item = parseStmtOrTailExpr();
                    if (item.type !== 'FnDecl') {
                        bug(sp, 'only functions are supported in impls for now');
                    }
                    item.parent = impl;

                    items.push({ type: 'Fn', decl: item });
                }
                impl.span = joinSpan(implKwSpan, tokens[i - 1].span);

                return impl;
            }
            case TokenType.Trait: {
                const traitKwSpan = tokens[i++].span;
                const name = expectIdent();
                const items: TraitItem[] = [];
                eatToken(TokenType.LBrace);
                while (!eatToken(TokenType.RBrace, false)) {
                    eatToken(TokenType.Fn);
                    const sig = parseFnSignature();
                    eatToken(TokenType.Semi);
                    items.push({ type: 'Fn', sig });
                }
                return {
                    type: 'Trait', items, name, span: joinSpan(traitKwSpan, tokens[i - 1].span)
                };
            }
            case TokenType.Use: {
                const useKwSpan = tokens[i++].span;
                if (tokens[i].ty !== TokenType.Ident) {
                    err(tokens[i].span, 'use must be followed by a path');
                }
                const path: Path<never> = parseTyPath((segment) => {
                    if (segment.args.length > 0) {
                        err(tokens[i].span, 'use path cannot have generics');
                    }
                    return { ident: segment.ident, args: [] };
                });
                const alias = eatToken(TokenType.As, false)
                    ? expectIdent()
                    : null;
                const semiSpan = tokens[i].span;
                eatToken(TokenType.Semi);
                return { type: 'Use', path, alias, span: joinSpan(useKwSpan, semiSpan) };
            }
            default: {
                const value = parseRootStmtExpr();

                // we allow block-like expression statements without a semicolon
                if (isBlockLike(value) || eatToken(TokenType.Semi, false)) {
                    // eat any extra ones
                    while (eatToken(TokenType.Semi, false));

                    return { span: [value.span[0], tokens[i - 1].span[1]], type: 'Expr', value };
                } else {
                    // Trailing expressions must be followed by the end of the block, i.e. the `}`
                    eatToken(TokenType.RBrace);
                    return { type: 'TailExpr', value };
                }
            }
        }
    }

    function parseStmt(): Stmt {
        const attrStartSpan = tokens[i].span;
        const stmtAttrs = parseAttributes();
        const attrStartEnd = tokens[i].span;
        let pathAttr: Attribute | undefined;
        if (pathAttr = stmtAttrs.find(attr => attr.key === 'path')) {
            if (!pathAttr.value || pathAttr.value.type !== 'String') {
                err(joinSpan(attrStartSpan, attrStartEnd), '#[path] attr value must be a string');
            }
            currentPathAttr = pathAttr.value.value;
        }

        const stmt = parseStmtOrTailExpr();
        if (stmt.type === 'TailExpr') {
            err(stmt.value.span, 'no trailing expression expected');
        } else {
            attrs.set(stmt, stmtAttrs);
            return stmt;
        }
    }

    while (i < tokens.length) {
        stmts.push(parseStmt());
    }

    return {
        stmts
    };
}
