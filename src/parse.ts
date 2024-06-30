import { Span, joinSpan } from "./span";
import { TokenType } from "./token";
import { tokenize } from "./tokenize";
import { I16, I32, I64, I8, IntTy, Ty, U16, U32, U64, U8 } from "./ty";

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
    | TokenType.Percent;

export type UnaryOp = TokenType.Not;

export type AssignmentKind = TokenType.Assign
    | TokenType.AddAssign
    | TokenType.SubAssign
    | TokenType.MulAssign
    | TokenType.DivAssign
    | TokenType.RemAssign;

export type Expr = { span: Span } & (
    | { type: "Block"; stmts: Stmt[] }
    | { type: "Path"; path: Path<AstTy> }
    | { type: "FnCall"; args: Expr[]; callee: Expr }
    | { type: "Index"; target: Expr; index: Expr }
    | { type: "ArrayLiteral"; elements: Expr[] }
    | { type: "ArrayRepeat"; element: Expr; count: number }
    | { type: "Number"; value: number; suffix: IntTy }
    | { type: "Bool"; value: boolean }
    | { type: "String"; value: string }
    | { type: "Assignment"; op: AssignmentKind, target: Expr; value: Expr }
    | { type: "Property"; target: Expr; property: string | number }
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
    | { type: "If"; condition: Expr; then: Expr; else: Expr | null }
    | { type: "While"; condition: Expr; body: Expr }
    | { type: "Tuple", elements: Expr[] }
);

export type LetDecl = { type: 'LetDecl', name: string, ty: AstTy | null, init: Expr };

export type AstFnSignature = {
    name: string,
    generics: Generics,
    parameters: FnParameter[],
    ret?: AstTy,
};
export type FnDecl = {
    type: 'FnDecl',
    sig: AstFnSignature,
    body: Expr
};
export type ExternFnDecl = {
    type: 'ExternFnDecl'
    abi: 'C' | 'intrinsic',
    sig: AstFnSignature
};
export type FnParameter = { name: string, ty: AstTy };
export type Generics = string[];
export type TyAliasDecl = { type: 'TyAlias', name: string, generics: Generics, constructibleIn: Path<AstTy>[], alias: AstTy };
export type GenericArg<Ty> = { type: 'Type', ty: Ty };
export type PathSegment<Ty> = { ident: string; args: GenericArg<Ty>[] };
export type Path<Ty> = { segments: PathSegment<Ty>[] };
export type Stmt = { span: Span } & ({ type: 'Expr', value: Expr } | LetDecl | FnDecl | TyAliasDecl | ExternFnDecl);
export type Mutability = 'imm' | 'mut';
export type RecordFields<Ty> = ([string, Ty])[];
export type AstVariant = { name: string };
export type AstEnum = { type: 'Enum', name: string, variants: AstVariant[] };
export type VariantId = number;
export type AstTy = { type: 'Path', value: Path<AstTy> }
    | { type: 'Array', elemTy: AstTy, len: number }
    | { type: 'Tuple', elements: AstTy[] }
    | { type: 'Pointer', mtb: Mutability, pointeeTy: AstTy }
    | { type: 'Record', fields: RecordFields<AstTy> }
    | AstEnum
    | { type: 'Alias', alias: AstTy, constructibleIn: Path<never>[] }
    | { type: 'Infer' };
export type Program = { stmts: Stmt[] };
export type LeftToRight = 'ltr';
export type RightToLeft = 'rtl';
export type Associativity = LeftToRight | RightToLeft;

export type AstPat = { span: Span } & ({ type: 'Number', value: number }
    | { type: 'Path', path: Path<AstTy> });

export type AstArm = { pat: AstPat, body: Expr };

export function genericsOfDecl(decl: FnDecl | TyAliasDecl | ExternFnDecl): Generics {
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
    [TokenType.Not]: 'ltr',
    [TokenType.Lt]: 'ltr',
    [TokenType.Le]: 'ltr',
    [TokenType.Gt]: 'ltr',
    [TokenType.Ge]: 'ltr',
    [TokenType.EqEq]: 'ltr',
    [TokenType.NotEq]: 'ltr',
};

export function parse(src: string): Program {
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

    function parsePat(): AstPat {
        return parseBottomPat();
    }

    function parseBottomPat(): AstPat {
        const expr = parseRootExpr();
        switch (expr.type) {
            case 'Number': return { type: 'Number', value: expr.value, span: expr.span };
            case 'Path': return { type: 'Path', path: expr.path, span: expr.span };
            default: throw new Error(`${expr.type} cannot be used in pattern position`);
        }
    }

    let aliasTyName: string | null = null;
    function parseTy(): AstTy {
        // We only allow `type X = enum {}`, i.e. the enum must be the direct aliased type, so reset it here.
        let enclosingAlias = aliasTyName;
        aliasTyName = null;

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
            case TokenType.Enum:
                i++;
                let name: string | null = null;
                if (tokens[i].ty === TokenType.Ident) {
                    name = snip(tokens[i++].span);
                } else if (enclosingAlias !== null) {
                    name = enclosingAlias;
                } else {
                    throw new Error('anonymous enum must be a direct alias');
                }

                eatToken(TokenType.LBrace);
                const variants: AstVariant[] = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    if (variants.length > 0) eatToken(TokenType.Comma);
                    variants.push({ name: expectIdent() });
                }
                ty = { type: 'Enum', name, variants };
                break;
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
                            throw new Error('cannot specify generic arguments on path twice');
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
            case TokenType.Break: return { type: 'Break', span: tokens[i++].span };
            case TokenType.Continue: return { type: 'Continue', span: tokens[i++].span };
            case TokenType.Match: {
                const startSpan = tokens[i].span;
                i++;
                const scrutinee = parseRootExpr();
                eatToken(TokenType.LBrace);

                // parse arms
                const arms: AstArm[] = [];
                while (!eatToken(TokenType.RBrace, false)) {
                    const pat = parsePat();
                    eatToken(TokenType.FatArrow);
                    const body = parseRootExpr();
                    arms.push({ pat, body });
                }

                return { type: 'Match', span: joinSpan(startSpan, tokens[i - 1].span), scrutinee, arms };
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
                case TokenType.Assign:
                case TokenType.AddAssign:
                case TokenType.SubAssign:
                case TokenType.MulAssign:
                case TokenType.DivAssign:
                case TokenType.RemAssign: {
                    const rhs = parseExpr(prec);
                    expr = { type: 'Assignment', op: op.ty, target: expr, value: rhs, span: joinSpan(expr.span, rhs.span) };
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
                aliasTyName = name;
                const alias = parseTy();
                aliasTyName = null;
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
