import { err } from "./error";
import { SourceMap, Span, File } from "./span";
import { Token, TokenType } from "./token";

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

export function tokenize(sm: SourceMap, file: File): Token[] {
    const src = sm.source;
    const tokens: Token[] = [];

    // current char
    let c = file.startPos;

    let isAtEnd = () => c >= file.endPos;

    while (!isAtEnd()) {
        let start = c;

        switch (src[c]) {
            case ' ':
            case '\r':
            case '\n':
                break;
            case '(': tokens.push({ span: [start, c + 1], ty: TokenType.LParen }); break;
            case '_': tokens.push({ span: [start, c + 1], ty: TokenType.Underscore }); break;
            case '#': tokens.push({ span: [start, c + 1], ty: TokenType.Hash }); break;
            case ')': tokens.push({ span: [start, c + 1], ty: TokenType.RParen }); break;
            case '[': tokens.push({ span: [start, c + 1], ty: TokenType.LSquare }); break;
            case ']': tokens.push({ span: [start, c + 1], ty: TokenType.RSquare }); break;
            case '{': tokens.push({ span: [start, c + 1], ty: TokenType.LBrace }); break;
            case '}': tokens.push({ span: [start, c + 1], ty: TokenType.RBrace }); break;
            case '%':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.RemAssign });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Percent });
                }
                break;
            case ':': tokens.push({ span: [start, c + 1], ty: TokenType.Colon }); break;
            case '!':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.NotEq });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Not });
                }
                break;
            case '=':
                let ty: TokenType;
                let hi: number;
                switch (src[c + 1]) {
                    case '=': ty = TokenType.EqEq; hi = 2; break;
                    case '>': ty = TokenType.FatArrow; hi = 2; break;
                    default: ty = TokenType.Assign; hi = 1; break;
                }
                tokens.push({ span: [start, c + hi], ty });
                c += hi - 1;
                break;
            case ';': tokens.push({ span: [start, c + 1], ty: TokenType.Semi }); break;
            case '.':
                if (src[c + 1] === '.') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.DotDot });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Dot });
                }
                break;
            case '<':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.Le });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Lt });
                }
                break;
            case '>':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.Ge });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Gt });
                }
                break;
            case ',': tokens.push({ span: [start, c + 1], ty: TokenType.Comma }); break;
            case '|':
                if (src[c + 1] === '|') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.OrOr });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Or });
                }
                break;
            case '+':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.AddAssign });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Plus });
                }
                break;
            case '-':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.SubAssign });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Minus });
                }
                break;
            case '*':
                if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.MulAssign });
                    c++;
                } else if (src[c + 1] === '.') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.StarDot });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Star });
                }
                break;
            case '&':
                if (src[c + 1] === '&') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.AndAnd });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.And });
                }
                break;
            case '/': {
                if (src[c + 1] === '/') {
                    while (!isAtEnd() && src[c] !== '\n') c++;
                } else if (src[c + 1] === '=') {
                    tokens.push({ span: [start, c + 2], ty: TokenType.DivAssign });
                    c++;
                } else {
                    tokens.push({ span: [start, c + 1], ty: TokenType.Slash }); break;
                }
                break;
            }
            case '"':
                c++;
                while (!isAtEnd() && src[c] !== '"') c++;
                if (isAtEnd()) err([c, c], 'Unexpected end of file');
                tokens.push({ span: [start, c + 1], ty: TokenType.String });
                break;
            default:
                if (src[c] === 'b' && src[c + 1] === '\'') {
                    const startPos = c;
                    // usually byte character lines are only going to be one byte, but \n is two in the source code, so use a loop here.
                    // we don't do any parsing or validation here and leave that to the parser
                    c += 2;
                    while (!isAtEnd() && src[c] !== '\'') { c++; }
                    if (isAtEnd()) err([c, c], 'Unexpected end of file');
                    tokens.push({ ty: TokenType.ByteChar, span: [startPos, c + 1] });
                } else if (isAlphaStart(src[c])) {
                    let ident = '';
                    while (isAlpha(src[c])) ident += src[c++];
                    let span: Span = [start, c];
                    c--;
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
                        case 'else': ty = TokenType.Else; break;
                        case 'for': ty = TokenType.For; break;
                        case 'while': ty = TokenType.While; break;
                        case 'break': ty = TokenType.Break; break;
                        case 'enum': ty = TokenType.Enum; break;
                        case 'continue': ty = TokenType.Continue; break;
                        case 'match': ty = TokenType.Match; break;
                        case 'impl': ty = TokenType.Impl; break;
                        case 'mod': ty = TokenType.Mod; break;
                        case 'trait': ty = TokenType.Trait; break;
                        case 'use': ty = TokenType.Use; break;
                        case 'as': ty = TokenType.As; break;
                        case 'where': ty = TokenType.Where; break;
                        default: ty = TokenType.Ident; break;
                    }
                    tokens.push({ span, ty });
                } else if (isDigit(src[c])) {
                    while (!isAtEnd() && (isDigit(src[c]) || src[c] === 'i' || src[c] === 'u')) c++;
                    let span: Span = [start, c];
                    c--;
                    tokens.push({ span, ty: TokenType.Number });
                } else {
                    err([c, c + 1], 'unknown token: ' + src[c]);
                }
        }
        c++
    }
    return tokens;
}
