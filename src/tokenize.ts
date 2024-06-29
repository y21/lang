import { Span } from "./span";
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

export function tokenize(src: string): Token[] {
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
                        case 'break': ty = TokenType.Break; break;
                        case 'continue': ty = TokenType.Continue; break;
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