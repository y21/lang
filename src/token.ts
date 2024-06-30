import { Span } from "./span";

export enum TokenType {
    Extern,
    Fn,
    Enum,
    Let,
    Return,
    If,
    For,
    While,
    Match,
    FatArrow,
    Type,
    True,
    False,
    Constructible,
    Ident,
    LParen,
    RParen,
    Break,
    Continue,
    LSquare,
    RSquare,
    LBrace,
    RBrace,
    Colon,
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
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
    DotDot,
    Dot,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    AndAnd,
    Or,
    OrOr,
    ByteChar
}

export interface Token {
    ty: TokenType;
    span: Span;
}


export function tokenCanContinuePattern(ty: TokenType): boolean {
    switch (ty) {
        case TokenType.Number:
        case TokenType.String:
        case TokenType.Ident:
        case TokenType.DotDot:
            return true;
        default:
            return false;
    }
}
