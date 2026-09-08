//! Finite caller-owned lexical stop masks.

pub(crate) type Stops = u16;

pub(crate) const STOP_COMMA: Stops = 1 << 0;
pub(crate) const STOP_SEMICOLON: Stops = 1 << 1;
const STOP_RPAREN: Stops = 1 << 2;
const STOP_RBRACKET: Stops = 1 << 3;
const STOP_RBRACE: Stops = 1 << 4;
pub(crate) const STOP_CLOSES: Stops = STOP_RPAREN | STOP_RBRACKET | STOP_RBRACE;
pub(crate) const STOP_RECORD_SPREAD: Stops = 1 << 5;
pub(crate) const STOP_RECORD_SPREAD_AFTER_OPERATOR: Stops = 1 << 6;
pub(crate) const STOP_COLON: Stops = 1 << 7;
pub(crate) const STOP_LBRACE: Stops = 1 << 8;
pub(crate) const STOP_ELSIF: Stops = 1 << 9;
pub(crate) const STOP_ELSE: Stops = 1 << 10;
pub(crate) const STOP_ARROW: Stops = 1 << 11;
pub(crate) const STOP_LINE_BREAK: Stops = 1 << 12;
pub(crate) const STOP_WITH: Stops = 1 << 13;
pub(crate) const STOP_IN: Stops = 1 << 14;

pub(crate) fn stops_for(close: crate::lexical::item::TokenKind) -> Stops {
    let close = match close {
        crate::lexical::item::TokenKind::RParen => STOP_RPAREN,
        crate::lexical::item::TokenKind::RBracket => STOP_RBRACKET,
        crate::lexical::item::TokenKind::RBrace => STOP_RBRACE,
        _ => unreachable!("only a matching close owns a delimited stop set"),
    };
    STOP_COMMA | STOP_SEMICOLON | close
}

pub(super) fn active_stop(source: &str, stops: Stops) -> bool {
    match source.chars().next() {
        Some(',') => stops & STOP_COMMA != 0,
        Some(';') => stops & STOP_SEMICOLON != 0,
        Some(')') => stops & STOP_RPAREN != 0,
        Some(']') => stops & STOP_RBRACKET != 0,
        Some('}') => stops & STOP_RBRACE != 0,
        Some(':') => stops & STOP_COLON != 0 && !source.starts_with("::"),
        Some('{') => stops & STOP_LBRACE != 0,
        Some('-') => stops & STOP_ARROW != 0 && crate::lexical::lexer::is_exact_arm_arrow(source),
        _ => false,
    }
}

pub(crate) fn active_stop_item(kind: crate::lexical::item::TokenKind, stops: Stops) -> bool {
    match kind {
        crate::lexical::item::TokenKind::Comma => stops & STOP_COMMA != 0,
        crate::lexical::item::TokenKind::Semicolon => stops & STOP_SEMICOLON != 0,
        crate::lexical::item::TokenKind::RParen => stops & STOP_RPAREN != 0,
        crate::lexical::item::TokenKind::RBracket => stops & STOP_RBRACKET != 0,
        crate::lexical::item::TokenKind::RBrace => stops & STOP_RBRACE != 0,
        crate::lexical::item::TokenKind::Colon => stops & STOP_COLON != 0,
        crate::lexical::item::TokenKind::LBrace => stops & STOP_LBRACE != 0,
        crate::lexical::item::TokenKind::Arrow => stops & STOP_ARROW != 0,
        _ => false,
    }
}
