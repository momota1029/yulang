use rowan::{Language, SyntaxKind as RowanSyntaxKind};

/// Node and token kinds in the lossless Yulang syntax tree.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u16)]
pub enum SyntaxKind {
    Root,
    UseDeclaration,
    OperatorHeader,
    BindingStatement,
    IntegerLiteral,
    UseKw,
    InfixKw,
    MyKw,
    Identifier,
    Integer,
    Dot,
    ColonColon,
    LParen,
    RParen,
    Equals,
    Operator,
    Whitespace,
    Newline,
    Unknown,
}

impl From<SyntaxKind> for RowanSyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// Rowan language marker for Yulang CST nodes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum YulangLanguage {}

impl Language for YulangLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: RowanSyntaxKind) -> Self::Kind {
        match raw.0 {
            value if value == SyntaxKind::Root as u16 => SyntaxKind::Root,
            value if value == SyntaxKind::UseDeclaration as u16 => SyntaxKind::UseDeclaration,
            value if value == SyntaxKind::OperatorHeader as u16 => SyntaxKind::OperatorHeader,
            value if value == SyntaxKind::BindingStatement as u16 => SyntaxKind::BindingStatement,
            value if value == SyntaxKind::IntegerLiteral as u16 => SyntaxKind::IntegerLiteral,
            value if value == SyntaxKind::UseKw as u16 => SyntaxKind::UseKw,
            value if value == SyntaxKind::InfixKw as u16 => SyntaxKind::InfixKw,
            value if value == SyntaxKind::MyKw as u16 => SyntaxKind::MyKw,
            value if value == SyntaxKind::Identifier as u16 => SyntaxKind::Identifier,
            value if value == SyntaxKind::Integer as u16 => SyntaxKind::Integer,
            value if value == SyntaxKind::Dot as u16 => SyntaxKind::Dot,
            value if value == SyntaxKind::ColonColon as u16 => SyntaxKind::ColonColon,
            value if value == SyntaxKind::LParen as u16 => SyntaxKind::LParen,
            value if value == SyntaxKind::RParen as u16 => SyntaxKind::RParen,
            value if value == SyntaxKind::Equals as u16 => SyntaxKind::Equals,
            value if value == SyntaxKind::Operator as u16 => SyntaxKind::Operator,
            value if value == SyntaxKind::Whitespace as u16 => SyntaxKind::Whitespace,
            value if value == SyntaxKind::Newline as u16 => SyntaxKind::Newline,
            _ => SyntaxKind::Unknown,
        }
    }

    fn kind_to_raw(kind: Self::Kind) -> RowanSyntaxKind {
        kind.into()
    }
}

pub type SyntaxNode = rowan::SyntaxNode<YulangLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<YulangLanguage>;
