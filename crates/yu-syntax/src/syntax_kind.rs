use rowan::{Language, SyntaxKind as RowanSyntaxKind};

/// Node and token kinds in the lossless Yulang syntax tree.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u16)]
pub enum SyntaxKind {
    Root,
    Missing,
    Error,
    UseDeclaration,
    UseTree,
    UsePath,
    UseGroup,
    UseGlob,
    UseAlias,
    UseQualifiers,
    UseVersion,
    UseAnchor,
    UseExclusion,
    UseExclusionGroup,
    OperatorHeader,
    OperatorName,
    BindingPower,
    BindingStatement,
    IntegerLiteral,
    IdentifierExpression,
    GroupedExpression,
    PrefixExpression,
    InfixExpression,
    SuffixExpression,
    NullfixExpression,
    UseKw,
    ModKw,
    RealmKw,
    BandKw,
    AsKw,
    WithoutKw,
    WithKw,
    InfixKw,
    MyKw,
    PubKw,
    OurKw,
    LazyKw,
    PrefixKw,
    SuffixKw,
    NullfixKw,
    Identifier,
    Integer,
    Version,
    Dot,
    ColonColon,
    Slash,
    Colon,
    Comma,
    Star,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Equals,
    Semicolon,
    Apostrophe,
    Backslash,
    Operator,
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
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
            value if value == SyntaxKind::Missing as u16 => SyntaxKind::Missing,
            value if value == SyntaxKind::Error as u16 => SyntaxKind::Error,
            value if value == SyntaxKind::UseDeclaration as u16 => SyntaxKind::UseDeclaration,
            value if value == SyntaxKind::UseTree as u16 => SyntaxKind::UseTree,
            value if value == SyntaxKind::UsePath as u16 => SyntaxKind::UsePath,
            value if value == SyntaxKind::UseGroup as u16 => SyntaxKind::UseGroup,
            value if value == SyntaxKind::UseGlob as u16 => SyntaxKind::UseGlob,
            value if value == SyntaxKind::UseAlias as u16 => SyntaxKind::UseAlias,
            value if value == SyntaxKind::UseQualifiers as u16 => SyntaxKind::UseQualifiers,
            value if value == SyntaxKind::UseVersion as u16 => SyntaxKind::UseVersion,
            value if value == SyntaxKind::UseAnchor as u16 => SyntaxKind::UseAnchor,
            value if value == SyntaxKind::UseExclusion as u16 => SyntaxKind::UseExclusion,
            value if value == SyntaxKind::UseExclusionGroup as u16 => SyntaxKind::UseExclusionGroup,
            value if value == SyntaxKind::OperatorHeader as u16 => SyntaxKind::OperatorHeader,
            value if value == SyntaxKind::OperatorName as u16 => SyntaxKind::OperatorName,
            value if value == SyntaxKind::BindingPower as u16 => SyntaxKind::BindingPower,
            value if value == SyntaxKind::BindingStatement as u16 => SyntaxKind::BindingStatement,
            value if value == SyntaxKind::IntegerLiteral as u16 => SyntaxKind::IntegerLiteral,
            value if value == SyntaxKind::IdentifierExpression as u16 => {
                SyntaxKind::IdentifierExpression
            }
            value if value == SyntaxKind::GroupedExpression as u16 => SyntaxKind::GroupedExpression,
            value if value == SyntaxKind::PrefixExpression as u16 => SyntaxKind::PrefixExpression,
            value if value == SyntaxKind::InfixExpression as u16 => SyntaxKind::InfixExpression,
            value if value == SyntaxKind::SuffixExpression as u16 => SyntaxKind::SuffixExpression,
            value if value == SyntaxKind::NullfixExpression as u16 => SyntaxKind::NullfixExpression,
            value if value == SyntaxKind::UseKw as u16 => SyntaxKind::UseKw,
            value if value == SyntaxKind::ModKw as u16 => SyntaxKind::ModKw,
            value if value == SyntaxKind::RealmKw as u16 => SyntaxKind::RealmKw,
            value if value == SyntaxKind::BandKw as u16 => SyntaxKind::BandKw,
            value if value == SyntaxKind::AsKw as u16 => SyntaxKind::AsKw,
            value if value == SyntaxKind::WithoutKw as u16 => SyntaxKind::WithoutKw,
            value if value == SyntaxKind::WithKw as u16 => SyntaxKind::WithKw,
            value if value == SyntaxKind::InfixKw as u16 => SyntaxKind::InfixKw,
            value if value == SyntaxKind::MyKw as u16 => SyntaxKind::MyKw,
            value if value == SyntaxKind::PubKw as u16 => SyntaxKind::PubKw,
            value if value == SyntaxKind::OurKw as u16 => SyntaxKind::OurKw,
            value if value == SyntaxKind::LazyKw as u16 => SyntaxKind::LazyKw,
            value if value == SyntaxKind::PrefixKw as u16 => SyntaxKind::PrefixKw,
            value if value == SyntaxKind::SuffixKw as u16 => SyntaxKind::SuffixKw,
            value if value == SyntaxKind::NullfixKw as u16 => SyntaxKind::NullfixKw,
            value if value == SyntaxKind::Identifier as u16 => SyntaxKind::Identifier,
            value if value == SyntaxKind::Integer as u16 => SyntaxKind::Integer,
            value if value == SyntaxKind::Version as u16 => SyntaxKind::Version,
            value if value == SyntaxKind::Dot as u16 => SyntaxKind::Dot,
            value if value == SyntaxKind::ColonColon as u16 => SyntaxKind::ColonColon,
            value if value == SyntaxKind::Slash as u16 => SyntaxKind::Slash,
            value if value == SyntaxKind::Colon as u16 => SyntaxKind::Colon,
            value if value == SyntaxKind::Comma as u16 => SyntaxKind::Comma,
            value if value == SyntaxKind::Star as u16 => SyntaxKind::Star,
            value if value == SyntaxKind::LParen as u16 => SyntaxKind::LParen,
            value if value == SyntaxKind::RParen as u16 => SyntaxKind::RParen,
            value if value == SyntaxKind::LBrace as u16 => SyntaxKind::LBrace,
            value if value == SyntaxKind::RBrace as u16 => SyntaxKind::RBrace,
            value if value == SyntaxKind::LBracket as u16 => SyntaxKind::LBracket,
            value if value == SyntaxKind::RBracket as u16 => SyntaxKind::RBracket,
            value if value == SyntaxKind::Equals as u16 => SyntaxKind::Equals,
            value if value == SyntaxKind::Semicolon as u16 => SyntaxKind::Semicolon,
            value if value == SyntaxKind::Apostrophe as u16 => SyntaxKind::Apostrophe,
            value if value == SyntaxKind::Backslash as u16 => SyntaxKind::Backslash,
            value if value == SyntaxKind::Operator as u16 => SyntaxKind::Operator,
            value if value == SyntaxKind::Whitespace as u16 => SyntaxKind::Whitespace,
            value if value == SyntaxKind::Newline as u16 => SyntaxKind::Newline,
            value if value == SyntaxKind::LineComment as u16 => SyntaxKind::LineComment,
            value if value == SyntaxKind::BlockComment as u16 => SyntaxKind::BlockComment,
            _ => SyntaxKind::Unknown,
        }
    }

    fn kind_to_raw(kind: Self::Kind) -> RowanSyntaxKind {
        kind.into()
    }
}

pub type SyntaxNode = rowan::SyntaxNode<YulangLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<YulangLanguage>;
