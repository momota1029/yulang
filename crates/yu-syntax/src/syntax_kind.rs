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
    BindingHeader,
    BindingBody,
    ModDeclaration,
    StructDeclaration,
    StructField,
    EnumDeclaration,
    EnumVariant,
    ErrorDeclaration,
    TypeDeclaration,
    RoleDeclaration,
    ImplDeclaration,
    ImplDescription,
    CastDeclaration,
    CastPattern,
    CastTarget,
    CastBody,
    ActDeclaration,
    DeclarationCompanion,
    DeclarationCompanionIndentedBody,
    DocCommentDeclaration,
    DocLinePrefix,
    DocBlockOpen,
    DocBlockClose,
    YmDoc,
    YmSection,
    YmImplicitSection,
    YmExplicitSection,
    YmHeading,
    YmSectionClose,
    YmText,
    YmHeadingMarker,
    YmListMarker,
    YmQuoteFenceMarker,
    YmQuotePrefix,
    YmFenceMarker,
    YmBlankLine,
    YmList,
    YmListItem,
    YmListItemBody,
    YmQuoteBlock,
    YmCodeFence,
    YmCodeFenceInfo,
    YmCodeFenceText,
    YmYulangCodeCell,
    YmParagraph,
    YmCommand,
    YmCommandArgs,
    YmCommandBody,
    YmDoCapture,
    YmMy,
    YmMyBindingHead,
    YmMyExpressionBody,
    YmUse,
    YmIfChain,
    YmIf,
    YmIfCondition,
    YmElsif,
    YmElsifCondition,
    YmElse,
    YmBackslash,
    YmBangLBracket,
    YmStrongMarker,
    YmEmphasisMarker,
    YmInlineRef,
    YmInlineGroup,
    YmInlineLink,
    YmInlineImage,
    YmInlineApply,
    YmInlineApplyHead,
    YmInlineApplyArgs,
    YmYulangArgs,
    YmDocArg,
    YmEmphasis,
    YmStrong,
    ForStatement,
    ForLabel,
    ForIterable,
    DeclarationTypeParameterList,
    DerivesClause,
    TestModuleMarker,
    IntegerLiteral,
    IdentifierExpression,
    ParenthesizedExpression,
    IfExpression,
    CaseExpression,
    CatchExpression,
    CaseLabel,
    CatchLabel,
    CaseScrutinee,
    CatchScrutinee,
    CaseBlock,
    CatchBlock,
    CaseArm,
    CatchArm,
    CaseGuard,
    CatchGuard,
    CaseArmSeparator,
    CatchArmSeparator,
    BracedStatementBlockExpression,
    Pattern,
    IdentifierPattern,
    IntegerPattern,
    SymbolPattern,
    ParenthesizedPattern,
    ListPattern,
    ListPatternSpreadItem,
    RecordPattern,
    RecordPatternField,
    RecordPatternSpreadItem,
    TypeExpression,
    ParenthesizedTypeGroup,
    NamedRecordType,
    TypeRecordField,
    ForallType,
    ForallTypeBinder,
    EffectRowType,
    BracketRow,
    PolymorphicVariantType,
    PolymorphicVariantTag,
    PolymorphicVariantPayload,
    TypePathTail,
    TypeCallTail,
    TypeApplyArgument,
    TypeArrowTail,
    PatternAliasTail,
    PatternAlternationTail,
    PatternTypeAnnotation,
    IfArm,
    ElseArm,
    Condition,
    OperatorChain,
    ColonApplicationTail,
    WithBodyTail,
    CallTail,
    IndexTail,
    IndexItem,
    ProjectionTupleTail,
    ProjectionRecordTail,
    ProjectionRecordSpreadItem,
    FieldTail,
    PathTail,
    MlArgument,
    IndentedStatementBlock,
    Statement,
    BlockStatementSeparator,
    PrefixOperatorUse,
    InfixOperatorUse,
    SuffixOperatorUse,
    NullfixOperatorUse,
    UseKw,
    ModKw,
    StructKw,
    EnumKw,
    ErrorKw,
    TypeKw,
    RoleKw,
    ImplKw,
    CastKw,
    ActKw,
    ForKw,
    InKw,
    RealmKw,
    BandKw,
    AsKw,
    WithoutKw,
    WithKw,
    DerivesKw,
    FromKw,
    ViaKw,
    InfixKw,
    MyKw,
    PubKw,
    OurKw,
    LazyKw,
    PrefixKw,
    SuffixKw,
    NullfixKw,
    IfKw,
    CaseKw,
    CatchKw,
    WhereKw,
    ElsifKw,
    ElseKw,
    Identifier,
    SigilIdentifier,
    Integer,
    Version,
    Dot,
    DotDot,
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
    Pipe,
    Arrow,
    Operator,
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
    Unknown,
    StringLiteral,
    StringEscape,
    StringInterpolation,
    StringInterpolationBody,
    RuleExpression,
    RuleBody,
    RuleAlternation,
    RuleSequence,
    RuleItem,
    RuleCapture,
    RuleQuantifier,
    RuleField,
    RulePath,
    RuleCall,
    RuleIndex,
    RuleLiteral,
    RuleLiteralInterpolation,
    RuleLazyCapture,
    StringStart,
    StringEnd,
    StringText,
    StringEscapeLead,
    StringEscapeSimple,
    StringEscapeUnicodeStart,
    StringEscapeUnicodeHex,
    StringEscapeUnicodeEnd,
    StringInterpolationPercent,
    StringInterpolationFormatText,
    StringInterpolationOpenBrace,
    StringInterpolationCloseBrace,
    RuleKw,
    RuleQuantifierToken,
    RuleLiteralStart,
    RuleLiteralEnd,
    RuleLiteralText,
    RuleLiteralOpenBrace,
    RuleLiteralCloseBrace,
    RuleLiteralColon,
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
            value if value == SyntaxKind::BindingHeader as u16 => SyntaxKind::BindingHeader,
            value if value == SyntaxKind::BindingBody as u16 => SyntaxKind::BindingBody,
            value if value == SyntaxKind::ModDeclaration as u16 => SyntaxKind::ModDeclaration,
            value if value == SyntaxKind::StructDeclaration as u16 => SyntaxKind::StructDeclaration,
            value if value == SyntaxKind::StructField as u16 => SyntaxKind::StructField,
            value if value == SyntaxKind::EnumDeclaration as u16 => SyntaxKind::EnumDeclaration,
            value if value == SyntaxKind::EnumVariant as u16 => SyntaxKind::EnumVariant,
            value if value == SyntaxKind::ErrorDeclaration as u16 => SyntaxKind::ErrorDeclaration,
            value if value == SyntaxKind::TypeDeclaration as u16 => SyntaxKind::TypeDeclaration,
            value if value == SyntaxKind::RoleDeclaration as u16 => SyntaxKind::RoleDeclaration,
            value if value == SyntaxKind::ImplDeclaration as u16 => SyntaxKind::ImplDeclaration,
            value if value == SyntaxKind::ImplDescription as u16 => SyntaxKind::ImplDescription,
            value if value == SyntaxKind::CastDeclaration as u16 => SyntaxKind::CastDeclaration,
            value if value == SyntaxKind::CastPattern as u16 => SyntaxKind::CastPattern,
            value if value == SyntaxKind::CastTarget as u16 => SyntaxKind::CastTarget,
            value if value == SyntaxKind::CastBody as u16 => SyntaxKind::CastBody,
            value if value == SyntaxKind::ActDeclaration as u16 => SyntaxKind::ActDeclaration,
            value if value == SyntaxKind::DeclarationCompanion as u16 => {
                SyntaxKind::DeclarationCompanion
            }
            value if value == SyntaxKind::DeclarationCompanionIndentedBody as u16 => {
                SyntaxKind::DeclarationCompanionIndentedBody
            }
            value if value == SyntaxKind::DocCommentDeclaration as u16 => {
                SyntaxKind::DocCommentDeclaration
            }
            value if value == SyntaxKind::DocLinePrefix as u16 => SyntaxKind::DocLinePrefix,
            value if value == SyntaxKind::DocBlockOpen as u16 => SyntaxKind::DocBlockOpen,
            value if value == SyntaxKind::DocBlockClose as u16 => SyntaxKind::DocBlockClose,
            value if value == SyntaxKind::YmDoc as u16 => SyntaxKind::YmDoc,
            value if value == SyntaxKind::YmSection as u16 => SyntaxKind::YmSection,
            value if value == SyntaxKind::YmImplicitSection as u16 => SyntaxKind::YmImplicitSection,
            value if value == SyntaxKind::YmExplicitSection as u16 => SyntaxKind::YmExplicitSection,
            value if value == SyntaxKind::YmHeading as u16 => SyntaxKind::YmHeading,
            value if value == SyntaxKind::YmSectionClose as u16 => SyntaxKind::YmSectionClose,
            value if value == SyntaxKind::YmText as u16 => SyntaxKind::YmText,
            value if value == SyntaxKind::YmHeadingMarker as u16 => SyntaxKind::YmHeadingMarker,
            value if value == SyntaxKind::YmListMarker as u16 => SyntaxKind::YmListMarker,
            value if value == SyntaxKind::YmQuoteFenceMarker as u16 => {
                SyntaxKind::YmQuoteFenceMarker
            }
            value if value == SyntaxKind::YmQuotePrefix as u16 => SyntaxKind::YmQuotePrefix,
            value if value == SyntaxKind::YmFenceMarker as u16 => SyntaxKind::YmFenceMarker,
            value if value == SyntaxKind::YmBlankLine as u16 => SyntaxKind::YmBlankLine,
            value if value == SyntaxKind::YmList as u16 => SyntaxKind::YmList,
            value if value == SyntaxKind::YmListItem as u16 => SyntaxKind::YmListItem,
            value if value == SyntaxKind::YmListItemBody as u16 => SyntaxKind::YmListItemBody,
            value if value == SyntaxKind::YmQuoteBlock as u16 => SyntaxKind::YmQuoteBlock,
            value if value == SyntaxKind::YmCodeFence as u16 => SyntaxKind::YmCodeFence,
            value if value == SyntaxKind::YmCodeFenceInfo as u16 => SyntaxKind::YmCodeFenceInfo,
            value if value == SyntaxKind::YmCodeFenceText as u16 => SyntaxKind::YmCodeFenceText,
            value if value == SyntaxKind::YmYulangCodeCell as u16 => SyntaxKind::YmYulangCodeCell,
            value if value == SyntaxKind::YmParagraph as u16 => SyntaxKind::YmParagraph,
            value if value == SyntaxKind::YmCommand as u16 => SyntaxKind::YmCommand,
            value if value == SyntaxKind::YmCommandArgs as u16 => SyntaxKind::YmCommandArgs,
            value if value == SyntaxKind::YmCommandBody as u16 => SyntaxKind::YmCommandBody,
            value if value == SyntaxKind::YmDoCapture as u16 => SyntaxKind::YmDoCapture,
            value if value == SyntaxKind::YmMy as u16 => SyntaxKind::YmMy,
            value if value == SyntaxKind::YmMyBindingHead as u16 => SyntaxKind::YmMyBindingHead,
            value if value == SyntaxKind::YmMyExpressionBody as u16 => {
                SyntaxKind::YmMyExpressionBody
            }
            value if value == SyntaxKind::YmUse as u16 => SyntaxKind::YmUse,
            value if value == SyntaxKind::YmIfChain as u16 => SyntaxKind::YmIfChain,
            value if value == SyntaxKind::YmIf as u16 => SyntaxKind::YmIf,
            value if value == SyntaxKind::YmIfCondition as u16 => SyntaxKind::YmIfCondition,
            value if value == SyntaxKind::YmElsif as u16 => SyntaxKind::YmElsif,
            value if value == SyntaxKind::YmElsifCondition as u16 => SyntaxKind::YmElsifCondition,
            value if value == SyntaxKind::YmElse as u16 => SyntaxKind::YmElse,
            value if value == SyntaxKind::YmBackslash as u16 => SyntaxKind::YmBackslash,
            value if value == SyntaxKind::YmBangLBracket as u16 => SyntaxKind::YmBangLBracket,
            value if value == SyntaxKind::YmStrongMarker as u16 => SyntaxKind::YmStrongMarker,
            value if value == SyntaxKind::YmEmphasisMarker as u16 => SyntaxKind::YmEmphasisMarker,
            value if value == SyntaxKind::YmInlineRef as u16 => SyntaxKind::YmInlineRef,
            value if value == SyntaxKind::YmInlineGroup as u16 => SyntaxKind::YmInlineGroup,
            value if value == SyntaxKind::YmInlineLink as u16 => SyntaxKind::YmInlineLink,
            value if value == SyntaxKind::YmInlineImage as u16 => SyntaxKind::YmInlineImage,
            value if value == SyntaxKind::YmInlineApply as u16 => SyntaxKind::YmInlineApply,
            value if value == SyntaxKind::YmInlineApplyHead as u16 => SyntaxKind::YmInlineApplyHead,
            value if value == SyntaxKind::YmInlineApplyArgs as u16 => SyntaxKind::YmInlineApplyArgs,
            value if value == SyntaxKind::YmYulangArgs as u16 => SyntaxKind::YmYulangArgs,
            value if value == SyntaxKind::YmDocArg as u16 => SyntaxKind::YmDocArg,
            value if value == SyntaxKind::YmEmphasis as u16 => SyntaxKind::YmEmphasis,
            value if value == SyntaxKind::YmStrong as u16 => SyntaxKind::YmStrong,
            value if value == SyntaxKind::ForStatement as u16 => SyntaxKind::ForStatement,
            value if value == SyntaxKind::ForLabel as u16 => SyntaxKind::ForLabel,
            value if value == SyntaxKind::ForIterable as u16 => SyntaxKind::ForIterable,
            value if value == SyntaxKind::DeclarationTypeParameterList as u16 => {
                SyntaxKind::DeclarationTypeParameterList
            }
            value if value == SyntaxKind::DerivesClause as u16 => SyntaxKind::DerivesClause,
            value if value == SyntaxKind::TestModuleMarker as u16 => SyntaxKind::TestModuleMarker,
            value if value == SyntaxKind::IntegerLiteral as u16 => SyntaxKind::IntegerLiteral,
            value if value == SyntaxKind::IdentifierExpression as u16 => {
                SyntaxKind::IdentifierExpression
            }
            value if value == SyntaxKind::ParenthesizedExpression as u16 => {
                SyntaxKind::ParenthesizedExpression
            }
            value if value == SyntaxKind::IfExpression as u16 => SyntaxKind::IfExpression,
            value if value == SyntaxKind::CaseExpression as u16 => SyntaxKind::CaseExpression,
            value if value == SyntaxKind::CatchExpression as u16 => SyntaxKind::CatchExpression,
            value if value == SyntaxKind::CaseLabel as u16 => SyntaxKind::CaseLabel,
            value if value == SyntaxKind::CatchLabel as u16 => SyntaxKind::CatchLabel,
            value if value == SyntaxKind::CaseScrutinee as u16 => SyntaxKind::CaseScrutinee,
            value if value == SyntaxKind::CatchScrutinee as u16 => SyntaxKind::CatchScrutinee,
            value if value == SyntaxKind::CaseBlock as u16 => SyntaxKind::CaseBlock,
            value if value == SyntaxKind::CatchBlock as u16 => SyntaxKind::CatchBlock,
            value if value == SyntaxKind::CaseArm as u16 => SyntaxKind::CaseArm,
            value if value == SyntaxKind::CatchArm as u16 => SyntaxKind::CatchArm,
            value if value == SyntaxKind::CaseGuard as u16 => SyntaxKind::CaseGuard,
            value if value == SyntaxKind::CatchGuard as u16 => SyntaxKind::CatchGuard,
            value if value == SyntaxKind::CaseArmSeparator as u16 => SyntaxKind::CaseArmSeparator,
            value if value == SyntaxKind::CatchArmSeparator as u16 => SyntaxKind::CatchArmSeparator,
            value if value == SyntaxKind::BracedStatementBlockExpression as u16 => {
                SyntaxKind::BracedStatementBlockExpression
            }
            value if value == SyntaxKind::Pattern as u16 => SyntaxKind::Pattern,
            value if value == SyntaxKind::IdentifierPattern as u16 => SyntaxKind::IdentifierPattern,
            value if value == SyntaxKind::IntegerPattern as u16 => SyntaxKind::IntegerPattern,
            value if value == SyntaxKind::SymbolPattern as u16 => SyntaxKind::SymbolPattern,
            value if value == SyntaxKind::ParenthesizedPattern as u16 => {
                SyntaxKind::ParenthesizedPattern
            }
            value if value == SyntaxKind::ListPattern as u16 => SyntaxKind::ListPattern,
            value if value == SyntaxKind::ListPatternSpreadItem as u16 => {
                SyntaxKind::ListPatternSpreadItem
            }
            value if value == SyntaxKind::RecordPattern as u16 => SyntaxKind::RecordPattern,
            value if value == SyntaxKind::RecordPatternField as u16 => {
                SyntaxKind::RecordPatternField
            }
            value if value == SyntaxKind::RecordPatternSpreadItem as u16 => {
                SyntaxKind::RecordPatternSpreadItem
            }
            value if value == SyntaxKind::TypeExpression as u16 => SyntaxKind::TypeExpression,
            value if value == SyntaxKind::ParenthesizedTypeGroup as u16 => {
                SyntaxKind::ParenthesizedTypeGroup
            }
            value if value == SyntaxKind::NamedRecordType as u16 => SyntaxKind::NamedRecordType,
            value if value == SyntaxKind::TypeRecordField as u16 => SyntaxKind::TypeRecordField,
            value if value == SyntaxKind::ForallType as u16 => SyntaxKind::ForallType,
            value if value == SyntaxKind::ForallTypeBinder as u16 => SyntaxKind::ForallTypeBinder,
            value if value == SyntaxKind::EffectRowType as u16 => SyntaxKind::EffectRowType,
            value if value == SyntaxKind::BracketRow as u16 => SyntaxKind::BracketRow,
            value if value == SyntaxKind::PolymorphicVariantType as u16 => {
                SyntaxKind::PolymorphicVariantType
            }
            value if value == SyntaxKind::PolymorphicVariantTag as u16 => {
                SyntaxKind::PolymorphicVariantTag
            }
            value if value == SyntaxKind::PolymorphicVariantPayload as u16 => {
                SyntaxKind::PolymorphicVariantPayload
            }
            value if value == SyntaxKind::TypePathTail as u16 => SyntaxKind::TypePathTail,
            value if value == SyntaxKind::TypeCallTail as u16 => SyntaxKind::TypeCallTail,
            value if value == SyntaxKind::TypeApplyArgument as u16 => SyntaxKind::TypeApplyArgument,
            value if value == SyntaxKind::TypeArrowTail as u16 => SyntaxKind::TypeArrowTail,
            value if value == SyntaxKind::PatternAliasTail as u16 => SyntaxKind::PatternAliasTail,
            value if value == SyntaxKind::PatternAlternationTail as u16 => {
                SyntaxKind::PatternAlternationTail
            }
            value if value == SyntaxKind::PatternTypeAnnotation as u16 => {
                SyntaxKind::PatternTypeAnnotation
            }
            value if value == SyntaxKind::IfArm as u16 => SyntaxKind::IfArm,
            value if value == SyntaxKind::ElseArm as u16 => SyntaxKind::ElseArm,
            value if value == SyntaxKind::Condition as u16 => SyntaxKind::Condition,
            value if value == SyntaxKind::OperatorChain as u16 => SyntaxKind::OperatorChain,
            value if value == SyntaxKind::ColonApplicationTail as u16 => {
                SyntaxKind::ColonApplicationTail
            }
            value if value == SyntaxKind::CallTail as u16 => SyntaxKind::CallTail,
            value if value == SyntaxKind::IndexTail as u16 => SyntaxKind::IndexTail,
            value if value == SyntaxKind::IndexItem as u16 => SyntaxKind::IndexItem,
            value if value == SyntaxKind::ProjectionTupleTail as u16 => {
                SyntaxKind::ProjectionTupleTail
            }
            value if value == SyntaxKind::ProjectionRecordTail as u16 => {
                SyntaxKind::ProjectionRecordTail
            }
            value if value == SyntaxKind::ProjectionRecordSpreadItem as u16 => {
                SyntaxKind::ProjectionRecordSpreadItem
            }
            value if value == SyntaxKind::FieldTail as u16 => SyntaxKind::FieldTail,
            value if value == SyntaxKind::PathTail as u16 => SyntaxKind::PathTail,
            value if value == SyntaxKind::MlArgument as u16 => SyntaxKind::MlArgument,
            value if value == SyntaxKind::WithBodyTail as u16 => SyntaxKind::WithBodyTail,
            value if value == SyntaxKind::IndentedStatementBlock as u16 => {
                SyntaxKind::IndentedStatementBlock
            }
            value if value == SyntaxKind::Statement as u16 => SyntaxKind::Statement,
            value if value == SyntaxKind::BlockStatementSeparator as u16 => {
                SyntaxKind::BlockStatementSeparator
            }
            value if value == SyntaxKind::PrefixOperatorUse as u16 => SyntaxKind::PrefixOperatorUse,
            value if value == SyntaxKind::InfixOperatorUse as u16 => SyntaxKind::InfixOperatorUse,
            value if value == SyntaxKind::SuffixOperatorUse as u16 => SyntaxKind::SuffixOperatorUse,
            value if value == SyntaxKind::NullfixOperatorUse as u16 => {
                SyntaxKind::NullfixOperatorUse
            }
            value if value == SyntaxKind::UseKw as u16 => SyntaxKind::UseKw,
            value if value == SyntaxKind::ModKw as u16 => SyntaxKind::ModKw,
            value if value == SyntaxKind::StructKw as u16 => SyntaxKind::StructKw,
            value if value == SyntaxKind::EnumKw as u16 => SyntaxKind::EnumKw,
            value if value == SyntaxKind::ErrorKw as u16 => SyntaxKind::ErrorKw,
            value if value == SyntaxKind::TypeKw as u16 => SyntaxKind::TypeKw,
            value if value == SyntaxKind::RoleKw as u16 => SyntaxKind::RoleKw,
            value if value == SyntaxKind::ImplKw as u16 => SyntaxKind::ImplKw,
            value if value == SyntaxKind::CastKw as u16 => SyntaxKind::CastKw,
            value if value == SyntaxKind::ActKw as u16 => SyntaxKind::ActKw,
            value if value == SyntaxKind::ForKw as u16 => SyntaxKind::ForKw,
            value if value == SyntaxKind::InKw as u16 => SyntaxKind::InKw,
            value if value == SyntaxKind::RealmKw as u16 => SyntaxKind::RealmKw,
            value if value == SyntaxKind::BandKw as u16 => SyntaxKind::BandKw,
            value if value == SyntaxKind::AsKw as u16 => SyntaxKind::AsKw,
            value if value == SyntaxKind::WithoutKw as u16 => SyntaxKind::WithoutKw,
            value if value == SyntaxKind::WithKw as u16 => SyntaxKind::WithKw,
            value if value == SyntaxKind::DerivesKw as u16 => SyntaxKind::DerivesKw,
            value if value == SyntaxKind::FromKw as u16 => SyntaxKind::FromKw,
            value if value == SyntaxKind::ViaKw as u16 => SyntaxKind::ViaKw,
            value if value == SyntaxKind::InfixKw as u16 => SyntaxKind::InfixKw,
            value if value == SyntaxKind::MyKw as u16 => SyntaxKind::MyKw,
            value if value == SyntaxKind::PubKw as u16 => SyntaxKind::PubKw,
            value if value == SyntaxKind::OurKw as u16 => SyntaxKind::OurKw,
            value if value == SyntaxKind::LazyKw as u16 => SyntaxKind::LazyKw,
            value if value == SyntaxKind::PrefixKw as u16 => SyntaxKind::PrefixKw,
            value if value == SyntaxKind::SuffixKw as u16 => SyntaxKind::SuffixKw,
            value if value == SyntaxKind::NullfixKw as u16 => SyntaxKind::NullfixKw,
            value if value == SyntaxKind::IfKw as u16 => SyntaxKind::IfKw,
            value if value == SyntaxKind::CaseKw as u16 => SyntaxKind::CaseKw,
            value if value == SyntaxKind::CatchKw as u16 => SyntaxKind::CatchKw,
            value if value == SyntaxKind::WhereKw as u16 => SyntaxKind::WhereKw,
            value if value == SyntaxKind::ElsifKw as u16 => SyntaxKind::ElsifKw,
            value if value == SyntaxKind::ElseKw as u16 => SyntaxKind::ElseKw,
            value if value == SyntaxKind::Identifier as u16 => SyntaxKind::Identifier,
            value if value == SyntaxKind::SigilIdentifier as u16 => SyntaxKind::SigilIdentifier,
            value if value == SyntaxKind::Integer as u16 => SyntaxKind::Integer,
            value if value == SyntaxKind::Version as u16 => SyntaxKind::Version,
            value if value == SyntaxKind::Dot as u16 => SyntaxKind::Dot,
            value if value == SyntaxKind::DotDot as u16 => SyntaxKind::DotDot,
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
            value if value == SyntaxKind::Pipe as u16 => SyntaxKind::Pipe,
            value if value == SyntaxKind::Arrow as u16 => SyntaxKind::Arrow,
            value if value == SyntaxKind::Operator as u16 => SyntaxKind::Operator,
            value if value == SyntaxKind::Whitespace as u16 => SyntaxKind::Whitespace,
            value if value == SyntaxKind::Newline as u16 => SyntaxKind::Newline,
            value if value == SyntaxKind::LineComment as u16 => SyntaxKind::LineComment,
            value if value == SyntaxKind::BlockComment as u16 => SyntaxKind::BlockComment,
            value if value == SyntaxKind::StringLiteral as u16 => SyntaxKind::StringLiteral,
            value if value == SyntaxKind::StringEscape as u16 => SyntaxKind::StringEscape,
            value if value == SyntaxKind::StringInterpolation as u16 => {
                SyntaxKind::StringInterpolation
            }
            value if value == SyntaxKind::StringInterpolationBody as u16 => {
                SyntaxKind::StringInterpolationBody
            }
            value if value == SyntaxKind::RuleExpression as u16 => SyntaxKind::RuleExpression,
            value if value == SyntaxKind::RuleBody as u16 => SyntaxKind::RuleBody,
            value if value == SyntaxKind::RuleAlternation as u16 => SyntaxKind::RuleAlternation,
            value if value == SyntaxKind::RuleSequence as u16 => SyntaxKind::RuleSequence,
            value if value == SyntaxKind::RuleItem as u16 => SyntaxKind::RuleItem,
            value if value == SyntaxKind::RuleCapture as u16 => SyntaxKind::RuleCapture,
            value if value == SyntaxKind::RuleQuantifier as u16 => SyntaxKind::RuleQuantifier,
            value if value == SyntaxKind::RuleField as u16 => SyntaxKind::RuleField,
            value if value == SyntaxKind::RulePath as u16 => SyntaxKind::RulePath,
            value if value == SyntaxKind::RuleCall as u16 => SyntaxKind::RuleCall,
            value if value == SyntaxKind::RuleIndex as u16 => SyntaxKind::RuleIndex,
            value if value == SyntaxKind::RuleLiteral as u16 => SyntaxKind::RuleLiteral,
            value if value == SyntaxKind::RuleLiteralInterpolation as u16 => {
                SyntaxKind::RuleLiteralInterpolation
            }
            value if value == SyntaxKind::RuleLazyCapture as u16 => SyntaxKind::RuleLazyCapture,
            value if value == SyntaxKind::StringStart as u16 => SyntaxKind::StringStart,
            value if value == SyntaxKind::StringEnd as u16 => SyntaxKind::StringEnd,
            value if value == SyntaxKind::StringText as u16 => SyntaxKind::StringText,
            value if value == SyntaxKind::StringEscapeLead as u16 => SyntaxKind::StringEscapeLead,
            value if value == SyntaxKind::StringEscapeSimple as u16 => {
                SyntaxKind::StringEscapeSimple
            }
            value if value == SyntaxKind::StringEscapeUnicodeStart as u16 => {
                SyntaxKind::StringEscapeUnicodeStart
            }
            value if value == SyntaxKind::StringEscapeUnicodeHex as u16 => {
                SyntaxKind::StringEscapeUnicodeHex
            }
            value if value == SyntaxKind::StringEscapeUnicodeEnd as u16 => {
                SyntaxKind::StringEscapeUnicodeEnd
            }
            value if value == SyntaxKind::StringInterpolationPercent as u16 => {
                SyntaxKind::StringInterpolationPercent
            }
            value if value == SyntaxKind::StringInterpolationFormatText as u16 => {
                SyntaxKind::StringInterpolationFormatText
            }
            value if value == SyntaxKind::StringInterpolationOpenBrace as u16 => {
                SyntaxKind::StringInterpolationOpenBrace
            }
            value if value == SyntaxKind::StringInterpolationCloseBrace as u16 => {
                SyntaxKind::StringInterpolationCloseBrace
            }
            value if value == SyntaxKind::RuleKw as u16 => SyntaxKind::RuleKw,
            value if value == SyntaxKind::RuleQuantifierToken as u16 => {
                SyntaxKind::RuleQuantifierToken
            }
            value if value == SyntaxKind::RuleLiteralStart as u16 => SyntaxKind::RuleLiteralStart,
            value if value == SyntaxKind::RuleLiteralEnd as u16 => SyntaxKind::RuleLiteralEnd,
            value if value == SyntaxKind::RuleLiteralText as u16 => SyntaxKind::RuleLiteralText,
            value if value == SyntaxKind::RuleLiteralOpenBrace as u16 => {
                SyntaxKind::RuleLiteralOpenBrace
            }
            value if value == SyntaxKind::RuleLiteralCloseBrace as u16 => {
                SyntaxKind::RuleLiteralCloseBrace
            }
            value if value == SyntaxKind::RuleLiteralColon as u16 => SyntaxKind::RuleLiteralColon,
            _ => SyntaxKind::Unknown,
        }
    }

    fn kind_to_raw(kind: Self::Kind) -> RowanSyntaxKind {
        kind.into()
    }
}

pub type SyntaxNode = rowan::SyntaxNode<YulangLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<YulangLanguage>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yumark_syntax_kinds_round_trip_through_rowan() {
        for kind in [
            SyntaxKind::DocCommentDeclaration,
            SyntaxKind::YmDoc,
            SyntaxKind::YmCommandBody,
            SyntaxKind::YmYulangCodeCell,
            SyntaxKind::YmInlineApplyArgs,
            SyntaxKind::YmStrong,
        ] {
            let raw = <YulangLanguage as Language>::kind_to_raw(kind);
            assert_eq!(<YulangLanguage as Language>::kind_from_raw(raw), kind);
        }
    }

    #[test]
    fn literal_syntax_kinds_round_trip_through_rowan() {
        for kind in [
            SyntaxKind::StringLiteral,
            SyntaxKind::StringEscape,
            SyntaxKind::StringInterpolation,
            SyntaxKind::StringInterpolationBody,
            SyntaxKind::RuleExpression,
            SyntaxKind::RuleBody,
            SyntaxKind::RuleAlternation,
            SyntaxKind::RuleSequence,
            SyntaxKind::RuleItem,
            SyntaxKind::RuleCapture,
            SyntaxKind::RuleQuantifier,
            SyntaxKind::RuleField,
            SyntaxKind::RulePath,
            SyntaxKind::RuleCall,
            SyntaxKind::RuleIndex,
            SyntaxKind::RuleLiteral,
            SyntaxKind::RuleLiteralInterpolation,
            SyntaxKind::RuleLazyCapture,
            SyntaxKind::StringStart,
            SyntaxKind::StringEnd,
            SyntaxKind::StringText,
            SyntaxKind::StringEscapeLead,
            SyntaxKind::StringEscapeSimple,
            SyntaxKind::StringEscapeUnicodeStart,
            SyntaxKind::StringEscapeUnicodeHex,
            SyntaxKind::StringEscapeUnicodeEnd,
            SyntaxKind::StringInterpolationPercent,
            SyntaxKind::StringInterpolationFormatText,
            SyntaxKind::StringInterpolationOpenBrace,
            SyntaxKind::StringInterpolationCloseBrace,
            SyntaxKind::RuleKw,
            SyntaxKind::RuleQuantifierToken,
            SyntaxKind::RuleLiteralStart,
            SyntaxKind::RuleLiteralEnd,
            SyntaxKind::RuleLiteralText,
            SyntaxKind::RuleLiteralOpenBrace,
            SyntaxKind::RuleLiteralCloseBrace,
            SyntaxKind::RuleLiteralColon,
        ] {
            let raw = <YulangLanguage as Language>::kind_to_raw(kind);
            assert_eq!(<YulangLanguage as Language>::kind_from_raw(raw), kind);
        }
    }

    #[test]
    fn appending_literal_kinds_preserves_the_old_unknown_discriminant() {
        assert_eq!(SyntaxKind::Unknown as u16, 229);
    }
}
