//! Typed recovery vocabulary shared by parser construction and diagnostics.

use std::{ops::Range, sync::Arc};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Delimiter {
    Parenthesis,
    Bracket,
    Brace,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum GrammarRole {
    Declaration(DeclarationRole),
    ForStatement(ForStatementRole),
    ClosingDelimiter {
        owner: ConstructRole,
        delimiter: Delimiter,
    },
    Statement(StatementRole),
    Expression(ExpressionRole),
    ExpressionList(ExpressionListRole),
    ColonApplication(ColonApplicationRole),
    WithBody(WithBodyRole),
    IfExpression(IfExpressionRole),
    CaseLike(CaseLikeRole),
    BracedStatementBlock(BracedStatementBlockRole),
    Pattern(PatternRole),
    Type(TypeRole),
    Literal(LiteralRole),
    Layout(LayoutRole),
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Embedded(EmbeddedRole),
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Yumark(YumarkRole),
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Token(TokenRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct YumarkRole {
    pub(crate) owner: YumarkOwner,
    pub(crate) slot: YumarkSlot,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
    dead_code,
    reason = "typed recovery vocabulary retained for deferred owner migration"
)]
pub(crate) enum YumarkOwner {
    DocComment,
    Section,
    List,
    ListItem,
    Quote,
    CodeFence,
    InlineGroup,
    InlineLink,
    InlineImage,
    InlineApply,
    InlineReference,
    Emphasis,
    Strong,
    Command,
    My,
    Use,
    DocArgument,
    DoCapture,
    IfChain,
    IfBranch,
    ElsifBranch,
    ElseBranch,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
    dead_code,
    reason = "typed recovery vocabulary retained for deferred owner migration"
)]
pub(crate) enum YumarkSlot {
    Starter,
    Name,
    Head,
    Arguments,
    Condition,
    BodyIntroducer,
    Body,
    Destination,
    BranchPredecessor,
    ClosingDelimiter,
    SectionClose,
    QuoteForm,
    ExpressionBody,
    Route,
    Terminator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeclarationRole {
    Import(ImportRole),
    OperatorHeader(OperatorHeaderRole),
    Binding(BindingRole),
    Mod(ModRole),
    Struct(StructRole),
    Enum(EnumDeclarationRole),
    Error(ErrorDeclarationRole),
    Type(TypeDeclarationRole),
    Role(RoleDeclarationRole),
    Impl(ImplRole),
    Cast(CastRole),
    Act(ActDeclarationRole),
    Derives(DerivesRole),
    Companion(DeclarationCompanionRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ImportRole {
    Path,
    GroupEntry,
    Alias,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum OperatorHeaderRole {
    Name,
    Fixity,
    LeftBindingPower,
    RightBindingPower,
    DefinitionIntroducer,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StatementKind {
    UseDeclaration,
    OperatorDefinition,
    BindingDeclaration,
    ModDeclaration,
    StructDeclaration,
    EnumDeclaration,
    ErrorDeclaration,
    TypeDeclaration,
    RoleDeclaration,
    ImplDeclaration,
    CastDeclaration,
    ActDeclaration,
    ForStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StatementRole {
    Starter,
    Separator,
    TrailingInput { owner: StatementKind },
    OperatorDefinitionBody,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ForStatementRole {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Pattern,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    InKeyword,
    Iterable,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum BindingRole {
    Target,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ModRole {
    Name,
    TestName,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StructRole {
    Name,
    BodyIntroducer,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Field,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    FieldName,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    FieldColon,
    FieldType,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    FieldSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum EnumDeclarationRole {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Name,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    BodyIntroducer,
    Variant(VariantDeclarationRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ErrorDeclarationRole {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Name,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    BodyIntroducer,
    Variant(VariantDeclarationRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum VariantDeclarationRole {
    Item,
    Name,
    Separator,
    FromType,
    PositionalPayload,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    NamedField,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    NamedFieldName,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    NamedFieldColon,
    NamedFieldType,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    NamedFieldSeparator,
    TupleFieldType,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TypeDeclarationRole {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Name,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    DefinitionIntroducer,
    Rhs,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    AttachedImpl(ImplRole),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ImplRole {
    Head,
    Description,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RoleDeclarationRole {
    Head,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ActDeclarationRole {
    Head,
    Source,
    BodyIntroducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CastRole {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    PatternIntroducer,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Pattern,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    TargetIntroducer,
    TargetType,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    BodyIntroducer,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DerivesRole {
    RoleReference,
    ViaTarget,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeclarationCompanionRole {
    Introducer,
    Body,
    Item,
    IndentedItem,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ConstructRole {
    ExpressionList,
    ImportGroup,
    OperatorName,
    ExpressionGroup,
    ArgumentList,
    IndexTail,
    ProjectionTupleTail,
    ProjectionRecordTail,
    BracedStatementBlockExpression,
    ParenthesizedPattern,
    ListPattern,
    RecordPattern,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    CastPattern,
    TypeCall,
    ParenthesizedTypeGroup,
    NamedRecordType,
    EffectRowType,
    BracketRow,
    PolymorphicVariantType,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    StructNamedFields,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    StructTupleFields,
    DeclarationCompanion,
    EnumBracedVariantBody,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    VariantNamedPayload,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    VariantTuplePayload,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExpressionListRole {
    Item,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExpressionRole {
    Nud,
    ParenthesizedSeparator,
    CallArgument,
    CallArgumentSeparator,
    IndexItem,
    IndexSeparator,
    ProjectionTupleItem,
    ProjectionTupleSeparator,
    ProjectionRecordItem,
    ProjectionRecordSpreadRhs,
    ProjectionRecordSeparator,
    FieldName,
    PathSegment,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    MlArgument,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ColonApplicationRole {
    Rhs,
    InlineArgument,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum WithBodyRole {
    Introducer,
    Body,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum IfExpressionRole {
    Condition,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    BodyIntroducer,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Body,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    ElseBody,
    IndentedStatement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CaseLikeRole {
    Scrutinee,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Block,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Arm,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Pattern,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Handler,
    Guard,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Arrow,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Body,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum BracedStatementBlockRole {
    Statement,
    Separator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PatternRole {
    Primary,
    SymbolName,
    AliasBinding,
    AlternationRhs,
    TypeAnnotation,
    ParenthesizedElement,
    ParenthesizedSeparator,
    ListItem,
    ListSpreadRhs,
    ListSeparator,
    RecordItem,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    RecordFieldName,
    RecordNestedPattern,
    RecordDefaultExpression,
    RecordSpreadRhs,
    RecordSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum TypeRole {
    Primary,
    PathSegment,
    CallArgument,
    CallArgumentSeparator,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    ApplyArgument,
    ArrowRhs,
    ParenthesizedItem,
    ParenthesizedSeparator,
    RecordField,
    RecordFieldName,
    RecordFieldColon,
    RecordFieldType,
    RecordFieldSeparator,
    ForallBinder,
    ForallBinderBoundary,
    ForallColon,
    ForallBody,
    EffectRowItem,
    EffectRowSeparator,
    BracketRowItem,
    BracketRowSeparator,
    LeadingEffectTypeHead,
    BracketRowArrow,
    PolymorphicVariantTag,
    PolymorphicVariantTagName,
    PolymorphicVariantPayload,
    PolymorphicVariantPayloadBoundary,
    PolymorphicVariantTagSeparator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LiteralRole {
    StringTerminator,
    StringEscapeSimpleTarget,
    StringEscapeUnicodeHex,
    StringEscapeUnicodeEnd,
    StringInterpolationOpenBrace,
    StringInterpolationCloseBrace,
    #[allow(
        dead_code,
        reason = "typed Rule DSL body-close contract awaits its production owner"
    )]
    RuleBodyCloseBrace,
    RuleParenClose,
    RuleCaptureRightItem,
    RuleFieldName,
    RulePathName,
    RuleUnexpectedItem,
    RuleLiteralTerminator,
    RuleLiteralInterpolationCloseBrace,
    RuleLazyCaptureName,
    RuleLazyCaptureCloseBrace,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LayoutRole {
    InlineTrivia,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
    dead_code,
    reason = "typed recovery vocabulary retained for deferred owner migration"
)]
pub(crate) enum EmbeddedRole {
    Body,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
    dead_code,
    reason = "typed recovery vocabulary retained for deferred owner migration"
)]
pub(crate) enum TokenRole {
    Punctuation,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RecoveryKind {
    Missing,
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UnexpectedSyntax {
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    EndOfInput {
        at: usize,
    },
    Token {
        range: Range<usize>,
        category: UnexpectedCategory,
    },
    Root(RootUnexpected),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum UnexpectedCategory {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PunctuationEvidence {
    Open(Delimiter),
    Close(Delimiter),
    Comma,
    Semicolon,
    Dot,
    Slash,
    Colon,
    ColonColon,
    Equals,
    Star,
    Apostrophe,
    Backslash,
    Arrow,
    Pipe,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RootUnexpected {
    UnrecognizedStarter {
        range: Range<usize>,
        head: RootUnexpectedHead,
    },
    TrailingInput {
        owner: StatementKind,
        range: Range<usize>,
        head: RootUnexpectedHead,
    },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum RootUnexpectedHead {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExpectedSyntax {
    Identifier,
    TypePayloadBoundary,
    Path,
    Expression,
    Pattern,
    TypeExpression,
    TypePathSegment,
    ForallTypeBinder,
    TypeBinderBoundary,
    Statement,
    StatementSeparator,
    OperatorName,
    BindingPower,
    InlineTrivia,
    DelimitedSequenceSeparator,
    Keyword(KeywordEvidence),
    Punctuation(PunctuationEvidence),
    Literal(LiteralExpected),
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Yumark(YumarkSyntaxEvidence),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LiteralExpected {
    StringTerminator,
    StringEscapeTarget,
    UnicodeHexDigit,
    RuleItem,
    RuleLiteralTerminator,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[allow(
    dead_code,
    reason = "typed recovery vocabulary retained for deferred owner migration"
)]
pub(crate) enum YumarkSyntaxEvidence {
    EmphasisMarker,
    StrongMarker,
    FenceMarker,
    QuoteFenceMarker,
    SectionCloseMarker,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum KeywordEvidence {
    In,
    Use,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Mod,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Struct,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Type,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    As,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Without,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    With,
    Lazy,
    Prefix,
    Infix,
    Suffix,
    Nullfix,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    If,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Elsif,
    #[allow(
        dead_code,
        reason = "typed recovery vocabulary retained for deferred owner migration"
    )]
    Else,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct ExpectationSources(u8);

impl ExpectationSources {
    #[cfg(test)]
    pub(crate) const SPECULATIVE: Self = Self(1);
    pub(crate) const COMMITTED_RECOVERY_RULE: Self = Self(1 << 1);

    #[cfg(test)]
    pub(crate) fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct SyntaxExpectation {
    pub(crate) role: GrammarRole,
    pub(crate) expected: ExpectedSyntax,
    pub(crate) range: Range<usize>,
    pub(crate) sources: ExpectationSources,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct RecoverySiteKey {
    pub(crate) role: GrammarRole,
    pub(crate) range: Range<usize>,
}

/// Revision-local recovery identity allocated by committed output.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct DiagnosticId(pub(crate) u32);

/// Recovery data is committed only after a recovery path has been selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CommittedRecoveryRecord {
    pub(crate) id: DiagnosticId,
    pub(crate) site: RecoverySiteKey,
    pub(crate) kind: RecoveryKind,
    pub(crate) unexpected: Arc<[UnexpectedSyntax]>,
    pub(crate) expectations: Arc<[SyntaxExpectation]>,
    pub(crate) primary_expectation: usize,
}
