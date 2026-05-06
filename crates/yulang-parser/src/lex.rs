use smallvec::SmallVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriviaKind {
    Space,
    LineComment,
    BlockCommentStart,
    BlockCommentText,
    BlockCommentEnd,
    QuotePrefix,
}
impl From<TriviaKind> for SyntaxKind {
    fn from(kind: TriviaKind) -> Self {
        match kind {
            TriviaKind::Space => SyntaxKind::Space,
            TriviaKind::LineComment => SyntaxKind::LineComment,
            TriviaKind::BlockCommentText => SyntaxKind::BlockCommentText,
            TriviaKind::BlockCommentStart => SyntaxKind::BlockCommentStart,
            TriviaKind::BlockCommentEnd => SyntaxKind::BlockCommentEnd,
            TriviaKind::QuotePrefix => SyntaxKind::QuotePrefix,
        }
    }
}
#[derive(Debug, Clone)]
pub struct Trivia(SmallVec<[TriviaPart; 1]>);
#[derive(Debug, Clone)]
pub struct TriviaPart {
    pub kind: TriviaKind,
    pub text: Box<str>,
}
impl TriviaPart {
    pub fn new(kind: TriviaKind, text: impl AsRef<str>) -> Self {
        Self {
            kind,
            text: text.as_ref().into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriviaInfo {
    None,
    Space,
    Newline {
        indent: usize,
        quote_level: usize,
        blank_line: bool,
    },
}
impl Trivia {
    pub fn new(vec: SmallVec<[TriviaPart; 1]>) -> Self {
        Self(vec)
    }
    pub fn empty() -> Self {
        Self(SmallVec::new())
    }
    pub fn parts(&self) -> &[TriviaPart] {
        &self.0
    }
    pub fn info(&self) -> TriviaInfo {
        if self.0.is_empty() {
            return TriviaInfo::None;
        }
        let lines_to_2 = self
            .0
            .iter()
            .filter(|part| matches!(part.kind, TriviaKind::Space | TriviaKind::QuotePrefix))
            .flat_map(|part| part.text.chars())
            .filter(|c| *c == '\n')
            .take(2)
            .count();
        if lines_to_2 == 0 {
            return TriviaInfo::Space;
        }
        let blank_line = lines_to_2 >= 2;
        let last = self
            .0
            .iter()
            .rfind(|part| matches!(part.kind, TriviaKind::Space | TriviaKind::QuotePrefix));
        if let Some(last) = last {
            let (mut indent, mut quote_level) = (0, 0);
            for c in last.text.chars().rev() {
                match c {
                    '\r' | '\n' => break,
                    '>' => {
                        indent += 1;
                        quote_level += 1
                    }
                    ' ' | '\t' => indent += 1,
                    _ => (),
                }
            }
            return TriviaInfo::Newline {
                indent,
                quote_level,
                blank_line,
            };
        }
        TriviaInfo::Newline {
            indent: 0,
            quote_level: 0,
            blank_line,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u16)]
#[warn(dead_code)]
pub enum SyntaxKind {
    // trivia
    Space = 0,
    LineComment = 1,
    BlockCommentStart = 2,
    BlockCommentText = 3,
    BlockCommentEnd = 4,
    QuotePrefix = 5,
    DocComment = 6,
    BlockComment = 7,

    // tokens
    Trivia = 100,
    Ident = 101,
    Number = 102,
    StringStart = 103,
    StringEnd = 104,
    StringText = 105,
    StringEscapeLead = 106,
    StringEscapeSimple = 107,
    StringEscapeUnicodeStart = 108,
    StringEscapeUnicodeHex = 109,
    StringEscapeUnicodeEnd = 110,
    StringInterpPercent = 111,
    StringInterpFormatText = 112,
    StringInterpOpenBrace = 113,
    StringInterpCloseBrace = 114,
    Symbol = 115,
    SigilIdent = 116,
    OpName = 117,
    Keyword = 118,
    Do = 119,
    If = 120,
    Else = 121,
    Elsif = 122,
    Case = 123,
    Catch = 124,
    My = 125,
    Our = 126,
    Pub = 127,
    Use = 128,
    Type = 129,
    Struct = 130,
    Enum = 131,
    Role = 132,
    Impl = 133,
    Act = 134,
    Mod = 135,
    As = 136,
    For = 137,
    In = 138,
    With = 139,
    Where = 140,
    Via = 141,
    Mark = 142,
    ParenL = 143,
    ParenR = 144,
    BracketL = 145,
    BracketR = 146,
    BraceL = 147,
    BraceR = 148,
    Backslash = 149,
    Apostrophe = 150,
    Arrow = 151,
    ColonColon = 152,
    DotField = 153,
    Comma = 154,
    Colon = 155,
    Equal = 156,
    Semicolon = 157,
    Pipe = 158,
    Infix = 159,
    Prefix = 160,
    Suffix = 161,
    Nullfix = 162,
    Slash = 163,
    Unknown = 164,

    // rule / ~"..." tokens
    Rule = 165,
    Tilde = 166,
    RuleQuantStar = 167,
    RuleQuantStarLazy = 168,
    RuleQuantPlus = 169,
    RuleQuantPlusLazy = 170,
    RuleQuantOpt = 171,
    // rule literal tokens (inside ~"...")
    RuleLitStart = 172,
    RuleLitEnd = 173,
    RuleLitText = 174,
    RuleLitOpenBrace = 175,
    RuleLitCloseBrace = 176,
    RuleLitColon = 177,
    MarkLitStart = 178,
    MarkLitEnd = 179,
    MarkLitText = 180,
    MarkHeadingSigil = 181,
    MarkSectionCloseSigil = 182,
    MarkBlankLine = 183,
    DotDot = 184,
    Cast = 185,

    // Yumark tokens
    YmHashSigil = 186,
    YmHashDotSigil = 187,
    YmListDashSigil = 188,
    YmListNumSigil = 189,
    YmFenceSigil = 190,
    YmChevronBlockSigil = 191,
    YmChevronPrefixSigil = 192,
    YmBlankLine = 193,
    YmText = 194,
    YmLBracket = 195,
    YmRBracket = 196,
    YmBang = 197,
    YmColon = 198,
    YmBackslash = 199,
    YmIdent = 200,
    YmSemi = 201,
    YmNewline = 202,
    YmPrefix = 203,
    YmStarSigil = 204,
    YmStrongSigil = 205,
    YmDocBlockSigil = 206,

    // nodes
    InvalidToken = 500,
    Expr = 501,
    Pattern = 502,
    PatOr = 503,
    PatAs = 504,
    TypeAnn = 505,
    TypeExpr = 506,
    TypeApply = 507,
    TypeCall = 508,
    TypeArrow = 509,
    TypeForall = 510,
    ApplyML = 511,
    ApplyC = 512,
    ApplyColon = 513,
    PrefixNode = 514,
    InfixNode = 515,
    SuffixNode = 516,
    PathSep = 517,
    Field = 518,
    Index = 519,
    LambdaExpr = 520,
    IfExpr = 521,
    IfArm = 522,
    ElseArm = 523,
    Cond = 524,
    CaseExpr = 525,
    CaseBlock = 526,
    CaseArm = 527,
    CaseGuard = 528,
    CatchExpr = 529,
    CatchBlock = 530,
    CatchArm = 531,
    CatchGuard = 532,
    Paren = 533,
    Bracket = 534,
    BraceGroup = 535,
    IndentBlock = 536,
    Separator = 537,
    StringLit = 538,
    StringInterp = 539,
    PatParenGroup = 540,
    PatRecord = 541,
    PatField = 542,
    TypeParenGroup = 543,
    TypeRecord = 544,
    TypeField = 545,
    TypeRow = 546,
    Binding = 547,
    BindingHeader = 548,
    BindingBody = 549,
    ModDecl = 550,
    UseDecl = 551,
    ActDecl = 552,
    TypeDecl = 553,
    StructDecl = 554,
    EnumDecl = 555,
    RoleDecl = 556,
    ImplDecl = 557,
    WhereClause = 558,
    StructField = 559,
    EnumVariant = 560,
    OpDef = 561,
    OpDefHeader = 562,
    OpDefBody = 563,
    Root = 564,
    WhereConstraint = 565,
    TypeVars = 566,
    TypePolyVariant = 567,
    TypePolyVariantItem = 568,

    // rule / ~"..." nodes
    RuleExpr = 569,
    RuleLit = 570,
    RuleAlt = 571,
    RuleSeq = 572,
    RuleCapture = 573,
    RuleParserRef = 574,
    RuleLazyCapture = 575,
    RuleQuant = 576,
    RuleLitInterp = 577,
    MarkExpr = 578,
    MarkInlineBody = 579,
    MarkHeredocBody = 580,
    MarkDoc = 581,
    MarkParagraph = 582,
    MarkText = 583,
    MarkHeading = 584,
    MarkSectionClose = 585,

    // Yumark nodes
    YmDoc = 586,
    YmHeading = 587,
    YmImplicitSection = 588,
    YmExplicitSection = 589,
    YmSectionClose = 590,
    YmList = 591,
    YmListItem = 592,
    YmListItemBody = 593,
    YmCodeFence = 594,
    YmCodeFenceInfo = 595,
    YmCodeFenceText = 596,
    YmQuoteBlock = 597,
    YmParagraph = 598,
    YmInlineExpr = 599,
    YmLinkDest = 600,
    YmApplyOp = 601,
    YmApplyArgs = 602,
    YmInlineRef = 603,
    YmInlineRefArgs = 604,
    YmCommand = 605,
    YmCommandArgs = 606,
    YmCommandBody = 607,
    YmMy = 608,
    YmMyHead = 609,
    YmMyBody = 610,
    YmUse = 611,
    YmIfChain = 612,
    YmIf = 613,
    YmElsif = 614,
    YmElse = 615,
    YmIfCond = 616,
    YmIfBody = 617,
    YmYulangArgs = 618,
    YmEmphasis = 619,
    YmStrong = 620,

    // doc comment statement node
    DocCommentDecl = 621,
    CastDecl = 633,
    PatSpread = 624,

    // effect row in type argument position: '[ ... ]
    TypeEffectRow = 622,

    // expression assignment suffix: lhs = rhs
    Assign = 623,

    // expression where-like suffix: expr with: ...
    WithBlock = 625,

    // list pattern: [head, ..tail]
    PatList = 626,

    // expression pipeline suffix: lhs | rhs
    PipeNode = 627,

    // statement loop: for x in xs: ...
    ForStmt = 628,
    ForHeader = 629,
    ForBody = 630,
    ForLabel = 631,
    ExprSpread = 632,
}

#[derive(Debug, Clone)]
pub struct Lex {
    pub leading_trivia_info: TriviaInfo,
    pub kind: SyntaxKind,
    pub text: Box<str>,
    pub trailing_trivia: Trivia,
}

#[derive(Debug, Clone)]
pub struct Token<Tag> {
    pub lex: Lex,
    pub tag: Tag,
}

#[derive(Debug, Clone)]
pub struct BareToken<Tag> {
    pub kind: SyntaxKind,
    pub tag: Tag,
    pub text: Box<str>,
}

impl Lex {
    pub fn new(
        leading_trivia_info: TriviaInfo,
        kind: SyntaxKind,
        text: impl Into<Box<str>>,
        trailing_trivia: Trivia,
    ) -> Self {
        Self {
            leading_trivia_info,
            kind,
            text: text.into(),
            trailing_trivia,
        }
    }

    pub fn tag<Tag>(self, tag: Tag) -> Token<Tag> {
        Token { lex: self, tag }
    }

    pub fn trailing_trivia_info(&self) -> TriviaInfo {
        self.trailing_trivia.info()
    }
}

impl<Tag> BareToken<Tag> {
    pub fn new(kind: SyntaxKind, tag: Tag, text: impl Into<Box<str>>) -> Self {
        Self {
            kind,
            tag,
            text: text.into(),
        }
    }

    pub fn map_tag<U>(self, f: impl FnOnce(Tag) -> U) -> BareToken<U> {
        BareToken {
            kind: self.kind,
            tag: f(self.tag),
            text: self.text,
        }
    }

    pub fn into_lex(self) -> Lex {
        Lex::new(TriviaInfo::None, self.kind, self.text, Trivia::empty())
    }
}
