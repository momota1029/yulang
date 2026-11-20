import Yulang.GeneralSourceRoleCstSourceExtent293

/-! The active Rust SyntaxKind labels, at the audited snapshot. Unknown labels
are declined; known opaque labels preserve their slot rather than disappearing. -/
namespace Yulang.GeneralSourceRoleCstWireTags293
open GeneralSourceRoleCstTree293 (Kind)

def labels : List String :=
  ["Root","Missing","Error","UseDeclaration","UseTree",
   "UsePath","UseGroup","UseGlob","UseAlias","UseQualifiers",
   "UseVersion","UseAnchor","UseExclusion","UseExclusionGroup","OperatorHeader",
   "OperatorName","BindingPower","BindingStatement","BindingHeader","BindingBody",
   "ModDeclaration","StructDeclaration","StructField","EnumDeclaration","EnumVariant",
   "ErrorDeclaration","TypeDeclaration","RoleDeclaration","ImplDeclaration","ImplDescription",
   "CastDeclaration","CastPattern","CastTarget","CastBody","ActDeclaration",
   "DeclarationCompanion","DeclarationCompanionIndentedBody","DocCommentDeclaration","DocLinePrefix","DocBlockOpen",
   "DocBlockClose","YmDoc","YmSection","YmImplicitSection","YmExplicitSection",
   "YmHeading","YmSectionClose","YmText","YmHeadingMarker","YmListMarker",
   "YmQuoteFenceMarker","YmQuotePrefix","YmFenceMarker","YmBlankLine","YmList",
   "YmListItem","YmListItemBody","YmQuoteBlock","YmCodeFence","YmCodeFenceInfo",
   "YmCodeFenceText","YmYulangCodeCell","YmParagraph","YmCommand","YmCommandArgs",
   "YmCommandBody","YmDoCapture","YmMy","YmMyBindingHead","YmMyExpressionBody",
   "YmUse","YmIfChain","YmIf","YmIfCondition","YmElsif",
   "YmElsifCondition","YmElse","YmBackslash","YmBangLBracket","YmStrongMarker",
   "YmEmphasisMarker","YmInlineRef","YmInlineGroup","YmInlineLink","YmInlineImage",
   "YmInlineApply","YmInlineApplyHead","YmInlineApplyArgs","YmYulangArgs","YmDocArg",
   "YmEmphasis","YmStrong","ForStatement","ForLabel","ForIterable",
   "DeclarationTypeParameterList","DerivesClause","TestModuleMarker","IntegerLiteral","IdentifierExpression",
   "ParenthesizedExpression","IfExpression","CaseExpression","CatchExpression","CaseLabel",
   "CatchLabel","CaseScrutinee","CatchScrutinee","CaseBlock","CatchBlock",
   "CaseArm","CatchArm","CaseGuard","CatchGuard","CaseArmSeparator",
   "CatchArmSeparator","BracedStatementBlockExpression","Pattern","IdentifierPattern","IntegerPattern",
   "SymbolPattern","ParenthesizedPattern","ListPattern","ListPatternSpreadItem","RecordPattern",
   "RecordPatternField","RecordPatternSpreadItem","TypeExpression","ParenthesizedTypeGroup","NamedRecordType",
   "TypeRecordField","ForallType","ForallTypeBinder","EffectRowType","BracketRow",
   "PolymorphicVariantType","PolymorphicVariantTag","PolymorphicVariantPayload","TypePathTail","TypeCallTail",
   "TypeApplyArgument","TypeArrowTail","PatternAliasTail","PatternAlternationTail","PatternTypeAnnotation",
   "IfArm","ElseArm","Condition","OperatorChain","ColonApplicationTail",
   "WithBodyTail","CallTail","IndexTail","IndexItem","ProjectionTupleTail",
   "ProjectionRecordTail","ProjectionRecordSpreadItem","FieldTail","PathTail","MlArgument",
   "IndentedStatementBlock","Statement","BlockStatementSeparator","PrefixOperatorUse","InfixOperatorUse",
   "SuffixOperatorUse","NullfixOperatorUse","UseKw","ModKw","StructKw",
   "EnumKw","ErrorKw","TypeKw","RoleKw","ImplKw",
   "CastKw","ActKw","ForKw","InKw","RealmKw",
   "BandKw","AsKw","WithoutKw","WithKw","DerivesKw",
   "FromKw","ViaKw","InfixKw","MyKw","PubKw",
   "OurKw","LazyKw","PrefixKw","SuffixKw","NullfixKw",
   "IfKw","CaseKw","CatchKw","WhereKw","ElsifKw",
   "ElseKw","Identifier","SigilIdentifier","Integer","Version",
   "Dot","DotDot","ColonColon","Slash","Colon",
   "Comma","Star","LParen","RParen","LBrace",
   "RBrace","LBracket","RBracket","Equals","Semicolon",
   "Apostrophe","Backslash","Pipe","Arrow","Operator",
   "Whitespace","Newline","LineComment","BlockComment","Unknown",
   "StringLiteral","StringEscape","StringInterpolation","StringInterpolationBody","RuleExpression",
   "RuleBody","RuleAlternation","RuleSequence","RuleItem","RuleCapture",
   "RuleQuantifier","RuleField","RulePath","RuleCall","RuleIndex",
   "RuleLiteral","RuleLiteralInterpolation","RuleLazyCapture","StringStart","StringEnd",
   "StringText","StringEscapeLead","StringEscapeSimple","StringEscapeUnicodeStart","StringEscapeUnicodeHex",
   "StringEscapeUnicodeEnd","StringInterpolationPercent","StringInterpolationFormatText","StringInterpolationOpenBrace","StringInterpolationCloseBrace",
   "RuleKw","RuleQuantifierToken","RuleLiteralStart","RuleLiteralEnd","RuleLiteralText",
   "RuleLiteralOpenBrace","RuleLiteralCloseBrace","RuleLiteralColon","Invalid","TypeCallClose",
   "AssignmentTail","TypeAnnotationTail","RecordPatternSeparator","RecordPatternForeignClose","ExpressionDelimitedSeparator",
   "ExpressionDelimitedForeignClose","StructFieldForeignClose","NamedRecordTypeSeparator","NamedRecordTypeClose","PolymorphicVariantForeignClose",
   "UseGroupForeignClose","TypeDelimitedForeignClose","PatternMlApplicationTail","PatternPathTail","PatternCallTail",
   "PatternFieldTail","WhereClause","SymbolExpression","LambdaExpression","FloatLiteral",
   "Float","ListExpression","ListExpressionSpreadItem","RangePattern","RecordExpressionSpreadItem",
   "PostfixIfExpression","NestingTooDeep"]

def compact : String → Kind
  | "Root" => .root
  | "RoleDeclaration" => .role
  | "TypeExpression" => .head
  | "TypeApplyArgument" => .argument
  | "IndentedStatementBlock" => .indented
  | "Statement" => .statement
  | "TypeDeclaration" => .typeDecl
  | "BindingStatement" => .binding
  | "RoleKw" => .roleKw
  | "PubKw" => .pubKw
  | "OurKw" => .ourKw
  | "MyKw" => .myKw
  | "TypeKw" => .typeKw
  | "Colon" => .colon
  | "Equals" => .equals
  | "Identifier" => .identifier
  | "SigilIdentifier" => .sigilIdentifier
  | "Whitespace" => .whitespace
  | "Newline" => .whitespace
  | "LineComment" => .lineTrivia
  | "BlockComment" => .lineTrivia
  | "Missing" => .missing
  | "Invalid" => .invalid
  | "Error" => .error
  | "NestingTooDeep" => .error
  | "Unknown" => .error
  | _ => .other

def kind (label : String) : Option Kind :=
  if label ∈ labels then some (compact label) else none

theorem kind_exact (label : String) (k : Kind) :
    kind label = some k ↔ label ∈ labels ∧ compact label = k := by
  by_cases h : label ∈ labels <;> simp [kind,h]

theorem closed_controls :
    kind "NestingTooDeep" = some .error ∧ kind "Unknown" = some .error ∧
    kind "Invalid" = some .invalid ∧ kind "LineComment" = some .lineTrivia ∧
    kind "BindingPower" = some .other ∧ kind "MadeUpCstKind" = none := by decide

end Yulang.GeneralSourceRoleCstWireTags293
