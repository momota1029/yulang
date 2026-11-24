# Cycle 391: S13bbb の原 RHS と同じモデルの固定先

I-68 の `addressed_semantic_ledger_to_dictionary` 一件のみ。正本 `af48e797986d30c200f7c0926f2b2184d4ebf850`、work `756fdb7e3e6d2a22a7f9874d6f9bfaca7e84b1f8`、最新 inbox blob `8fcff32329234b9cc304a919051d1c30e03542aa`。最上段・出現・written の順、S13bbb の元の定理文は変更しない。

## 具体的に検証したもの

- **ordinary**: 元 receipt の `Body`、元出現と出力 ordinal、actual capture、元の requested target を保つ。explicit binder は event の capture list に照合し、default は元 demand の実 position を使う。存在しない default pos に fallback を当てない。default の captured center の式は既存の `positional_exact` とその actual input の存在から導出し、式を追加仮定にしない。actual `translate(normalize(bodyPattern receipt.source))` と `logical(bodyCapture ...)` の exact row がある場合、その same row が current state に retained なら、`SourceEquation` と `Holds m.assignment` を同じモデルで得る。 `C323.SourceEquation` は普通の source rule で checker ではない。
- **native output**: 同じ ordinal の literal `.declared` が持つ arbitrary `Argument Nat` vector、同じ literal target にある actual retained C365 `Origin`、実 kind/mode の `DeclaredComparison` から、同じ `m.nativeSyntax` の観測、context well-formedness、`ContextDerives` を得る。点に直さず、任意の型/行引数・長さ・入れ子を保持する conditional projection。**元 body から endpoint が出ること、又は retention が自動で付くことは証明していない**。
- **authored output**: もう一方の `authoredValues` は `Seen` から実 fixed target で tag/constructor と任意長の ordered evaluated value/row point vector を得る。これは native interval observation とも、同じ target の別の source RHS とも同一視しない。こちらも exact anchor を引数に置く observation theorem。

native 比較の元は [C365 比較](https://github.com/momota1029/yulang/blob/af48e797986d30c200f7c0926f2b2184d4ebf850/lean/Yulang/GeneralDeclarativeI65Comparison365.lean#L83) と [State / Fits](https://github.com/momota1029/yulang/blob/af48e797986d30c200f7c0926f2b2184d4ebf850/lean/Yulang/GeneralDeclarativeI65State365.lean#L38)。普通の元は [C323 SourceEquation](https://github.com/momota1029/yulang/blob/af48e797986d30c200f7c0926f2b2184d4ebf850/lean/Yulang/GeneralDeclarativeAssocRule323.lean#L30)、explicit/default の違いは [C320 bodyCapture](https://github.com/momota1029/yulang/blob/af48e797986d30c200f7c0926f2b2184d4ebf850/lean/Yulang/GeneralDeclarativeOutputs320.lean#L56)。[C383 logical unary tagged](https://github.com/momota1029/yulang/blob/af48e797986d30c200f7c0926f2b2184d4ebf850/lean/Yulang/GeneralDeclarativeI65LogicalNominalOutput383.lean#L18) は actual source equation/binder→exact tagged observation が明示された狭い例。一般の typed body をそれに縮めない。

## 残る補題を独立にする

1. `addressed_meaning_to_exact_source_rhs`: 同じ addressed tree の each event で、original explicit/default body と exact captures / actual ordinal が、literal output payload（ordinary row 又は exact declared arguments）を導くこと。単に `Supplies`、typed syntax の保存、constructor 比較だけでは RHS を説明しない。ここは未証明。
2. `exact_rhs_to_dictionary_in_same_model`: 原 RHS の関係と same event の意味から、元の ordinal/target の retained semantics を実際の同一 model で読み、元の written の列を保つ canonical `DictionaryEvidence` を構成すること。ordinary と各正当な retained observation の projection は下のように機械検証済み。全宣言・全混在 tree を結ぶのは未証明。

親の元の三前提から 1 を得て 2 を呼ぶ。他の node から `Fits` や payload を挿入せず、同じ位置と state を使う。受理条件や tag / native carrier の新しい同一視を決めず、旧 solver journal/release も宣言的状態へ入れない。

## 厳格検証

Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true` を C390 exact replay の依存で実行し exit 0。ordinary と authored は `[propext, Quot.sound]`、native は既存比較を通じ `[propext, Classical.choice, Quot.sound]`。default capture は `[propext]`、元の三前提の合成型チェックは `[propext, Quot.sound]`。合成チェックだけには両未証明義務を引数にする。依存は C388/C390 の exact replay。下の conditional cuts は元の S13bbb の完了ではない。新規 module、別 import 監査、全体 build または Rust を実行した扱いにしない。

```lean
import Yulang.GeneralDeclarativeI65AddressedReplay390
import Yulang.GeneralDeclarativeI65SameEventSemantics388
import Yulang.GeneralDeclarativeAssocRule323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal Value authoredRegistry Seen evaluate)
open GeneralDeclarativeEntailment320 (Holds literal)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture positional_exact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRecursiveNominalIntervals (Argument ContextWellFormed)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)

/-- No out-of-range role-argument fallback is claimed as actual support.
Explicit names use the original event capture list; default names use
the original requested positional arguments, not declaration binders. -/
def OriginalBodyCapture {s : State} {q : Request}
    (event : LiteralLocalEvent s q) (receipt : OrderedReceipt) (capture : Nat → Capture) : Prop :=
  ∀ name ∈ (bodyPattern receipt.source).variables,
    match receipt.source with
    | .explicit _ => event.captures.lookup name = some (capture name)
    | .default _ _ _ => ∃ argument, q.demand.arguments[name]? = some argument

/-- The literal default uses the existing role-position convention.
The actual stored argument supplies the center; the proof does not
require a solver capture or a new fallback. -/
theorem original_default_capture_uses_actual_center
    {s : State} {q : Request} {event : LiteralLocalEvent s q} {receipt : OrderedReceipt}
    {capture : Nat → Capture} {role name : Nat} {rhs : Roles.Term}
    (body : receipt.source = .default role name rhs)
    (binding : OriginalBodyCapture event receipt capture)
    {position : Nat} (used : position ∈ (bodyPattern receipt.source).variables) :
    ∃ argument, q.demand.arguments[position]? = some argument ∧
      bodyCapture q.demand capture receipt.source position =
        ⟨argument.center,argument.center,argument.center⟩ := by
  have supported := binding position used
  rw [body] at supported
  obtain ⟨argument,atPosition⟩ := supported
  exact ⟨argument,atPosition,by simpa only [body,bodyCapture] using positional_exact q.demand atPosition⟩

/-- An occurrence-specific ordinary payload equation reads the
original Body and its actual variables. Capture agreement and
retention are not supplied by the receipt metadata alone. -/
theorem retained_exact_ordinary_rhs_same_model
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    {i : Nat} {receipt : OrderedReceipt} {row : Equation}
    (position : event.receipts[i]? = some receipt)
    (written : receipt.written = .ordinary row)
    (capture : Nat → Capture)
    (bindings : OriginalBodyCapture event receipt capture)
    (payload : ∃ nf,
      translate (authoredRegistry s.current).constructors
        (interpretation s.current.environment.source.snapshot)
        (normalize (bodyPattern receipt.source)) = some nf ∧
      row = ⟨receipt.requested.target,logical (bodyCapture q.demand capture receipt.source) .actual nf⟩)
    (kept : row ∈ s.current.ordinary.equations)
    (m : Model) (fit : Fits s m) :
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
      q.demand.outputs[i]? = some receipt.requested ∧
      row.left = receipt.requested.target ∧
      OriginalBodyCapture event receipt capture ∧
      SourceEquation (authoredRegistry s.current)
        (interpretation s.current.environment.source.snapshot) q.demand event.declaration capture row ∧
      Holds m.assignment row := by
  obtain ⟨occurrence, ordinal, request, supplies, atTarget⟩ := event.receiptAt i receipt position
  have fixed : row.left = receipt.requested.target := by
    simpa only [OrderedReceipt.writesTarget,written] using atTarget
  exact ⟨occurrence,ordinal,request,fixed,bindings,
    ⟨receipt.requested,List.mem_of_getElem? request,receipt.source,supplies,payload⟩,
    literal kept m.assignment fit.1.1⟩

/-- Exact native retention needs an already justified endpoint with
the actual arbitrary value/row vector, and an origin at the literal
fixed target. This interprets it in the same full contextual model;
it does not derive the endpoint from an authored RHS. -/
theorem retained_exact_native_rhs_same_model
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    {i : Nat} {receipt : OrderedReceipt}
    (position : event.receipts[i]? = some receipt)
    {target constructor : Nat} {syntaxTree : Pattern} {args : List (Argument Nat)}
    (written : receipt.written = .declared target syntaxTree args)
    {origin : Origin} (kept : origin ∈ s.origins)
    (atTarget : origin.slot = target)
    (atEndpoint : origin.endpoint = .nominal constructor args)
    (coherence : DeclaredComparison s.current.environment s.current.ordinary s.modes false
      (.nominal constructor args) (.nominal constructor args))
    (m : Model) (fit : Fits s m) :
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
      q.demand.outputs[i]? = some receipt.requested ∧
      m.nativeSyntax receipt.requested.target = some (.nominal constructor args) ∧
      ContextWellFormed s.modes false (.nominal constructor args) ∧
      ContextDerives s.modes m.assignment false (.nominal constructor args) (.nominal constructor args) := by
  obtain ⟨occurrence, ordinal, request, _, writes⟩ := event.receiptAt i receipt position
  have fixed : target = receipt.requested.target := by
    simpa only [OrderedReceipt.writesTarget,written] using writes
  have retained := fit.2 origin kept
  rw [atTarget,fixed,atEndpoint] at retained
  obtain ⟨kind,_,meaning⟩ := in_same_model coherence m.assignment fit.1.1
  exact ⟨occurrence,ordinal,request,retained,kind,meaning⟩

/-- The independent authored-value observation genuinely retains an
arbitrary ordered value/row list, without coercing it into a native
nonpoint endpoint. The actual source and literal ordinal are not
reconstructed from the equality of model values. -/
theorem retained_authored_vector_same_model
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    {i : Nat} {receipt : OrderedReceipt}
    (position : event.receipts[i]? = some receipt)
    {payload : AuthoredNominal} (kept : payload ∈ s.current.visible)
    (fixed : payload.place = receipt.requested.target)
    (m : Model) (fit : Fits s m) :
    receipt.occurrence = q.occurrence ∧ receipt.ordinal = i ∧
      q.demand.outputs[i]? = some receipt.requested ∧
      ∃ v : Value, m.authoredValues receipt.requested.target = some v ∧
        v.tag = payload.tag ∧ v.name = payload.name ∧ v.arguments = payload.arguments.map (evaluate m.assignment) := by
  obtain ⟨occurrence,ordinal,request,_,_⟩ := event.receiptAt i receipt position
  obtain ⟨v,seen,tag,name,arguments⟩ := fit.1.2 payload kept
  exact ⟨occurrence,ordinal,request,v,fixed ▸ seen,tag,name,arguments⟩

/-- Only the composition type is tested: both genuine semantic
obligations remain required. The original three inputs stay fixed. -/
theorem s13bbb_split_composition_typecheck
    [ReplayJudgment] {s : State} {m : Model} {q : Request}
    {d : CommonRoleOutermostResolver.Dictionary} {events : LiteralEventTree (s := s)}
    {written : List OrderedReceipt}
    (localSem : Model → LiteralEvent s → Prop) (source : LiteralEvent s → Prop)
    (dict : Model → Request → CommonRoleOutermostResolver.Dictionary → Prop)
    (extractRhs : AddressedDictionaryEvents s q d events →
      LedgerMeaning (localSem m) events → LedgerMeaning source events)
    (assemble : AddressedDictionaryEvents s q d events →
      orderedLiteralReceipts events = written → LedgerMeaning (localSem m) events →
      LedgerMeaning source events → dict m q d)
    (addressed : AddressedDictionaryEvents s q d events)
    (outputs : orderedLiteralReceipts events = written)
    (semantic : LedgerMeaning (localSem m) events) :
    dict m q d :=
  assemble addressed outputs semantic (extractRhs addressed semantic)

end Yulang.GeneralDeclarativeI65

#print axioms Yulang.GeneralDeclarativeI65.retained_exact_ordinary_rhs_same_model
#print axioms Yulang.GeneralDeclarativeI65.retained_exact_native_rhs_same_model
#print axioms Yulang.GeneralDeclarativeI65.retained_authored_vector_same_model

#print axioms Yulang.GeneralDeclarativeI65.original_default_capture_uses_actual_center
#print axioms Yulang.GeneralDeclarativeI65.s13bbb_split_composition_typecheck
```
