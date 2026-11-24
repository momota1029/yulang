# Cycle 393: 同じ source body から event を組み立てる

正本 `eebde455ae8194cd799f10d08cf66a7fcfc2e777`、I-69 inbox `5e202637769e290325b60e4425812e784428f3d7`。S13bbba のみ。不足の出所は [C392 I-69 事実表](https://github.com/momota1029/yulang/blob/7a2e639154daff892e412b3c4a550d4f45feaf0a/notes/design/dots-cycle-392-i69-missing-source-facts.md) と同じ **(a)**。S13bbbb・固定上段・下位一覧の分割は変更しない。

## 今回の実物

`AuthoredBodyFrame393` は現 source registry の実 declaration ordinal と visible の根拠、元の where/body の論理 placement と head capture を受ける。名前を既存の `FrameReadback325.sourceNames` で生成し、同じ declaration と同じ placement から **実 where demand と捕捉 list を直接組み立てる**。元の event の `captures`/children と一致するという外部仮定を置かない。explicit 名をその生成 list から読み、role default は元 demand の位置を読む。

各 original request output は `Fin` ordinal で `Supplies` と actual independent body evaluation から作る。ordinary は C323 の意味を持つ正規 RHS、declared は C392 の bare/tagged native 読み（任意長、値/行 mixed、native nesting、元端点）。全出力を `List.ofFn` で元順に発行し、その列および where/capture の実物から `LiteralLocalEvent` を構成する。既成の receipt や出力の同一性を求めない。各 ordinal の `generated_original_rhs393` は、構成したその event と実出力を既存の source 意味に結び直す。model/solver/release/manifest を使わない。

where 出力だけが定義する binder は `Declaration.Produced` から元の clause と output equation を得る。生成された当該 child の fixed output と、親の RHS が読むその capture point は同一（`generated_where_binder_at_original_output393`）。実際に使った native argument が持つ独立 `ValueBind` / `RowBind` は、同じ point に運ぶ（`generated_where_binder_kinded_rhs393`）。kind を同じ数の slot や別の model から推測するのではない。

## 元の文の残り

1. C386 `ReplayJudgment` は independent source の interface、C384 `ExactSelectedRule384` は key/kids の選択までは残すが、そこから actual kinded head/where binding と元 body の各 source evaluation を一般に生産する rule はまだない。今回の構成の入力は、選択そのもの、任意 source におけるその入力の生産、又は意味を結果から逆向きに結論するものではない。
2. 普通の compiler が現に表せる compound はそのまま使用する。native 平行 branch における bare/tagged app は native application が再帰的に入れ子になっても扱うが、record/join の一般 structural subtree 内部にある nonpoint declared parameter の **literal 型付き RHS** まで既存 `.declared target Pattern Arguments` に表す規則は未実装。ordinary に変換したり、これらの shape を拒否にしたりしない。結果の representation を決め打ちして元 spec の意味を変えない。今の不足は採用済み semantics の formal rule/representation にあり、未決の挙動を見つけたわけではない。

従って S13bbba の全称は未完。C393 の module は actual scoped producer のみで、`Classifies` をこの範囲に制限しない。S13bbbb、Step 2・3、旧 Local/C334、fixture、停止性は触らない。

## 独立の exact Body projection 検証

C323 の `SourceEquation` は元 source body の存在を述べるので、それだけを actual receipt の body の同一性として使わない。下の `nth_generated_receipt_keeps_original_rhs393` は、元 output list の `getElem?` から **その receipt が持つ body、target、literal RHS そのもの**の `BodyWrite393` を得る。ordinary では、元の `receipt.source` を引数とした実 capture と正規化/変換された式を直接得る。別の body へ取り替えない。新しい repo module/fixture は増やさず、Lean 4.35.0 `--stdin --trust=0 -DwarningAsError=true`、四つの検証が `[propext, Classical.choice, Quot.sound]`。

## compound native に必要な規則を既存 ordinary に読み替えない

`declared_native_compound_not_ordinary_fallback393` は actual `SourceMode.declared` の constructor が record/variant/join の内部にあれば、既存 ordinary `translate` はその compound を翻訳しないと証明する。primitive/invariant flag のない実 declared から既存定義だけで導く。root が record/join なら `BodyWrite393` の typed app/tagged app の branch にも該当しない（`current_rule_lacks_structural_declared_rhs393`）。よって scoped rule を unrestricted `Classifies` にそのまま入れることはできない。これは**中間表現・局所規則の不足**であって、当該プログラムが言語仕様上拒否されるという証明ではない。候補順も変えない。

```lean
import Yulang.GeneralDeclarativeI65OriginalBodyEvent393

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceMetadataRows291 (interpretation)

/-- No second choice of body: the original nth generated receipt has
the exact original source and literal output derivation. -/
theorem nth_generated_receipt_keeps_original_rhs393
    {s q} (f : AuthoredBodyFrame393 s q) (each : ∀ i, AuthoredOutput393 f i)
    {ordinal : Nat} {receipt : OrderedReceipt}
    (placed : (emittedEvent393 f each).receipts[ordinal]? = some receipt) :
    BodyWrite393 f receipt.source receipt.requested.target receipt.written := by
  have within : ordinal < (emittedEvent393 f each).receipts.length :=
    (List.getElem?_eq_some_iff.mp placed).1
  have bounded : ordinal < q.demand.outputs.length := by
    simpa only [(emittedEvent393 f each).receiptCount] using within
  let i : Fin q.demand.outputs.length := ⟨ordinal,bounded⟩
  have same := Option.some.inj ((emitted_original_sequence393 f each i).symm.trans placed)
  cases same
  exact (each i).builds

/-- Unlike bare SourceEquation membership, this statement names the
same explicit/default Body held by the literal ordered receipt. -/
theorem ordinary_generated_receipt_is_exact_body393
    {s q} (f : AuthoredBodyFrame393 s q) (each : ∀ i, AuthoredOutput393 f i)
    {ordinal : Nat} {receipt : OrderedReceipt} {row : GeneralDeclarativeHead320.Equation}
    (placed : (emittedEvent393 f each).receipts[ordinal]? = some receipt)
    (ordinary : receipt.written = .ordinary row) :
    (∀ n ∈ (normalize (bodyPattern receipt.source)).variables,
      (f.slots receipt.source n).isSome = true) ∧
    ∃ nf, translate (authoredRegistry s.current).constructors
        (interpretation s.current.environment.source.snapshot)
        (normalize (bodyPattern receipt.source)) = some nf ∧
      row = ⟨receipt.requested.target,logical (bodyCapture q.demand f.names.input receipt.source) .actual nf⟩ := by
  have source := nth_generated_receipt_keeps_original_rhs393 f each placed
  rw [ordinary] at source
  cases source with
  | ordinary supported compiled => exact ⟨supported,_,compiled,rfl⟩

/-- Structural positions in the written normalized source. This
does not say which source forms are accepted or how they are emitted. -/
inductive CompoundSubexpression393 (root : GeneralDeclarationPatterns.Pattern) :
    GeneralDeclarationPatterns.Pattern → Prop where
  | here : CompoundSubexpression393 root root
  | recordPayload : CompoundSubexpression393 root payload →
      CompoundSubexpression393 root (.record label payload tail)
  | recordTail : CompoundSubexpression393 root tail →
      CompoundSubexpression393 root (.record label payload tail)
  | variant : CompoundSubexpression393 root payload →
      CompoundSubexpression393 root (.variant tag payload)
  | joinLeft : CompoundSubexpression393 root first →
      CompoundSubexpression393 root (.join first last)
  | joinRight : CompoundSubexpression393 root last →
      CompoundSubexpression393 root (.join first last)

open GeneralDeclarativeWitnessConstructorModes357 (Environment SourceMode)
open GeneralNominalCenteredHeadMatExpressions (application translateMany)

private theorem translation_none_in_compound393
    (catalogue : GeneralDeclarationPatterns.Constructors)
    (interp : GeneralNominalInspection.Interpretation)
    {sub whole : GeneralDeclarationPatterns.Pattern}
    (occurs : CompoundSubexpression393 sub whole)
    (noneAt : translate catalogue interp sub = none) :
    translate catalogue interp whole = none := by
  induction occurs with
  | here => exact noneAt
  | recordPayload path prior => simp [translate,prior]
  | recordTail path prior =>
    simp [translate,prior]
  | variant path prior => simp [translate,prior]
  | joinLeft path prior => simp [translate,prior]
  | joinRight path prior =>
    simp [translate,prior]

/-- The existing ordinary translator cannot be a fallback for an
arbitrary mixed declared-native compound; this is not a rejection
result for the declarative language. -/
theorem declared_native_compound_not_ordinary_fallback393
    (catalogue : GeneralDeclarationPatterns.Constructors)
    {e : Environment} {ctor : Nat} {ps : List CommonDeclaredNominalInspection.Parameter}
    {args : List GeneralDeclarationPatterns.Pattern} {whole : GeneralDeclarationPatterns.Pattern}
    (source : SourceMode e ctor (.declared ps))
    (occurs : CompoundSubexpression393 (.app ctor args) whole) :
    translate catalogue (interpretation e.source.snapshot) whole = none := by
  apply translation_none_in_compound393 _ _ occurs
  cases source with
  | declared _ noPrimitive noInvariant =>
    have notOrdinary :
        ∀ fs, application catalogue (interpretation e.source.snapshot) ctor fs = none := by
      intro fs
      simp only [application]
      cases catalogue ctor with
      | none => rfl
      | some d =>
        simp [GeneralSourceMetadataRows291.interpretation,noPrimitive,noInvariant]
    simp [translate,notOrdinary]

def StructuralTop393 : GeneralDeclarationPatterns.Pattern → Prop
  | .record .. | .join .. => True
  | _ => False

/-- This is a precise coverage limit of BodyWrite393 itself, not a
language rejection. The scoped producer must not be selected as the
unrestricted source admission rule. -/
theorem current_rule_lacks_structural_declared_rhs393
    {s q} (f : AuthoredBodyFrame393 s q) (body : Yulang.GeneralDictionaryAssociatedProvenance.Body)
    (target : Nat) (written : LiteralWriteSyntax)
    {ctor : Nat} {ps : List CommonDeclaredNominalInspection.Parameter}
    {args : List GeneralDeclarationPatterns.Pattern}
    (source : SourceMode s.current.environment ctor (.declared ps))
    (top : StructuralTop393 (normalize (bodyPattern body)))
    (contains : CompoundSubexpression393 (.app ctor args) (normalize (bodyPattern body))) :
    ¬ BodyWrite393 f body target written := by
  intro proof
  cases proof with
  | ordinary _ got =>
    have failed := declared_native_compound_not_ordinary_fallback393
      (authoredRegistry s.current).constructors source contains
    rw [failed] at got
    contradiction
  | native root _ =>
    rw [root] at top
    exact top
  | tagged root _ =>
    rw [root] at top
    exact top

end Yulang.GeneralDeclarativeI65

#print axioms Yulang.GeneralDeclarativeI65.nth_generated_receipt_keeps_original_rhs393
#print axioms Yulang.GeneralDeclarativeI65.ordinary_generated_receipt_is_exact_body393

#print axioms Yulang.GeneralDeclarativeI65.declared_native_compound_not_ordinary_fallback393

#print axioms Yulang.GeneralDeclarativeI65.current_rule_lacks_structural_declared_rhs393
```
