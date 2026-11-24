# Cycle 387: S13b の同一 event 意味移送と固定先

対象は I-68 の S13b だけ。最上段と元の S13b の文は変更しない。作業開始時の正本 `1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71`（I-68 inbox blob `8fcff32329234b9cc304a919051d1c30e03542aa`）、元の work `89bdb8bbe5fed839fafc1ac2bfdfa3084b9c95b8`。正本には C386 の replay/alignment が入っている。

## 意味の移送ができる範囲

C386 の `LoweredEventLedger s lowered events` が持つ exact event で相互帰納する。左の `TreeMeaningOver P lowered` は各 node で `P` を問う fold で、右の `LedgerMeaning P events` は独立な canonical ledger の fold。子を一つも並べ替えず、出力の空列も node として持つ。もとの `replay` の exact 両側・canonical tree・receipt equality にその同じ ledger の意味を足す。新たな same-event 前提はない。これは任意の局所意味 `P` で成立する実験であり、`P` が言語の型付き意味だと宣言するものではない。

## 元の S13b に残る固定先の意味

- [C386 の literal syntax](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean) `.declared target sourceSyntax arguments` は `Pattern` と original `Argument Nat` 列を保持するが、その型は target の現状態保持を表すものではない。receipt の実証は `Supplies`・ordinal/place/name・`writesTarget`。source/capture から実際に出た一般 typed 中身、および原 authored rows/origins に残ることを別に示す必要がある。
- [C365 の `Fits`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeI65State365.lean#L47): assignment・独立な authoredValues・nativeSyntax。nativeSyntax は origin がある実 slot を制約する。[C357 の `Seen`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeWitnessDeclaredState357.lean#L39) は `List (Ty ⊕ Common.Row)` の評価された点の列を保持する。tag/constructors を含むこの観測を、再帰・非点 `Bounds` まで表す native endpoint の単なる構文観測と同一視しない。下の非干渉補題は、各観測で元の保持事実が無い index を変えても `Fits` が成立することを示す。これは実選択された出力がどのケースで保持されるかについての反例ではない。
- [C368 `TypedWritten / typed_written_all_models`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeI65LiteralTypedBody368.lean#L82) は同じ状態へ残る unary value の `fixedTyped` と metadata/covariant を実際に使う。これを arbitrary row/value vectors や nonpoint のモデル意味に引き延ばせない。[一般の文脈比較](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeWitnessFullIntervals357.lean) は正しい継承 variance の下で、既に与えられた endpoints を比較するが、指定された出力 target に原 RHS を書いた証拠ではない。ordinary の [C324 `one / row_iff`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeNormalizeAssoc324.lean) は actual capture から literal ordinary equation が出る場合に使える。arbitrary native `.declared` の代わりに ordinary へ戻さない。

**切り分け**: S13ba は exact lowerer index で既にある局所意味を matched ledger へ移すだけ。S13bb はその同じ ledger から、原 source/capture・原 where と出力順を残した辞書の意味を作り、同じモデルで literal fixed target の一般の評価・保持を示す。正しい型付き意味を別の ledger の表示一致や `Fits` だけで埋めない。出力をどう分類・受理するか、新しいモード、target を write する順序は決めない。最上段の組立は C380 の文のまま。

## 厳格な Lean 実験（下の bytes）

既存の C386 detach 再構築済み `.olean` および C385 pinned dependency のみを使用。両 C386 入力ソースの Git blobs は `463ad7788cf349e96f30e70c8b7f5cd7dff82a18` と `f4ba39df51a04f157cf980691b33a26ecb3ec862` で実ファイルと照合。Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true` で exit 0。末尾三件の公理はそれぞれ `[propext, Quot.sound]`。新規モジュールとしての登録、別 standalone Audit の import、全体 build と Rust は実行していない。

```lean
import Yulang.GeneralDeclarativeI65CanonicalReplay386

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree)

section
variable [judgment : ReplayJudgment] {s : State}

mutual
/-- Meaning is indexed by the exact lowered tree rather than just by its
dictionary and flattened receipt list. P is a local, same-model predicate
to be supplied by the concrete I-65 semantics, never a classifier. -/
def TreeMeaningOver (P : LiteralEvent s → Prop) :
    {q : Request} → {d : Dictionary} → {written : List OrderedReceipt} →
    GeneralTree s q d written → Prop
  | q, _, _, .node event _ kids => P ⟨q,event⟩ ∧ ForestMeaningOver P kids

def ForestMeaningOver (P : LiteralEvent s → Prop) :
    {qs : List Request} → {ds : List Dictionary} → {written : List OrderedReceipt} →
    GeneralForest s qs ds written → Prop
  | _, _, _, .nil => True
  | _, _, _, .cons head tail => TreeMeaningOver P head ∧ ForestMeaningOver P tail
end

mutual
/-- Independent semantic predicate on the explicit canonical occurrence ledger.
Even a node with no output receipts retains a local semantic obligation. -/
def LedgerMeaning (P : LiteralEvent s → Prop) : LiteralEventTree (s := s) → Prop
  | .node event kids => P event ∧ LedgerForestMeaning P kids

def LedgerForestMeaning (P : LiteralEvent s → Prop) : LiteralEventForest (s := s) → Prop
  | .nil => True
  | .cons first rest => LedgerMeaning P first ∧ LedgerForestMeaning P rest
end

private theorem meaning_on_matched_ledger {P : LiteralEvent s → Prop}
    {q : Request} {d : Dictionary} {written : List OrderedReceipt}
    {lowered : GeneralTree s q d written} {events : LiteralEventTree (s := s)}
    (paired : LoweredEventLedger s lowered events) (meaning : TreeMeaningOver P lowered) :
    LedgerMeaning P events := by
  revert meaning
  exact LoweredEventLedger.rec
    (motive_1 := fun {_ _ _} lowered events _ => TreeMeaningOver P lowered → LedgerMeaning P events)
    (motive_2 := fun {_ _ _} lowered events _ => ForestMeaningOver P lowered → LedgerForestMeaning P events)
    (fun {_ _ _ _} _ _ {_} _ below meaning => by
      exact ⟨meaning.1, below meaning.2⟩)
    (fun _ => True.intro)
    (fun _ _ left right meaning => by
      exact ⟨left meaning.1, right meaning.2⟩)
    paired

variable {q : Request} {d : Dictionary} {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

theorem aligned_same_event_semantics {P : LiteralEvent s → Prop}
    {replay : LiteralTreeFrom tree t lowered}
    (alignment : CanonicalDictionaryReplay replay)
    (meaning : TreeMeaningOver P lowered) :
    ∃ events : LiteralEventTree (s := s),
      ExactReplayEvents replay events ∧
      ExactOrderedOccurrences (dictionaryTree d) events ∧
      orderedLiteralReceipts events = written ∧ LedgerMeaning P events := by
  obtain ⟨events, exactEvents, order, receipts⟩ := alignment.ledger
  exact ⟨events, exactEvents, order, receipts, meaning_on_matched_ledger exactEvents.2 meaning⟩

end

variable {s : State}

/-- A fitting model alone cannot materialize a native typed target not
anchored by one of its own source origins. This is a projection fact,
not a counterexample to an independently justified selected write. -/
theorem fits_change_unanchored_native_s13b {m : Model} (fit : Fits s m)
    (target : Nat) (replacement : Option (CommonRecursiveNominalIntervals.Endpoint Nat))
    (outside : ∀ read ∈ s.origins, read.slot ≠ target) :
    Fits s { m with nativeSyntax := fun i => if i = target then replacement else m.nativeSyntax i } := by
  refine ⟨fit.1, ?_⟩
  intro read present
  simpa only [ite_eq_right (outside read present)] using fit.2 read present

/-- Point payload views are a second projection. A typed source-to-state
theorem must tell which exact original row or native endpoint is retained,
rather than filling an unconstrained projection with a fabricated value. -/
theorem fits_change_unanchored_authored_s13b {m : Model} (fit : Fits s m)
    (target : Nat) (replacement : Option GeneralDeclarativeWitnessDeclaredState357.Value)
    (outside : ∀ row ∈ s.current.visible, row.place ≠ target) :
    Fits s { m with authoredValues := fun i => if i = target then replacement else m.authoredValues i } := by
  refine ⟨⟨fit.1.1,?_⟩,fit.2⟩
  intro row present
  obtain ⟨value,written,tag,name,args⟩ := fit.1.2 row present
  exact ⟨value, by simp only [ite_eq_right (outside row present),written],tag,name,args⟩
end Yulang.GeneralDeclarativeI65

#print axioms Yulang.GeneralDeclarativeI65.aligned_same_event_semantics
#print axioms Yulang.GeneralDeclarativeI65.fits_change_unanchored_native_s13b
#print axioms Yulang.GeneralDeclarativeI65.fits_change_unanchored_authored_s13b
```
