# Cycle 389: S13bb の辞書出現と型付き固定先

I-68 の `exact_semantic_ledger_to_dictionary` だけを対象とする。I-68 inbox `8fcff32329234b9cc304a919051d1c30e03542aa`、正本 `784ece5c5686a56d7959fb6e51bc0a0374b00cb5`、元の work `7001ddf34033176cc8b8b81a62696d2a5cabc62d`。最上段・旧 S13bb の定理文と引数を変更しない。

## S13bba: 実辞書と実要求の位置

C388 の `ExactReplayEvents replay events` の lowered 側から、同じ source event と guard を使って `AddressedDictionaryEvents s q d events` を構成できる。これは Tree の key だけの比較とは異なり、元の full `Request`、実 `Dictionary.node` と子辞書列、元の `event.kids`、元の occurrence と ordinal の receipt schema を同じ node に保つ。where の子を再選出しない。実辞書へ移したあとでも、canonical diagnostic 順を独立に導ける。局所モデルを呼ばない。

## S13bbb: 同一モデルの固定出力証拠

`LiteralLocalEvent.receiptAt` は元の request/ordinal/target と原宣言の `Supplies` を保存するが、literal typed 構文および任意長の引数を **その body と capture から評価した** ことは述べていない。下の一般補題で、同じ target に任意の `Pattern` と `Argument Nat` 列を代入した receipt でも、このフィールド結論はそのまま成立することを検証した。これは新しい選択 event を作るものではない。独立 source guard は差し替え後の receipt に移していないので、承認済み言語の反例や選択の非一意性の証明ではない。

`Pattern` は record・variant・join を含み、native `Endpoint` は普通の `TyTerm` と nominal の入れ子を区別する。C365 `authoredValues` は任意長の点列を扱えても、`nativeSyntax` のままの非点区間や exact tagged output と同一ではない。型/行・点/非点の区別を落とす射影を既成の解として採らない。受理形や組合せの新しい禁止を導いたわけではない。

不足する二つの関係を混同しない:

1. **入力の解釈と原 RHS の関係**。同一の原宣言と `Supplies`、元の where/出力 ordinal、用いた actual capture を経て、固定先に記録された ordinary equation 又は declared type/row/vector が本当にその body を表すこと。explicit の宣言 binder と default の role 位置を同一視しない。[C320 `bodyPattern/bodyCapture`](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeOutputs320.lean#L56) と [C324 ordinary `row_iff`](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeNormalizeAssoc324.lean) は普通の行を実際に説明する。[C383 tagged unary](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeI65LogicalNominalOutput383.lean#L18) は原 RHS・実捕捉中心から exact nominal row を与えるが、非点、入れ子、任意の型/行引数を一般に生成しない。
2. **同じ状態・モデルで書き込み先に残る関係**。C387 の非干渉で分かった通り、`Fits` が制約するのは retained row / source origin がある先。元の ordinal と target の両方を保つ同一状態の事実が必要。[C368 `typed_written_all_models`](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeI65LiteralTypedBody368.lean#L114) は tagged unary point の保持を実際に使う。[C365 `in_same_model`](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeI65Comparison365.lean#L90) は元の bounds と mode のまま同一 assignment で比較できるが、その端点を持つ typed 出力が当該固定先に現れることは示さない。既存 [C363 同一モデル木](https://github.com/momota1029/yulang/blob/784ece5c5686a56d7959fb6e51bc0a0374b00cb5/lean/Yulang/GeneralDeclarativeWitnessSelectedSourceMeaning363.lean#L95) も scoped `Complete` の証明で、任意の ledger の保持とは違う。

元の S13bb は `addressed_semantic_ledger_to_dictionary (exact_replay_ledger_addresses eventMatch) outputs semantic`。canonical 順は `addressed_replay_has_canonical_order` で再び得られ、元の明示前提は消さない。S13bbb は concrete `GeneralLocalMeaning s m` を要求し、任意の P や `Fits` だけから書き込み済みの型を推測しない。proof-erased 存在を実行データへ展開しない。将来の型付き解釈には、新しい受理条件、書き込み順、solver の release/manifest を決めず、実 source/local semantics の一般の証明を使う。

## 厳格検証した Lean 実験

C388 の独立 replay を importし、Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true` exit 0。この段階は下の exact structural kernel と制約フィールドの計算だけで、モジュール登録や S13bb の完了ではない。依存公理は addresses と receipt field lemma が各 `[propext]`、canonical order と四前提の合成型検証は各 `[propext, Quot.sound]`。合成型検証は第二補題を引数に置く明示試験で、concrete な型付き意味を実装しない。

```lean
import Yulang.GeneralDeclarativeI65SameEventSemantics388

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree dictionaryForest)

mutual
/-- The actual dictionary constructors are paired against full
request occurrences. Every child is the same finite lowered child
of a source where request, not an unrelated event with the same key. -/
inductive AddressedDictionaryEvents [judgment : ReplayJudgment] (s : State) :
    Request → Dictionary → LiteralEventTree (s := s) → Prop where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩) :
      AddressedDictionaryForest s event.kids ds events →
      AddressedDictionaryEvents s q (.node event.declaration.id ds) (.node ⟨q,event⟩ events)

inductive AddressedDictionaryForest [judgment : ReplayJudgment] (s : State) :
    List Request → List Dictionary → LiteralEventForest (s := s) → Prop where
  | nil : AddressedDictionaryForest s [] [] .nil
  | cons :
      AddressedDictionaryEvents s q d first →
      AddressedDictionaryForest s qs ds rest →
      AddressedDictionaryForest s (q :: qs) (d :: ds) (.cons first rest)
end

section
variable [judgment : ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

/-- Addresses refine rather than replace the canonical diagnostic shape. -/
theorem addressed_replay_has_canonical_order
    {events : LiteralEventTree (s := s)}
    (addressed : AddressedDictionaryEvents s q d events) :
    ExactOrderedOccurrences (dictionaryTree d) events := by
  exact AddressedDictionaryEvents.rec
    (motive_1 := fun _ d events _ => ExactOrderedOccurrences (dictionaryTree d) events)
    (motive_2 := fun _ ds events _ => ExactOrderedForest (dictionaryForest ds) events)
    (fun {_ _ _} event _ _ below => by
      simpa only [dictionaryTree] using ExactOrderedOccurrences.node ⟨_,event⟩ below)
    (by simpa only [dictionaryForest] using (ExactOrderedForest.nil (s := s)))
    (fun _ _ first rest => by
      simpa only [dictionaryForest] using ExactOrderedForest.cons first rest)
    addressed

private theorem lower_ledger_exact_request_addresses
    {events : LiteralEventTree (s := s)} (matched : LoweredEventLedger s lowered events) :
    AddressedDictionaryEvents s q d events := by
  exact LoweredEventLedger.rec
    (motive_1 := fun {q d _} _ events _ => AddressedDictionaryEvents s q d events)
    (motive_2 := fun {qs ds _} _ events _ => AddressedDictionaryForest s qs ds events)
    (fun {_ _ _ _} event guard {_} _ kids => .node event guard kids)
    .nil
    (fun _ _ first rest => .cons first rest)
    matched

theorem exact_replay_ledger_addresses
    {replay : LiteralTreeFrom tree t lowered} {events : LiteralEventTree (s := s)}
    (eventMatch : ExactReplayEvents replay events) :
    AddressedDictionaryEvents s q d events :=
  lower_ledger_exact_request_addresses eventMatch.2

/-- Typecheck the original four-premise assembly with the selected
second obligation named. This does not instantiate its concrete
model interpretation or promote receiver shape to semantics. -/
theorem s13bb_split_composition_typecheck
    (localMeaning : Model → LiteralEvent s → Prop)
    (dictionaryMeaning : Model → Request → Dictionary → Prop)
    (m : Model)
    {replay : LiteralTreeFrom tree t lowered} {events : LiteralEventTree (s := s)}
    (assemble : AddressedDictionaryEvents s q d events →
      orderedLiteralReceipts events = written →
      LedgerMeaning (localMeaning m) events → dictionaryMeaning m q d)
    (eventMatch : ExactReplayEvents replay events)
    (_canonical : ExactOrderedOccurrences (dictionaryTree d) events)
    (outputs : orderedLiteralReceipts events = written)
    (semantic : LedgerMeaning (localMeaning m) events) :
    dictionaryMeaning m q d := by
  exact assemble (exact_replay_ledger_addresses eventMatch) outputs semantic

end
/-- The literal receipt indexing rules do not compare original and newly
supplied declared payloads. This is a rule-field calculation, not a
second accepted event: the independent event guard is not transported. -/
theorem declared_receipt_index_fields_do_not_check_payload
    {s : State} {q : Request} (event : LiteralLocalEvent s q)
    (i : Nat) (r : OrderedReceipt) (located : event.receipts[i]? = some r)
    (target : Nat) (original replacement : GeneralDeclarationPatterns.Pattern)
    (before after : List (CommonRecursiveNominalIntervals.Argument Nat))
    (writtenAs : r.written = .declared target original before) :
    let changed : OrderedReceipt := {r with written := .declared target replacement after}
    changed.occurrence = q.occurrence ∧ changed.ordinal = i ∧
      q.demand.outputs[i]? = some changed.requested ∧
      GeneralDictionaryAssociatedProvenance.Supplies
        (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).roles
        event.declaration changed.requested.name changed.source ∧ changed.writesTarget := by
  obtain ⟨path, ordinal, provided, supplies, fixed⟩ := event.receiptAt i r located
  exact ⟨path, ordinal, provided, supplies, by
    simpa only [OrderedReceipt.writesTarget, writtenAs] using fixed⟩

end Yulang.GeneralDeclarativeI65

#print axioms Yulang.GeneralDeclarativeI65.exact_replay_ledger_addresses

#print axioms Yulang.GeneralDeclarativeI65.declared_receipt_index_fields_do_not_check_payload

#print axioms Yulang.GeneralDeclarativeI65.addressed_replay_has_canonical_order

#print axioms Yulang.GeneralDeclarativeI65.s13bb_split_composition_typecheck
```
