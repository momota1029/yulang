# C431: 受理した証人の元 row ordinal は実読みにそのまま残る

公開済み R15 `04be83be1baa9d1426f3598cb7a7c0ecf740f9cf` の exact Git bytes を読み直した production 環境で、下記を新しい空 cwd の独立ファイルに置いて `lean --trust=0 -DwarningAsError=true`（4.35.0）で実行、exit 0。4件すべて標準公理のみ。追加レビュー用の再現コードで、統合対象の Lean path や実行版は変更しない。

任意の p/r/w について新規構造分岐が `true` なら、読んだ元行の ordinal がデータ証人の originalWhereRow と同一であり、表示は同じ実 packet に等しい。候補は元 graph に実際に retained された行で、同値な別値を選ぶ証明ではない。物理 allocator の一般的な一意性は主張しない。

```lean
import Yulang.GeneralDeclarativeI65I74StructuralWhereEntry431
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
theorem original_row_does_not_change_wire_address431
    {s q} {f : AuthoredBodyFrame393 s q} {w} {a}
    (seen : readOriginalRecordArgument427 f w = some a) :
    a.rowOrdinal = w.rowOrdinal := by
  unfold readOriginalRecordArgument427 at seen
  split at seen
  · contradiction
  · split at seen
    · split at seen
      · split at seen
        · contradiction
        · split at seen
          · split at seen
            · contradiction
            · dsimp only at seen
              split at seen
              · split at seen
                · have e := Option.some.inj seen
                  rw [← e]
                · contradiction
              · contradiction
          · contradiction
      · contradiction
    · contradiction
#print axioms original_row_does_not_change_wire_address431
end Yulang.GeneralDeclarativeI65.StructuralWhere427

namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
theorem read_pair_retains_exact_wire_address431
    {s q} {w : PositivePairWire427} {p}
    (seen : readOriginalPositivePair427 s q w = some p) :
    p.original.rowOrdinal = w.originalWhereRow := by

  unfold readOriginalPositivePair427 at seen
  dsimp only at seen
  split at seen
  · obtain ⟨root,_,hroot⟩ := Option.bind_eq_some_iff.mp seen
    obtain ⟨rootChecked,_,hchecked⟩ := Option.bind_eq_some_iff.mp hroot
    split at hchecked
    · split at hchecked
      · obtain ⟨row,_,hrow⟩ := Option.bind_eq_some_iff.mp hchecked
        obtain ⟨original,hs,horiginal⟩ := Option.bind_eq_some_iff.mp hrow
        obtain ⟨child,_,hchild⟩ := Option.bind_eq_some_iff.mp horiginal
        split at hchild
        · split at hchild
          · split at hchild
            · obtain ⟨parentRival,_,hp⟩ := Option.bind_eq_some_iff.mp hchild
              obtain ⟨childRival,_,hc⟩ := Option.bind_eq_some_iff.mp hp
              split at hc
              · split at hc
                · have eq := Option.some.inj hc
                  rw [← eq]
                  exact original_row_does_not_change_wire_address431 hs
                · contradiction
              · contradiction
            · contradiction
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · contradiction
#print axioms read_pair_retains_exact_wire_address431
end Yulang.GeneralDeclarativeI65.StructuralWhere427

namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
open StructuralWhere427
theorem successful_C15_read_retains_wire_row431 {p w a}
    (seen : readOriginal p w = some a) :
    a.pair.original.rowOrdinal = w.selected.originalWhereRow := by
  unfold readOriginal at seen
  obtain ⟨pair,entered,h⟩ := Option.bind_eq_some_iff.mp seen
  split at h
  · have exactPair := Option.some.inj h
    rw [← exactPair]
    exact read_pair_retains_exact_wire_address431 entered
  · contradiction

theorem accepted_public_C15_witness_names_actual_original_row431 {p r w}
    (seen : check p r (.originalStructuralWhere w) = true) :
    ∃ a, readOriginal p w = some a ∧
      a.pair.original.rowOrdinal = w.selected.originalWhereRow ∧
      r = a.report := by
  obtain ⟨a,read,same⟩ := executable_report_is_original431 _ _ _ seen
  exact ⟨a,read,successful_C15_read_retains_wire_row431 read,same⟩
#print axioms successful_C15_read_retains_wire_row431
#print axioms accepted_public_C15_witness_names_actual_original_row431
end Yulang.GeneralDeclarativeI65.I72.StructuralWhere431
```
