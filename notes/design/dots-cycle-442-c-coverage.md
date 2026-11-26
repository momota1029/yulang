# C442 の C coverage（三条件の照合）

| 行 | 状態 | source と証拠 |
| --- | --- | --- |
| C22 | **未完** | §6.1/6.3 + §4.6 の row/value nominal associated RHS。元の one-output `ref 'e 'a` authored event と nonflattened B6 receipt は再現した。固定先の値が全 original Fits でその RHS に等しいことは、同一 State の二モデルで反例。独立 typed `Descriptor` が既に保持されている別 graph の同一 assignment では正しいが、現行 canonical State/producer がその Models を供給する経路は未確認。R22／新 public check／同外形 check_sound は足していない。 |

C01–C21 は既存 scoped 実装を変更していない。C21 の literal `ref _ int`／rank-2 や一般完全性が済んだという集計ではない。[前の一覧](dots-cycle-441-c-coverage.md) と [今周の保持設計](dots-cycle-442-c22-retention-next.md)。

**残り 1 行 (C22)。**
