この周に閉じた C の行: C03 / X9「`Show (list 'a)` の実 `where Show 'a` の子で K2 を報告する」（`dictionary_sound_R3`, `WhereCycle411.check_sound`、work/dots-main で三条件を検証）。

## 対象と結果

- 仕様 §6.3 の `impl Show (list 'a) where Show 'a` / `show [loop 1]`。元の親 list は構造的な循環の上にない。literal binder で捕捉した再帰型 `ν = :tag ν` が、実 where 一つによって初めて子の需要 `Show ν` になる。元の親位置 `[27]` と実 where ordinal 0 から `[27,0]` が得られる。報告は `selected 88 [rejected]`（verdict `rejected`、書込み空）。裸の親根 K2 や親の選択成功ではない。checker の true はこの正確な拒否報告の証人が検査を通ったことを示す。
- 見えている唯一の宣言、宣言済み invariant list、元の一引数点、同一 role の literal 変数 where 一つ、空出力に限定。[C 一覧](../design/dots-cycle-411-c-coverage.md) の C03 だけが完了。[境界と検証](../design/dots-cycle-411-c03-verification.md)。

## I-74 の三条件

1. [whereListLocal411](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListRule411.lean#L133) は checker・子の循環証人・モデルの存在に依らず、元候補の照合と実宣言を使う局所規則。これを `R2` に足した `R3` について、任意の State・元の需要・辞書で `Classifies R3 s q (.selected d)` なら、同じ State の任意 fitting model で固定 `DictionaryEvidence s m q d`（[dictionary_sound_R3](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListRule411.lean#L154)）。旧 `R2` は当該親の局所選択を表さないことも示した。
2. [WhereCycle411.check](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListEntry411.lean#L204) の追加分岐の witness data は元親 origin ordinal・escape palette・既存 Cycle350 証人のみ。実 source から role、where clause、束縛、point を確かめ、[元 event の子](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListEntry411.lean#L113)を得る。親根の安全と checked lexical scope・Paterson 条件を照合する。raw graph を support で濾過せず **実 child demand** に旧 raw cycle check を実行する。旧 `List410.check` はそのまま。旧・新は同時に通らず、[成功 witness の exact Result は一意](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListPriority411.lean#L172)。
3. [WhereCycle411.check_sound](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListEntry411.lean#L245) は true から同じ元 Problem と exact 報告の `ClassifiedAs`、同じ State の **全 fitting model** の `ReportEvidence`。木・空の write・元の子順を保持する。[一つの実 trace をモデルの全称より前に固定](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListFidelity411.lean#L53)。さらに、今回の branch が通った fitting State では [全 R3 trace が当の親と raw 子の木になり、別の declarative verdict はない](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Yulang/GeneralDeclarativeI65I74WhereListCoherence411.lean#L128)。追加事実は fitting nativeSyntax が元の同一 slot に一つの literal endpoint を与えることだけを使い、checker はモデルに依存しない。一般の分類完全性や停止性の主張ではない。

## 検証と枝の状態

- [X9 の strict 実例](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Audit/Cycle411I74WhereListSpecX9.lean#L118)は周期型の resolved B4 snapshot に対し true。[子の正確な発現](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Audit/Cycle411I74WhereListSpecX9.lean#L174)と、[同じ周期型の fitting model の evidence](https://github.com/momota1029/yulang/blob/6160e8a8ba39096e43694ba67c8cd47db0ba7efe/lean/Audit/Cycle411I74WhereListSpecX9.lean#L162)を独立に検証した。親を裸 rejected にした報告・親成功 leaf・旧 X8 branch・循環しない子は false。実 alias 帰路を親に足すと新 branch は false、旧 raw root branch は true。不一致の子 raw wire・偽 origin・偽親 ID は false。実行値 `[true,false,false,false,false,false,true,false,false,false]`。
- 同じ C03 だけの別検証: role・nominal・束縛・端点の slot・occurrence をすべて改名した入力で true、間違った束縛・role・余分な where・fallback role・二候補・誤った子引数 index は false（`[true,false,false,false,false,false,false]`）。また子が 2 つの異なる構造辺で循環する同じ形で true、1 辺の短絡・別行の偽造は false（`[true,false,false]`）で、同じ二節点の正則 fitting model と `ReportEvidence` を別途確認。この追加対照は検査の範囲を広げない。
- 境界の対照として、方向付き Bound 2 本と flat alias を足した別の fitting snapshot では、同じ元 child rejection の分類と report evidence があっても、公開 checker の全証人が false になることを確認した。正式な X9 の三条件は満たすが、この inherited parent palette は一般の raw K2 非存在を完全に証明する機構ではない。詳細は[境界ノート](../design/dots-cycle-411-c03-verification.md)。検査の限界を証明する追加の [standalone Audit](https://github.com/momota1029/yulang/blob/2e0ccef4b260c42ae73c611a70b4e7e06f64df13/lean/Audit/Cycle411I74WhereListCertificateBoundary.lean) も strict で照合した。
- 技術 pin `2e0ccef4b260c42ae73c611a70b4e7e06f64df13`、Lean tree `9d4507d3518231e1044369275ab44ed80f0875f8`。固定 Git bytes を別の出力先へ取得し、Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) の `lake env lean --trust=0 -DwarningAsError=true`。新規 6 source、独立 Audit 6 本、追記 import 6 本の集約、すべて exit 0。43 unique audited names は `propext`、`Classical.choice`、`Quot.sound` の部分集合のみ。別出力先の C410/C411 joint replay は 12 source、9 Audit、追記 import 集約、全て exit 0。
- 出発時 integration/m1-final `a6a88060218fe5b53340c9c705a6719bdb900fce` で I-65 の三定理の基準と C409 の exact 9 blob（barrel 込み）を確認。integration/types `1b9361bb6dfca0642ee7d7e149e2e224bff535c0` も read-only 確認。C410 はこの周の途中で integration/m1-final `c87d30a67e585f47e6656190d4a44ff47437d088` に反映（全 10 Lean blob と Lean tree `8943ce3be8a4232691a49f1f77805903ae89666a` 一致）。この統合元と同じ素材で C411 を再生した。C411 の結果は work/dots-main の検証で、integration 完了の主張ではない。
- expected-head non-force で work/dots-main のみ。今回の公開差分は報告・心拍込み 18 パス。変更 path、barrel 全体の prefix と追記のみ、凍結 `lean/Audit.lean` と `lean/README.md` の blob ID（本文は読まない）を照合。false は言語の拒否ではない。全体の `lake build`、監督役向け `verify-lean.sh`、Rust/Yulang2、パーサ、NoFalseRejection、停止性は対象外。利用枠は不明。

## 引継ぎ

- 次は C04 / X10。X9 の実 where 子と違い、元候補の nested record head が **実際に** 入った構造位置で K2 を検証する。元の候補、field、到達位置を要し、親根や架空 where 子に置き換えない。
- 質問ノートなし。新しい言語判断は行っていない。
- 最終 integration/m1-final `c87d30a67e585f47e6656190d4a44ff47437d088`、integration/types `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 inbox `b99a214965f1e236ab62e6cffa13b77b617543cb` を再確認。

- 最終照合開始 `2026-11-25T07:23:53.026Z`（50 分経過）。

**C の残り: 19 行（C04–C22）。**
