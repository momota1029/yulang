この周に閉じた G の行: なし。G03 は元の where 位置の橋と同 role の兄弟のない累積入口まで。広い行として未完、残り19行。

# C450: where の原位置で実 child K2 を検査

- 実開始: 2026-11-26T21:34:30.929Z。終了時刻と経過は同じコミットの heartbeat。使用量の枠は不明。
- 適用 I-83、inbox `1b9ef468ce4e6f844f53533a59c431f27119f66a`。終了時の正本: `integration/m1-final@d0ffaea1ce9897d9b5a4ff3f3e9d9f46bb11fec0`、Lean `0135594ffed895c958a7e3e5c1468fa0bde89ca2`。
- 技術 pin: `work/dots-main@faf8aa01bb77a884f48fa5dc357325496de62475`、Lean `75d34b1e8af7b0881d62221b6be3d9de1932b509`。今回の成果は work/dots-main。正本への統合は未確認。
- 設計: `notes/design/dots-cycle-450-g03-where-order.md`、原木と需要併合の区別は `notes/design/dots-cycle-450-g03-original-vs-merge.md`。

## 証明したこと

1. `raw_child_cycle_has_finite_original_wire450`: 任意の元の ordinary state と任意の需要について、元の実 root の K2 があることと、その実引数番号・Bound/Alias/structural path を読む有限データ証人が存在することは同値。別根・別の状態の検査を代用しない。
2. `parent_header_exact450`, `literal_parent_reconstructs_all_original_children450`: 実 authored の invariant list-binder point frame、元の可視候補一つ、異なる binder、出力なしの範囲。どの原 clause の位置でも、元の単一変数引数とゼロ出力を実に選んだ Event から復元。親の occurrence に元番号を足し、実 clause の role と元の捕捉を使う。子の数・位置は固定しない。各子は同じ snapshot 上で実 raw K2 か、G02 の実成功 leaf。兄弟間の retained equation 更新は入れない。
3. `exact_original_where_report_iff_finite_only_data450`, `accepted_where_keeps_each_actual_child_position450`: 元の trace の独立な選択・全子・同じ報告から、その元報告（選択した親、全子の並び、verdict、空 writes）を通す有限 wire が存在し、逆にチェックを通る報告はその元の木。任意の実原位置で rejected とその位置の実 child raw K2 が対応し、未検査・欠落・別根を代用しない。この層は併合前の原木の補助で、昇格入口として使わない。
4. 昇格入口 `WhereSites450.NoSiblingMerge.check_full450` は、実可視宣言から読む兄弟 role が pairwise distinct の場合だけ新分岐へ送る。これは同 role を要する兄弟間併合がない十分条件で、必要条件でも言語の拒否でもない。 `exact_guarded_original_report_has_data450` と同外形 `check_full_sound450` は同じ FullState の全適合モデルで原 trace の意味と真の成功子の辞書を保存する（拒否親には辞書を作らない）。C449 までの全旧 witness は直接委譲し、全入力で Bool 不変。 `original_C411_same_role_child_is_covered_by_promoted_C450` は旧 C411 の同 role 親・単一子（独立な実選択と K2）を同じ報告の有限 wire に持ち上げる。

## 実入口の検査

- 元の authored 親の二つの入力から別々に捕捉し、実第一子は成功、実第二子だけが K2。三つ目の原位置・原構文の反転でも同じ子が位置に従う。子がなく親だけ rejected の報告・実親 K2・欠落した成功子・wire 入替・別の循環根・余った wire・K2 行削除は不受理。
- 同じ role と同じ実入力を異なる clause ID で二度書いた実例。元 trace の補助は元の重複を記録できるが、昇格入口は全 wire で不受理。これはこの分岐の限界であり、プログラムの拒否を意味しない。公開 guard 2組、出力は `[true,true,true,false,false,false,false,false,false,false]` と `[true,true,true,true,false,false,false,false,false,false,false,false]`。
- 追加の非公開 QA: 通常の raw Alias が与えられると実同 role point の K2 と有限証人が代表へ移る。一方、元の同 role 子の二つの実 point の行の右辺が同じで全適合モデルで値が同値なのに、片方だけ raw K2 の適合可能な状態を確認。旧 value-based SameInputs だけから K2 の移送はできない。仕様の入力同一性の規則の変更や代表の診断政策は主張しない。元の C411 実 fixture の新旧照合も非公開 QA。

## 検証、残り

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`: exact 8 production と 10 独立 Audit を production-only imports で個別に実行、48件の `#print axioms` は標準のみ。実行テストは証明に使っていない。Audit の import: Yulang.* 以外 0 件。別 Audit import なし。旧 7732 production／2132 Audit ほか既存 Lean 入力不変、凍結 Audit.lean と README.md は ID を照合、集約は 8 import 追記のみ。全体 build、verify-lean.sh、Rust は未実行。

G03 全体を閉じるには、同 role の兄弟を元の入力の同一性・非同一性の独立証拠で扱うこと、併合があるとき原位置の列と代表・診断へ写すことが残る。出力依存を伴う where・一般の再帰・一般の選択側の完全性は証明していない。それらを仮定で消したり、他の G 行を進めたりしていない。新しい仕様判断を要求する質問ノートなし。
