# Dots cycle 405 — 同じ選択導出から検査位置を得る

閉じた補題なし・分けた補題なし。

- I-72。基点 `91f7a9d24d2f8923b3d2d597f8bb6a37ce20a3e2`、開始時の integration `8edef9d7cbc0bb92a126e4fd60b7c3f61851120d`、指示 blob `2684940d16dd1b4f8aa76788a2719010b04a3bf4`。前周の完了心拍と報告を確認。同じ固定文・C380 一覧のまま、I-65 (1) の実際の選択規則のみを進めた。
- Lean 差分は `a6b5625c0e9955b29cfd729a4f827bf196853a8b`（Lean tree `7365f9a7b43b4f627e0de0bf764364b3718d921d`）で固定。新規 Lean 15 モジュール、独立 Audit 15、`Yulang.lean` にその import だけを末尾追記。変更は報告・設計 2 本・心拍を含む 35 パス。

## 選択と辞書の実証

C402 の暫定 S03 は同一イベントの `visits` を任意の列に交換できた（C404 の矛盾）。今回は `GroundedPriority405` と `GroundedCanonical405` で、実際の候補表を対象とする導出から列を生成した。`inserted_marker_is_not_grounded405` は C404 の後付けマーカーが同じ選択から出ないことを証明する。変数だけの head では構造検査は空だが、元の候補・引数・反復する変数の位置は消さず、`GroundedPositions405` と `GroundedRawOrder405` で宣言レジストリの元の番号に戻しても順序が保存される。

- **非空の正の例**: `AuthoredNativeSelection405.chosen_authored_native_unary_has_nonempty_actual_visits405`。一候補・一引数の declared 共変 `K 'a`、独立に付いた下端・上端を持つ実際の head から、下端の元の根を 1 回検査する選択導出を作る。子は単なる変数なので検査しない。原グラフの root K2 は先に判定し、以前に表せた曖昧・子 K2 の分岐はこの同一の一候補の形とは両立しない。この正の証明は実 payload 名の元の記述が得られる場合で、欠けた場合を拒否とは判定しない。その実中心を出力側で保持し、ガードから推測しない。既存の能力の範囲で [`authored_native_selects_with_original_B6_and_where405`](https://github.com/momota1029/yulang/blob/a6b5625c0e9955b29cfd729a4f827bf196853a8b/lean/Yulang/GeneralDeclarativeI65I72AuthoredNativeSelection405.lean#L303) は、同じノードで供給された元の B6 型つき RHS、実際の固定先行と順序付き where 導出を使い、同じ辞書 ledger をすべての `Fits` モデルで得る。
- **同一導出と支持の森**: `GroundedExactTrace405.original_producer_remains_the_one_consumed405` では正の受け側を先に仮定せず、`atOriginal 0` が元の生産側の導出そのものを読む受け側を作る。`GroundedLocalReceipt405` は、候補に使った同じ event から、反復した実中心の保持済み等式、where の元の番号と名前、B6 の出力番号と固定先を読む。`UnifiedGroundedReplay405.existing_source_rules_assemble_grounded_dictionary405` は、与えられた同じ source trace の全選択ノード（where と、それとは別の出力支持）で priority を証明し、同じ ledger を返す。
- **範囲を明示した S03 の置換**: `CanonicalMixedPriority405.canonical_actual_mixed_visit_order405` と [`actual_mixed_S03_is_exact405`](https://github.com/momota1029/yulang/blob/a6b5625c0e9955b29cfd729a4f827bf196853a8b/lean/Yulang/GeneralDeclarativeI65I72CanonicalMixedPriority405.lean#L50) は表現できる変数 head と上記の native head について、同一 event・支持のあらゆる実証で**列全体**が一致すること、到達位置は元の raw 宣言番号で、その位置に raw K2 がないことを示す。既存 C402 の不可能な前提を上の assembly は使わない。暫定 `exact_rhs_in_C402_provisional_signature405 : S13bbba` は、既に型つき元語を持つ C402 の Event からの読出しに限る。一般の source がその Event を作ること、integration の C380 の行を閉じることとは区別した。

## K2・残り

`GroundedNative405` では、元の固定先に片付いた出力がある場合だけ、独立な authored 上端と合わせて native の最初の子を実際に検査する。未完了の内側の環は入力支持から除いても raw K2 には残り、拒否する。raw root K2 は森も候補検査列も不要。`GroundedNativeCenters405.declared_guard_alone_cannot_name_selected_center405` は、同じ両端・構文・捕捉葉の順を保った `DeepRead` が中心名を一意にしないことを示す。これは証拠表現の限界であって、言語に別の拒否条件を足す理由ではない。

次: (1) 完了出力 lower の正の native head を、authored Origin を偽造せずに表現する。同じ原出現・引数番号・path の実 payload 名を供給する別の論理入力が必要（端点を中心としてはならない）。(2) 実際に入った構造候補の失敗/保留を含め、全可視候補について検査を取りこぼさない導出に拡げる。今回の一候補 trace はその全称ではない。仕様質問は作っていない。C380 表示は未解決 14（未証明 3・一部 11）のまま。I-65 (2)(3)、停止性、旧 Local/C334、fixture、Rust/Yulang2 実機は対象外。

## 検証

Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。全 15 新規ソースと独立 Audit を strict に実行。公開 pin から Git blob を再取得し、`git hash-object` 各 30 件の一致を確認。既存の依存物を使いつつ**今回の** 15 個の生成済み成果を除去した別ディレクトリで `lake env lean --trust=0 -DwarningAsError=true` により公開ソースと全 Audit、追加 import からなる監査を再構築、終了 0。65 宣言の依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ（部分集合を含む）。巨大な barrel は元の全バイト + 正確な末尾 15 import と照合。変更パス、凍結 2 blob、固定文/C380 は Git で照合。リポジトリ全体の build / `verify-lean.sh` は監督役向けで未実行。使用枠は不明。
- 最終照合開始 `2026-11-25T01:20:34.278Z`（50 分経過）。
