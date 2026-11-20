# dots-main cycle 287: 行を含む実 where 子の据付・保留・辞書

## 対象と結果

二つの checked registry を比較した。同じ生の初期 journal に、座標 0 の `R(row0)`、座標 1 の `F(R(row0))`、未確定の出力座標 2 を置く。実親 `F(a)` は `where` で実子を一つ生成し、関連出力 `F(F(a))` を据える。子は (A) 型全体を変数で受け取る宣言、または (B) `R(r)` の行位置を直接読む宣言。二つとも Lean の実 mixed-kernel 例であり、新しく Yulang2 の表面プログラムを実行した結果ではない。

- **実据付・モデルの健全性と完全性**: `GeneralRebaseRowParentStep287.actual_step/generated`、`GeneralRebaseRowParentFrame287.after_exact`。両 registry について実際に一つの親据付がある。同じ完全割当てに対し、据付後の全 Models は、座標 0 の型が `R(row0)`、1 が `F(0 の型)`、2 が `F(F(0 の型))` にそれぞれ同値であることと必要十分。生 snapshot 自体は据付後も元の制約と同値 (`RowTrustedBoundary287.raw_after`)。親据付は出力名の型を狭めるが、元の型を全座標で固定し両方とも元の Models に入る二割当てを、変更した独立の行だけで新たに分離しない (`RowPublic287.no_new_ambient_row_test`)。この周の正の例は型の内側の行を運ぶのであり、新しい独立の行読みをしたとは主張しない。
- **子の分類・辞書の健全性と完全性**: `GeneralRebaseRowGeneratedChild287.pending_actual/no_child_evidence`、`GeneralRebaseRowPayloadExact287.exact/comparison`、`GeneralRebaseRowLocal287.positive_tree/blocked_tree`。行分解側は checked、かつ子入力が Known の一点行 descriptor でも、現在の `translate` は行位置を保留する。実際に生成された子は `InspectionPending` で、`Failed` でも `Prepared` でもない。K2 拒否や辞書不存在として分類していない。親の木は `.selected 0 [.pending]`、どの妥当な割当てにも完成した根辞書はない。型全体を受け取る側は、全 Models と同じ割当てでの根 Evidence の同時成立が、上記型検査と payload `.node 0 [.node 1 []]` に必要十分。
- **生と正準の支持・健全性と完全性**: `GeneralRebaseRowMinimal287.before_minimal/after_minimal/canonical_minimal`、`GeneralRebaseRowPublic287.public_arbitrary_unused_rows`。任意の有限の型・行の読取り集合について、完全割当ての生 Models を判定する最小支持は、前は型 0,1 と行 0、後は型 0,1,2 と行 0。含むことが必要十分。正準補完では型 2 を計算するので型 0,1 と行 0 で足り、未使用行は任意。型の全座標を保って行 0 だけ変更すると、元の source 条件そのものを破れる (`RowChildRaw287.ambient_boundary`)。それを子が新たに加える条件と混同しない。
- **補助・実経路と外側の範囲**: `GeneralRebaseRowActualPaths287.only_before/maximal_endpoint/raw_accessible` と `GeneralRebaseRowClosure287.no_step`。この二つの生 journal の初期状態からの極大経路は、どちらも実親据付一手だけで生 Step が止まる。`RowEvidenceAt287.stable_pending_without_dictionary` は、子が保留で完成した辞書がない場合でも、生安定と、子の証拠を前提とする EvidenceAt が両立することを示す。`RowOuterBoundary287.no_outer_reach` は、保たれる元 source が固定 `GroundRoots` を満たさないので両終点とも外側の Initial からは到達不能と示す。`RowClosedTerm287.wrapped_not_closed` により、行を一値へ固定するだけでも、名義引数を型としてしか組み立てない現行の閉じた表現では `F(R(row))` を表せない。したがって B4 の外側の普遍主張への反例ではない。
- **補助・信頼できる出力キャッシュ**: `GeneralRebaseRowSettlement287.evidence_without_discharge`、`GeneralRebaseRowTrustedBoundary287.forbidden_known`、`GeneralRebaseRowSemanticMark287.all_except_trust`。正の枝の葉は辞書証拠があり `Committed` だが、実 journal の plan ledger には子がないため `Discharged` ではない。従って親出力の trusted fact は得られない。既存の下端から `F(slot1)` と書く descriptor は全 journal モデルで出力2を表すが、認証 cache を作れない。285 と異なり、中間型がないのではなく、出力を信頼する手続きが不足。`RowSourceLeaf287.output_independent_leaf` は、親出力を満たさない元 source 割当てでも正の枝の局所子証拠が立つことを示し、循環しない将来の ledger 補助証明を隔離した。現行ルールは変更していない。
- **実行と診断の区別・健全性と完全性**: `GeneralRebaseRowProjection287.actual_square/materially_different_at_same_output_view`。現行 270 の二事実の出力射影は、実親据付に一手対応するが、終点は両枝で同一なので、それだけから辞書の完成を判定できない。`GeneralRebaseRowFixtureDriver287.actually_read/exact_run` はこの二例に限り、実際の子検査の blocked/conflicts/arity を読む1ビットを加え、実終点の解決木と計算結果を任意の木について照合した。両枝を Lean で実行した。既存の全言語の resolver を置換していない。

## 追加ファイルと検証

- `lean/Yulang/GeneralRebaseRow*287.lean` を31本追加。主な群は row head/source/pending、親 packet/inputs/output/frame/step、子 evidence と exact payload、typed public/minimal、局所診断、settlement/trust/mark、経路 closure と境界、実 fixture driver。`lean/Yulang.lean` は import の追記のみ。以前の Lean ファイル・`lean/Audit.lean`・`lean/README.md`・仕様・Rust・lake 設定は変更していない。
- Lean 4.35.0、`lake env lean --trust=0 -M 3200 -DwarningAsError=true`。新規31モジュールと独立監査9本（64宣言）が exit 0。監査で出た公理は `propext / Classical.choice / Quot.sound` のみ。旧回帰15本も exit 0。二つの `tools/verify-lean.sh --no-build` は exit 0。静的検査の REVIEW 2件は `Cycle287Driver.lean` の純粋な `#eval (run true/false).map Prod.snd` のみ。独立の同監査で両方の木を表示し、`#guard` も通した。全体 build・全体 Audit・CI は実行していない。[ログと再現手順](../verification/cycle287/)。
- 2026-11-20 02:30:05Z に開始。始めに `integration/m1-final` の `b9bb2a19d271447d6f03f8b99e8ec97c9ee50363` の standing orders、続いて inbox（ACTIVE、I-53）を読んだ。286 完了 `dfbb9f68dc03bf095e9091be84f0584ddfced2cf` の心拍と報告を照合。監査 `55574b6052ef1534fd0fc36d6d3617ebede59a0e` の C3-ROLE-01/02（既存の関連型・constructor・where の表面回帰）を確認。新しい表面テストや parser の可否の主張はしない。
- 中間 pin: `5553233b`（開始）、`b23b5b0d`（設計）、`6d545031`（実検査保留）、`673810f9`（10分域）、`9b0b32bf`（実据付）、`f1f9a2fc`（実辞書と cache）、`9defdb56`（生経路と範囲）、`7345d642`（検証済み成果）。前周から59パス。private `work/dots-main` だけに非強制 expected-head で反映。利用枠残量は不明、終盤の空きは約52 GiB。

## 未達と候補

独立の行位置を読む子が、元の妥当な二割当てを実据付で分離する正の例は未達。直接読む枝は現行の検査で保留。全般の B4/T1c 停止性、主型性、一般 239/240 の後継への移植、表面構文対応も未証明。質問ノートは追加していない。

残る候補は (1) 行を型とは別に持つ実検査・binder・閉じた表現を同じ例で接続する、(2) 親出力から独立して検証できた葉を、証拠に基づき ledger で扱う方策を設計する、(3) 後継の有限射影に診断を運ぶ領域と仮定を明記する。[三つの境界の設計](../design/2026-11-20-cycle287-separated-obligations.md)。


報告固定: 2026-11-20T03:21:06Z（経過 51.02 分）。
