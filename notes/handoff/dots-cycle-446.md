この周に閉じた G の行: なし。G00 は公開入口の証人構成に残る全体ヘッダー条件のため未完。G の残り: 22 行（G00 を含む）。

# Cycle 446 — G00: raw K2 の有限証人と選択宣言のヘッダー

- 実開始: 2026-11-26T17:35:15.917Z。通常終了の判定は公開した最終 heartbeat を参照。
- 適用指示: I‑82、inbox `ac05479d3a45842a7c63d304689b28ba1d245eb1`。最終確認時の正本: `integration/m1-final@dfa16a4f0ecf4795eea14048d0a99f1d2c956b70`、Lean tree `f1aa56bce113c634cfd2a6a17c8495e429d3a071`。
- 検証済み技術コミット: `work/dots-main@4f712041ae20bf6c518eae9414968716f04bcae1`、Lean tree `3cbed9fc47dea8d743486f0914a1cc003ae58808`。正本の Lean tree と今回の技術成果の一致: 未確認（今回の成果の所在は work/dots-main）。

## 今回証明したこと

1. `SplitEscape446` は有向 Bound の順位と平坦な Alias の側を別々に照合する。既存の `2→0→1`、`1~2`、構造辺 `0→1` の例では旧順位証明器の形は通らないが、新しい証人は通る。実際に元の raw AliasCycle があれば、新しい証人もすべて拒否する。
2. `SplitBoundRank446`、`SplitEscapeFinite446` の `raw_safe_iff_finite_split_witness446` は任意の元の raw 状態・検査位置で、raw AliasCycle がないことと、実際の行を検査する有限データ証人の存在との同値を確立した。Bound の順位は、元の区間・変数間原子から得る有向前件集合を符号化する。収集対象には平坦 Alias、デコードした構造子の子、元の検査位置を含む。非計算的な存在定理で、今回の公開構成は N=rawLimit に対して側表が指数長になりうる。既存の証人の検査結果と全対象位置の側を保ちながら順位表 N、側表 N+1 に圧縮する Lean 検証も別途実施したが、公開実装には含めていない。N は位置番号の上界で、相異なる位置の数ではない。
3. `RetainedSplitReader446`、`RetainedSplitEntry446` では、この証人を既存 G00 の原宣言・候補番号・B6・出現と元の報告に接続した。`check_full_sound446` は同じ状態の全 FitsFull について元の辞書と書き出し順を保証する。旧 witness はすべての入力で C445 にそのまま委譲し、lift 上で旧 R21 の Bool が同じ。`independent_local_and_header_have_exact_witness446` は局所選択と独立した `HeaderReady445` から同じ元報告の証人を構成する。外から raw 証人・配置証拠・reader の成功を仮定しない。
4. C442 由来の入口実行で、元の固定先21への正しい保持、別固定先22、旧 Int が入った固定先、保持なしを確認した。結果は順に `[true,false,false,false]`。各例で source replay と保持位置を別途照合した。旧 Int の状態にはモデルがあり、新しい型付き保持を連言するとモデルがなくなることも別のカーネル定理で確認した。上書きではない。

## G00 の残りと次の作業

`Cycle446I74RetainedHeaderBoundary` は C442 由来の同じ選択を保ったまま、独立に Checked な無関係の ground where 宣言を登録する実例。登録全体の Checked と Coverage、元の一候補・局所選択・本物の B6・元の報告・保持後の一つの FitsFull を示した。それでも現行の全体 `checkHeader439` の保守的な `stableSchema` 検査が落ち、現行の新しい `.splitOutput` 形式の証人はこの正確な報告を一つも通せない。言語仕様上の拒否ではなく、入口固有の制限であり、旧形式すべての失敗を主張するものでもない。

`RetainedLocalHeader446.selected_header_exact446` は、選ばれた元の宣言だけのデータ検査が、その宣言の where 無し・既存 DeclarationCovered・DeclarationChecked と一致することを証明した。公開した reader/checker はまだこれを使わず、旧定義も変更していない。未組み込みの別実験では、旧入口を残した局所ヘッダー経路が既存の独立した C445 局所選択から追加ヘッダー仮定なしに同じ報告を通し、上記反例と四つの回帰例も検証した。次は、この経路を許可された公開入口へ接続し、同じ健全性・互換性・四つの回帰を再確認すること。一般の R_full/check_full、一般言語の NoFalseRejection、探索・停止性、G01 には進んでいない。

## 確認範囲

公式 Lean 4.35.0、`--trust=0 -DwarningAsError=true`。公開の6 production モジュールと8独立 Audit の実ファイルを production-only の import 経路で個別に確認し、57件の公理出力は Lean 標準公理のみ（または公理なし）、入口例の `#guard_msgs` も成功。Audit の import: Yulang.* 以外 0 件。相互 Audit import なし。上記コミットから独立に取得した14ソースの内容を検証済みバイト列と照合し、既存 production 7,702、Audit 2,094 と他 Lean エントリ31を変更していないこと、集約ファイルへ正確に6 importのみ追記したこと、凍結二ファイルの blob ID 不変を確認した。全量 Lean build と Rust は実行していない。
