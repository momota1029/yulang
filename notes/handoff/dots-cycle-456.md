この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C456 引継ぎ

- 実開始 2026-11-27 03:35:19 UTC、通常終了下限 04:25:19 UTC。実終了・解放は同コミットの heartbeat。
- 開始時の権威 `integration/m1-final@67b0df5a7423a56b8f0e212e7217e92f7e08042d`、Lean `54e8b8050b48e032ca76a6392d9b82776cd3feee` に C455 が採用済み。最終照合: `integration/m1-final@67b0df5a7423a56b8f0e212e7217e92f7e08042d` / Lean `54e8b8050b48e032ca76a6392d9b82776cd3feee`。I-83 / I-85 に従い G04 のみ。G03b、G05 以降には着手していない。
- 成果は [work/dots-main の固定コミット](https://github.com/momota1029/yulang/commit/eaea391b21e6614c71f133874629def58fb1a3e5)、Lean `c7a8ba322261954433e8897b2264234d76178dd4`。

## G04 で届いた範囲

単一の可視候補、親の同じ point、実 where 一つ、名前付き出力指定なしのまま、閉じた record field に至る途中に tag 付き variant、primitive pair、および実宣言に由来する単項 covariant value nominal point があっても、元の位置・issuer・raw K2 を保つ有限の再生を追加した。proper prefix は元の source/OriginRoute とその raw 形状、元の候補側 pattern と実の子の位置、raw 非循環を照合する。終点は実際に訪問した名前付き field の非変数型位置で、開口用の source はそこで不要。変数で束縛しただけの未訪問循環は報告に使わない。

- `RecordTraversal455.MixedQA.mixed_cycle_has_actual_finite_wire` は実到達経路と finite wire の両方向。`MixedNative456.real_extra_original_iff_finite_ordinal455` は variant/pair の元の構文・実物理保有位置・元 issuer の照合。variant/pair の native payload は実の変数名への指し先に限り、深い下位項は別の実 source row で開く。実 pair の第2引数と、第1引数の非検査循環を区別した。
- 旧 query 変換が実 declared mode の application を読めないことを `legacy_application_cannot_read_original_declared_mode456` で示し、同じ元宣言を通す `AuthoredInspectQuery456.compile_query_exact` で局所修復した。旧変換がもともと成功する場合の code は保存される。新しい code は Visit 用の形だけであり、型の値の解釈に流用していない。`RoutedQueryHeader456.exact_same_written_header_replays456` は同じ可視候補・元の head/where・既存の構造審査を保持する。
- `RoutedNominalPoint456.literal_covariant_point_child_is_only_original_ordinal456` と `original_point_compares_in_the_same_model456` は実 Use / mode table、正しい native source 位置、元の index 0、同じ全適合モデルの比較を確認する。比較は **同じ point とそれ自身**。継承なしでは1個、継承ありでは4個の reflexive 原子で、異なる端点の区間比較ではない。nominal body は開かない。
- 最終の累積入口は **`RoutedNominalMixed456.check_full_nominal456`**。少なくとも一つの実 nominal hop を持つ新分岐は `actual_routed_field_report_iff_finite_wire456` と `independent_routed_field_derivation_has_cumulative_witness456`、任意の同じ FitsFull に対する `check_full_sound456` を持つ。以前の variant/pair 用 `RoutedMixed456.check_full456` に全入力で Bool を変えずに直接委譲し、その先も C455 の正規入口に委譲する。旧 raw-only 試作を再導入せず、辞書選択や where 子の生成・出力書込は行わない。
- 実 FullProblem と実 FitsFull を持つ対照で、record→variant→pair 第2引数→nominal 第1引数→record field の5段を一つの報告として検証した。元 route / issuer、variant tag、pair/nominal の位置・native 由来、候補・経路・終点のすり替え、root K2 と実 subfield を取り違える対照は false。旧候補変換 false / 同じ元宣言での新変換 true も検証した。false はこの有限 checker が証明を受け取らないという観察であり、言語の拒否ではない。

## 開いたままの範囲

異なる端点を持つ nominal、一般の mode または kind/多引数、変数名を介さない任意の inline native payload、open record tail、固定 ConservativeSmaller が落とす元の nonfirst where を、公開の正規入口にはまだつないでいない。open prefix から実 field の値を投影できても raw K2 edge を付け足す根拠にはならない。非先頭 binder の元 where には既存 DeclarationReady と実 route の補助検証があるが、公開判定を変えていない。次はこの同じ実例で局所診断の元宣言をつなぐこと。spec・既存承認規則・表示方針は変更せず、新しい質問も積んでいない。

## 再現と範囲

公式 Lean 4.35.0、`--trust=0 -DwarningAsError=true`。固定 Git bytes の production 7 を依存順にビルドし、新規 Audit 11 は production-only の別実行で通過。Audit の `#print axioms` 66 件と production の追加 print 3 件は標準公理のみ（またはなし）。`#guard_msgs/#eval` は4組の実行回帰。以前の production 7,769 と Audit 2,183 の全 Git blob は一致、集約は import 7 行追記のみ、凍結対象は ID のみ照合。全体の Lake/verify-lean.sh、Rust、parser は未実施。
