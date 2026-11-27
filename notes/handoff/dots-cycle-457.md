この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C457 引継ぎ

- 実開始 2026-11-27 04:31:40 UTC。通常終了下限 05:21:40 UTC。実終了と解放は同コミットの heartbeat。
- 権威: 開始時 `integration/m1-final@97471f6e20ed88e84a91797be4dafeadffba888b`、採用済み C456 Lean `c7a8ba322261954433e8897b2264234d76178dd4`。最終照合 `integration/m1-final@97471f6e20ed88e84a91797be4dafeadffba888b` / Lean `c7a8ba322261954433e8897b2264234d76178dd4`。I-83 / I-85 の G04 のみ。G03b、G05 以降は未着手。
- 成果は [work/dots-main の固定コミット](https://github.com/momota1029/yulang/commit/c8afb348ad75b8ee9305d7ecaca8bdcea06b7b03)、Lean `2095eb6a97d0f0422c31a073fd2724f53defe879`。

## G04 の実証

旧 ConservativeSmaller のみが落とす**元の非先頭 binder を参照する where**でも、既存の DeclarationReady に必要な元の role・constructor・字句条件、実の正規化後の個数・Smaller・全捕獲での StableSmaller を照合し、同じ FullProblem で **本当に到達した名前付き field の K2**を再生した。解決済み FullProblem を入力とし、単一の可視候補、point 親、元 where 1 つ、名前付き出力指定なしの範囲。旧 checker が落ちた事実を入力条件にはしていない。元の宣言/where の選択・実行・採用規則を変更していない。

- `RoutedReadyHeader457.exact_same_written_local_ready_header_replays457` は同じ原宣言と query/where を再生する。`RecordDiagnosticReady457.conservativity_is_the_only_missing_closed_header_field457` はこの局所条件の下で残った旧条件を分離する。新分岐ではその条件が成立しないことを独立に照合する。旧経路に適合するものは新分岐へすり替えない。
- 純 record 分岐 `RoutedReadyRecord457` と混在分岐 `RoutedReadyMixed457` はそれぞれ `actual_routed_field_report_iff_finite_wire457`、`independent_routed_field_derivation_has_cumulative_witness457`、`check_full_sound457` を持つ。独立な原宣言・raw K2 と実経路から同じ有限 report を再生し、任意の同じ FitsFull について健全。原 clause の ID と ordinal は元 where の由来の照合用で、診断位置を where に移したり子を生成したりしない。選択・辞書・出力書込を行わない。
- 最終の累積入口 **`RoutedReadyMixed457.check_full_ready_mixed457`** は純 field Ready を経由して C456 の正規入口に全入力で同じ Bool を委譲する。混在分岐は実の非 record hop を少なくとも一つ要求する。root K2 や途中の K2 を末尾の field に置き換えない。`ReadyReportBoundary457` の補題は、終点に raw K2 がない場合は個別 witness に限らず全 witness が false であることを示す。
- 同じ実 FitsFull を持つ対照で、深さ 3 の非先頭 field と、record→variant→pair 第2引数→実 declared unary covariant nominal self-point 第1引数→field の五段の双方を確認。旧入口の既知の正例は引き続き true。where/候補・実 ordinal、元の route/issuer、raw 終点自体の K2 欠如を変える対照は false。false はこの有限診断証拠の外であり、それだけでは言語の拒否を意味しない。

## 残り

未解決の open tail、非 point nominal、一般 mode/kind/多引数、任意の inline source payload／bound pattern は含まない。解決済みの原 tail について、同じ raw graph に**既に存在する正確な閉 row**と整合した場合の私的実例・全モデル補題を検証したが、公開入口には入れていない。原 field 投影だけを根拠に raw K2 edge を増やしたり、未確定の need を開いたりしない。spec、既存の宣言審査、診断表示の方針は変更せず、新しい質問はない。G04 を閉じない。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。固定 Git bytes の production 3 と独立 Audit 6 を対象検証。全44件の `#print axioms` は標準公理のみ（またはなし）、3 組の実行回帰。既存 production 7,776、既存 Audit 2,194 の blob は全一致。集約は import 3 行の追記のみ。凍結対象は ID のみ照合。全体ビルド、verify-lean.sh、Rust、parser は未実施。
