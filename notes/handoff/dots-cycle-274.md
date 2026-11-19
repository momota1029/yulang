# Cycle 274: 実230の有限 rebase、正の終端辞書、mixed refresh の境界

- 指示 I-52 / I-51 / I-53。書き込みは `work/dots-main` のみ、公開は expected-head 付き non-force。既存 Lean、spec、計画、設定、凍結ファイルは未変更、barrel は末尾追記のみ。
- 開始: 2026-11-19 13:31:40 UTC（13:30 定時枠）。報告作成: 2026-11-19T14:23:02Z（51.37 分）。使用量の枠: 不明。
- 前周の完了 `751fde8daf79272c1028b6f6a8dc85273abf22c4` と心拍を確認、ローカル開始 tree `f90f562fcf711498b9d90985b0185cc9517595e9` と一致。他 writer は見当たらなかった。
- integration/m1-final は開始時 `d272fe1eaf29cca645d48c28ad0a44c5eb0bc2fa`。途中で `3382f7eaab33017d4697fcbe082acc070bd1ae1b` に変わったため、公開をいったん止めて immutable 指示・inbox を確認。blob `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4` / `2f6b72446884d0e340537ac4b9aea1bb6c0e047d` は同一、STOP なし。同 tree `ed47f02db1847fe2c221b7a9788ec6c3fc163853` のローカル祖先 `a1cc0b224` を静的検査の基準にした。
- 途中公開: 31e417ab、4693e642、5c7a38b8、27e22249、f0009faa、f5206a72、af3b8f5f、fe1ac8fa、7205d165、6030ac67、552545fc 。前周から 92 ファイル（Lean・監査・記録・報告・心拍を含む）。

## 実証結果

1. **実230の正の source への対応。** 最初の versioned install、実 Reobserve、最後の実 install の三辺に対し、`GeneralRebaseTerminalBridge274.realized / trace_realized` はこの有限機械の任意の受理遷移・列が対応する本物の Step を持つと証明。旧実行全体の完全性・終了を主張しない。正規化した lower/upper/actual 支持は同じ論理 owner block にあり、観測時は committed を変えず、service 時に一度だけ上書き。有限 rank は 3→2→1→0。この範囲の Acc。実 `arguments/report` を読み、完成した報告のみ bindings として採る計算（`TerminalObservation274.exact`）。actual center は根の nominal 観測から証明した source 2 で、上端と推測しない。実 before/point context を入力に葉 payload を返し、before を point の代用にすると none。
2. **任意の公開 assignment の厳密な意味。** `GeneralRebaseTerminalRows274` と `TerminalBridge274.public_agrees` は四位相すべてで元との双方向対応。型 ID0～4 と全 row の値は字面通り固定し、一つの full model を作る。初回 install は output4 を真に制限し、以後の観測と再 install は同じ公開 projection。終端は actual 233 の正の葉 Evidence を全ての受理公開境界で与える。単一の例示モデルだけではない。
3. **全 actual install 位相の同一 assignment での必要十分条件。** `TerminalFirstExact274.initial_to_first` は元初期モデルに optional body ＋私的型式3本（旧 lower=source4、上端とcenter=source2）を足すことと一致。Reobserve は同一モデル。 `TerminalPointExact274.exact` は point full model ＋私的型式2本（新 lower/upper が source2 と等価）が二度目の actual install のちょうど全条件。この2本は終端から必要、任意の point model で十分。各片方だけを optional に間違えた witness は元 point では可、終端不可。`TerminalRepair274.repairs` は任意の実 point model の新しい2型座標だけで終端へ完備し、それ以外の型・全 row を固定。 `TerminalActivation274.finished` は任意の初期 full model から、source0～3・全 row を文字通り維持し、出力4を実 optional union に置いた正の終端辞書を構成。
4. **公開値だけの決定的な型読み戻しと一つの辞書 witness。** `GeneralRebaseSemanticSupport274.exact` は legacy-empty journal でその有限 read-support 上だけ型が意味的同値で row が文字通り同じなら、Models が同値と示す。実230の reads を旧/新スロット＋actual＋source に制限。`TerminalAlias274` の型 read は source4（旧 lower）や source2（幅の役割）へ向く一方、row ID は変えない。 `TerminalDecode274.exact` は公開型5値と全 row だけから選択不要の decode を与え、実終端の全 Model、実葉 Evidence、既存 stable-name executor の終端 block を同一 assignment で必要十分。範囲外の型値を読まず bottom は未使用座標だけ。
5. **固定セルの実行と正の payload。** `TerminalScheduler274.after_install` は既存242 scheduler の観測/service と実際の有限 Step を対応。 `TerminalSchedulerModels274.one_common_state` は初回 install 後から終端まで、固定セル store と本物の journal が同じ公開境界・一つの witness を持つ。固定 lower の意味は source4 から source2 に変わり、旧・新 block を同じセルに同時に課すのは矛盾。本物の歴史的 versioned 2スロットを別名で読む場合は矛盾しない。 `TerminalPayload274.checked/view_exact` は実終端 full model で正しい宣言 ID・空子リストだけを Evidence として受理し、有限型 alias を介した版も同値。 `TerminalStoreBoundary274.store_not_evidence` は実の初期幅型出力が安定セル store の最後だけを通れても、実 optional body を満たさず真の終端モデルではないと反証。
6. **mixed の安全な境界。** `TerminalMixedRefresh274.mixed_reachable` は I44 の実三辺が mixed でも到達を与える。これだけで安定性は移さない。 `TerminalMixedFrontier274.mixed_stable_iff` は追加 Step があるなら、それは既存の3つの私的幅の座標（旧 upper、新 lower、新 upper）のどれかを明示化する refresh に限ること、逆にその証明書があれば実 Step であることを証明。どのような実追加 Step でも同一 full assignment の真偽は変わらない（`model_transparent`）。`TerminalTrustedWidth274.width_justified` はこの3つが versioned input を使う mixed trusted slice でそれぞれ証明可能、`legacy_cannot_justify_width` は旧 source-only cut ではいずれも不可能と示す。必要な raw slot 登録・refinement と全新 head の証明書を実際に作るところまでは未完で、mixed Stable の真偽は未確定。

## 検証と残り

- 27 新規 Lean モジュール、301 個の名前付き宣言、単独監査 11 本、重点再実行 17 本。個別 `lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . …`、各監査を単独再実行。主検証は全27モジュール完了。追加の別キャッシュ再コンパイルは公開締切のため 13/27 モジュールの PASS まで記録し、全件・別キャッシュ監査の完了は主張しない。許容公理 propext / Classical.choice / Quot.sound のみ。既存の未cache依存は内容を変えず個別出力。全体 lake build / CI / 実機は常設指示により未実行。
- `git diff --check`、`bash tools/verify-lean.sh . a1cc0b224 --no-build`、`bash tools/verify-lean.sh . d750e84ea --no-build` は exit 0。出力全文、barrel/凍結ファイル確認、全宣言一覧は [verification/cycle274](../verification/cycle274/)、設計は [design](../design/2026-11-19-cycle274-terminal-positive-rebase.md)。
- 未完: 230以外へ自動的に source context を得る一般 compiler、複数 owner と生成子を伴う正の recursive Evidence、全 source の Acc・意味保存。以前に反証された 238 の生成 child 下端保存や旧239/240の無条件停止性は主張しない。

- 次候補: 実230の private width を一つ選び既存 raw slot を保った Fin6 登録と Refines を構成（trusted 型事実は済み）。または matching child が既に locate される別の source で、同じ方式の正の非葉辞書例を作る。
