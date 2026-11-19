# dots-main cycle 277 — 実 HeadAlloc 非葉と、混合カーネルの有限長境界

- 開始: 2026-11-19 16:30:14 UTC。報告記録: 2026-11-19T17:20:17Z（経過 50.05 分）。
- 276 を照合して開始。integration は開始時 `751fde8d`、途中から `869026cf`。両時点の standing orders と inbox を読み、指示 blob が同一、ACTIVE、I-51〜53 と凍結継続を確認。private `work/dots-main` のみに公開。
- [設計と証明境界](../design/2026-11-19-cycle277-compiled-source.md)。途中版には実 Step・V8 証拠・公開端点の復元・名前所有・有限長の順にチェックポイントを置いた。

## 今回証明したこと

1. **実 HeadAlloc アダプターで Display→Int が一歩で止まる。** 276の直接境界の到着状態を等しいと仮定せず、元の source Initial に対して、コンパイル後の Registry で候補、現在 Frame、Effect、safe 判定を再構成。`GeneralRebaseCompiledInstall277.adapter_step` は実装の Step。該当する具体的初期状態ではこれが唯一の Step で、到着後に次の Step はない（`GeneralRebaseCompiledAcc277.adapter_acc`）。直接版とコンパイル版で生の core は異なる。無関係な Wrap のキー変更が予約リストにも実際に現れる一方、raw site、中心、実子への順序付き edge、普通の式、および任意の全割当上のモデル述語は同じ。
2. **実子を持つ V8 証拠と公開端点の正確な復元。** 両ノードの実 V8 Local は `.selected`。有効な任意の到着モデルで `.node 1 [.node 3 []]` を構成し、`EvidenceAt` と `GeneratedChildren`、誤キー等を拒む正確な payload 判定を確認。実行機械の二状態は具体的な全到達状態とすべての Step に対応。公開データとして source 0,1 の型値を与えた場合、定義した公開述語を満たすことと、有効な全モデルへの拡張があることは同値。条件を満たせば非公開の型を bottom、行を空に置く明示的な復元で足りる。任意の公開型のモデル判定が実行可能とは主張しない。
3. **一般の実到達状態で、新規割り当てと診断の境界を証明。** `GeneralRebaseMixedOwnedTrace277.adapter_reachable` は実 source の任意の到達状態で、各 raw 名が seed 以下または所有キーの符号であり、記録された中心付き site の出力先は raw source に載ると示す。install、refresh、reobserve、equate、enqueue、merge を扱う。したがってこの範囲で任意の registry・invocation・bindings に Fresh を示せる。所有なしで予約だけした人工状態では、同じ構成子・role 0候補でも Fresh が変わる反例を検証した（source 到達例ではない）。
4. **同一の実到達状態からの registry 差し替え。** 構成子と対象 role の宣言所属が同じなら、`GeneralRebaseRegistryLocal277.reached_local` はすべての V8 Local（K2、未検査、出力矛盾、sharing 等）を保存。現時点で生成されたすべての focus に同条件を課すと、`GeneralRebaseRegistryOneStep277.reached_one_step` は任意の実 Step に対応する Step を構成し、任意の全割当上のモデル述語、raw/center sites、順序付き edges、aliases、seed、ordinary、Known を保存する。既存の明示／既定出力と以前の効果も比較する。出発状態は同一で、到着した別々の journal からの一般双模倣は未証明。
5. **実トレース長の明示上界。** インストールなしの実区間は、その区間の開始時の異なる raw 名数を M、中心付き occurrence ID 数を C とすると、最大 `Q=2M+M²+C²` 歩。refresh・reobserve・equate・merge が有限 fact を真に増やし、この区間では新しい raw 名が増えない。各 install が追加する異なる raw 名はコンパイル済み registry の予約キー数以下、中心付き ID は最大 requirement 数以下。任意の実有限トレースについて plan ledger の増加を k とすると、長さは `k + (k+1)Q` 以下（この式の Q には k 回の増加を加えた上界を用いる）。従って、実 install 数の一様上界、または「有限キー候補内」かつ「同じキーの再訪は既存の意味・効果・子辺で committed」を別に証明できれば full Acc が従う。239の既存の実反例は逆に、任意数の install に到達でき、この有限キー証明書を持たないことを Lean で確認。同じ (occurrence ID, declaration ID) の再訪が committed でない具体例も独立に検査した。 有限射影が安定した後も、この非吸収性が毎周残る。

## 残り

- 任意 source で install 数が有界とはいえない。239 型については新しい再ベース表現側で反復を潰す必要がある。次に証明すべきことは、該当断片の実 source が有限キーに入り、同じキーを持つ新規 plan の意味・出力効果・子辺が既存履歴から本当に従うこと。今回の有限長上界は、それを仮定なしで済ませたものではない。具体的な次手は 239 の upper 名の bottom パッチ反例を再ベース版でも追い、同じ owner の上下一点化を既存の binder と保持済み式で説明できるか、公開端点を変えずに検査すること。
- 対象 role の可視宣言自体が変わる一般の HeadAlloc 変換、別々の journal をまたぐ多段対応、任意プログラムの V8 producer、全面停止は未証明。仕様判断は変更せず、質問ノートは追加していない。

## 検証

- 新規ライブラリ 33 モジュール、独立監査 14 本、318 宣言を trust=0・警告エラー化で確認。標準公理のみ。 独立監査14本と主要16モジュールを再検査して全件 PASS。
- Lean の純粋な閉じた例でコンパイル済み予約12・最大子数1、正しい／誤ったキー、正しい／余分な子の payload、および明示的公開復元モデルの実 V8 証拠を検証した。
- `git diff --check`、統合ベース・276ベースの `tools/verify-lean.sh --no-build`、凍結ファイル無変更と各追加モジュールの barrel 追記を確認。静的ゲートの要約は再実行コマンドと完全出力の SHA-256 を付けた。全 lake build・CI・Yulang 実機は実行していない。使用枠は不明。
- [検証コマンド](../verification/cycle277/commands.txt) / [検証マニフェスト](../verification/cycle277/verified-manifest.txt) / [239再訪検査](../verification/cycle277/owner-key-obstruction.lean) / [閉じた例](../verification/cycle277/compiled-regressions.lean)。今回の変更・追加 118 ファイル。
