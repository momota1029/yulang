# dots cycle 341: 実 solver の成功診断と支持つき宣言判断の対照

## 指示と範囲

- 開始時に `integration/m1-final` の常設指示・inbox・spec 6 / 10 を再読。integration は `32244df15707e3a153b4add4272a3a0a56bb04ec`、作業の出発点は C340 `259e8f6b6f47682ce9561f45fafc7c01a2f0a436`。I-62 に従い、旧宣言的 `Local` との対応は目標から外した。比較相手は到達した実 mixed Lean solver 状態と、I-58/I-61・同じタグの合流を備えた C340 の支持付き正の証人判断。どのプログラムを通すかは変更しない。
- 開始直後に作業環境が offline だった。承認済みのクラウド環境を再接続し、残っていた作業木と公式 Lean 4.35.0 を再利用。新しい Lean ソース・独立監査・barrel の import 追記・説明・心拍のみ。非 force の期待 head 検査つきで `work/dots-main` のみに公開。

## (2) 今回閉じた補題（成功して既に止まった範囲）

1. **成功した実診断の同じ木。** `GeneralDeclarativeStoppedPaired341.exact` は、任意の raw 状態・境界・根・有限成功診断木について、実登録された center site、モード別の lower/center/upper の alias、現在の alias class 要求の文字通りの列、実生成子への閉包、および順序つきの子の証人を持つとき、宣言側で**同一診断木**と同じ辞書を導く。どこかで同じ値になるというだけでは位置・名前・順序の条件は満たさない。呼び出しごとに同じ raw occurrence の論理的な端点名が異なってもよく、固定出力は改名しない。 `StoppedDiagnostic341.exact_tree` は関数として射影できる場合の補題。どちらも既に得られた有限成功木の帰納だけであり、raw packet 健全性や solver の停止は前提・結論にしていない。別に `StoppedLockstep341.same_assignment` は、現 packet を実際に構成できる断片でのみ、同じ一つの割当ての raw Evidence と宣言的 Evidence を導く。
2. **記録済み packet を現在に読み直す。** `StoppedHistory341.retained_current_sites` は、任意の到達状態に実際に記録された effect について、過去の実 install から現在までの範囲で raw/center site が文字通り保持されることを示す。 `retarget_frame` は、観測を保つ精密化と現候補の実再検査から、保持された site・物理変数 lookup・宣言を用いて *現在の* Frame を構成する。 `StoppedRetarget341.recorded_semantics` は任意の現 raw モデルで現 packet と現 class の出力が成り立つことを示し、 `ordered_rows_same` は任意のリストで逐次コンパイルの結果（失敗を含む）と、成功時の正確な RHS・固定 target の列を保持する。 `StoppedPeers341.fit_iff` は、存在する現モデルと観測を保つ retarget を前提として、残る互換性が「同じ alias class の過去の候補が現在の再検査で失敗していない」と同値であることを示す。一役割一キーの断片では過去の記録と現選択から Frame と実現可能性まで導出する（選択の新規則ではない）。 `StoppedOrdinal341.placed_ordinal` は任意の ordinal で実際の同じ class 要求と target を保ち、実 installable で既に止まった場合にその行が全モデルで成り立つと示す。履歴に対する仮想 install は足さない。
3. **C276 実二節点。** `StoppedDisplay341.all_current` は root と実際の生成済み未記録 child 両方の現在 Frame と実現可能な packet を、各々の過去選択・空の要求列・実モデルから構成する。 `StoppedPairedDisplay341.exact_diagnostic` は、検査済み小 executor の成功と実停止状態について、raw child `(1,1,1)` と compiler child `(2,1,3)` をモード別に対応づけて、同じ診断木 `selected 1 [selected 3 []]` を最新の宣言判断で示す。 `actual_success` は既存の ordinary 名を保持する明示的拡張後の同じモデルで二つの Evidence を得る。任意の実行環境に対する Rust の比較ではない。
4. **C285 実出力と全モデルの回帰。** 実 install → refresh → halt。 `StoppedRequested341.ordinal_zero` は実 ordinal 0 の output 名 0、固定 target 3、RHS `Foo(Foo(var 2))` を現 binder 2 から得る。現 plan 自体は journal にないが、同じ occurrence には別の過去 plan がある。 `StoppedRetargetCut341.fit_from_history285` は実履歴から新しい現 Frame と packet を出す。 `StoppedDepthExact341.base_exact` は、現普通射影＋この固定出力行と、**全 raw journal モデル**の同じ割当てでの同値。 `StoppedMissingOutput341.cannot_omit` では出力行を省くと実文脈は満たすが全 raw journal には入らない反例を得る。真の compiler は新端点名 4/5 を発行するため、同じ任意の割当てをそのまま流用すると失敗する実例も確認した（`StoppedFreshCut341.exact_extension_needed`）。明示補完なら全 raw 旧意味 footprint に**全座標が一致**し、逆も成り立つ（`compiled_exact`）。その同じ保守拡張で最新の宣言的 Evidence と現 raw Evidence が得られる。版をまたいで出力 target を付け替えていない。独立監査で、補完により行の座標は変わらず、生成された出力 RHS も refresh で観測した scalar も source 由来に昇格しないことを再検査。
5. **C316 の正確な限界。** `StoppedObstruction341.actual_obstruction` は、実到達・実 halt、子も成功した二節点の raw 選択、実生成子を同時に持つが、現在 root の Frame はどれも、全 raw 現モデルで full packet を作れないと示す。 `StoppedReports341.Compound.recursive_report` は実ガード/辺から有限の選択診断が得られることも確認した。 `StoppedRetargetCut341.no_retained_transport` は、観測を保つ同じ記録 packet の retarget では、この root へ移せないことを示す。保持した where の下端式と、現観測の幅の要求が、同一の版なし番地で衝突する既知の現象を、今の Frame の側から切り分けた。これは原因の切り分けであり、宣言側が C316 を拒否するとも、Rust 実装が同じ診断を返したとも言わない。旧 Local 対応の再導入や停止性の追加はしない。

## 残り（I-62 の数え方）

- **(4) 1 群。** I-60 の証人つき辞書健全性はそのまま。I-61/合流の承認済み射影を、任意の混在した入れ子・非 plain の認められた形に広げる一般の入力生成群は残る。C340 の正の joined 判定や C334 の元定理を狭めていない。
- **(2) 2 群。** (A) 任意の既停止実状態に対し、実 solver の普通情報・端点・型変数共有・出力由来を、最新の支持付き判定の実証人に写す一般射影。今回閉じた記録済み且つ観測を保つ断片では、残る失敗検査を明示。未記録一般と、C316 のように版依存の入力が変わる場合は未解決。(B) 任意の実返却（正の信頼できる診断、拒否/保留を含む全診断、正しい子順・出力・辞書）の正確さ。今回、条件付き成功木の輸送と二つの実成功例を証明したが全報告の定理ではない。I-59/K2 と未解決時の優先順位は変更していない。
- 次の候補: ① C317–319 の版つき where 記録を、過去の子と現在の子を混同せず最新証人への実 `Placement` として検証する。C319 の `RootCertificate.before` は別台帳 `versionedWhere` の install 前 Frame なので、現 `mixed.effects` についての本周の履歴定理をそのまま適用しない。② (2 A) の record/nonpoint 実 raw 射影では中心行を source と偽らず、端点の由来・固定出力・明示的な ordinary 拡張を個別に証明する。③ 実返却の負側の正確さは別に扱い、I-59 の既決 K2 等を持ち直すまで正側から推論しない。

## 質問

今回はなし。言語の判断は行わず、I-62 の実 solver と支持つき宣言判断だけを比較した。

## 検証・公開

- 公式 Lean 4.35.0。新規各 module の `lake build --wfail Yulang.GeneralDeclarative...341`、固定 Git bytes から 22 新規ソース・7 独立監査を一件ずつ `lean --trust=0 -DwarningAsError=true` で再検査し全件 PASS。そのうち生成行の由来・行モデルの監査は追加の `lean/Audit/Cycle341Origin.lean`。旧 `Audit.lean` は使わない。C334 の元辞書定理および C340 の joined 対応も同一 bytes の比較対象として再検査。
- 独立監査で 47 宣言の出力は標準公理 `propext`、`Classical.choice`、`Quot.sound` のみ。焦点 import の推移検査 `AXIOM-GATE-PASS: 101268 declarations`。I-62 専用検査は 7 ルート・2585 到達宣言で、旧宣言的対応の指定した定理群への依存なし。
- 固定された証明本体 `5ee53409f231f5b3f732daa6cd3c4367cae31ffd`。追加監査と検証ログを含む inputs `86100542a88c9b24f1d1c6e909a0addfe329166b`。完全な差分ログは [この出力](../verification/cycle341/diff-only-full.txt)、固定ソース検査 [一覧](../verification/cycle341/exact-detached-trust0.txt)、[公理](../verification/cycle341/exact-detached-axioms.txt) と [追加監査](../verification/cycle341/origins-audit.txt)。追加監査を含めた同じ差分検査も PASS（`--no-build` の凍結読み除外版）。フル Lake build、監督役の全体 CI、および Rust 実行は行っていない。
- 既存 barrel の 319840 bytes は完全な prefix を保持し、22 本の新規 import だけを追記。I-57 の二つの凍結項目は内容を checkout/読み書きせず、integration と初期/公開先の blob ID 一致だけを確認。監査追加までの固定ピンの差分は 57 パス。報告を加えた最終 tree も expected-head 親と逐語照合する。
- 最初の UTC 記録は 08:34:53、心拍開始 `2026-11-22T08:35:02Z`、報告更新 `2026-11-22T09:22:31Z`。最初の記録から報告まで約 47.6 分（始動の遅れがあっても次の枠と重複しない 09:25 UTC の上限を遵守）。利用枠の残量は不明。
