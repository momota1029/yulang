# dots-main cycle 345: 現在の別名クラスの出力由来と Ready

- 開始: 2026-11-22 12:32:29 UTC。指示元 `7dfbbfd750423300b6acaf57232c39b57ffa6c91` と前回の完了点 `d7e6a230c53cbec7bac7abed45fa8f8d05e9ec3f` を先に確認。途中の統合 `7fffb973195326f5fc947673adee7cc4ed91f5b6` でも standing/inbox、spec 6、spec 10、B4 草稿の blob は一致。I-62 に従い、旧 `Local` との対応は再開していない。
- 実作業の最初と 12:58 UTC 前後で作業環境がロールバック。承認済みの同一環境に戻し、公開点から Yulang と監査だけを厳密復元。他の checkout、凍結2ファイル、integration は触っていない。

## 今回の証明

- **出力の由来と順序。** `CurrentOrder345.rows` は solver の「現在の物理 site 順、各 site の出力番号順」をタグ付きで保持し、出力の射影が既存の実リストと厳密に一致する。等しい target でも別の物理行は消さない。任意の実 mixed finite trace で旧物理 site 番号・出力番号は維持され、出力列の順序と重複は部分列として保存される。merge の exact scan では新しい依頼が元の列の途中にも入り得る。alias 同値だけで出力を元の出生 site に移さない。
- **宣言と Ready。** 実 source 到達の role/由来不変量と、その実解釈の Coverage から、現在の全依頼について `RequestsDeclared` と `Ready` を導出。版付き隔離 `InstallStep` に対しても、現在 stamp を特定し、実コミット後の全クラスに同じ導出を行う（`CurrentReady345.from_reachable`）。既知の名前だけでなく実コンパイラの RHS 翻訳成功を得る。ここでの由来は raw ルート／where 節とその物理依頼で、未解決の出力を I-61 の独立した頭の根拠に変えない。
- **任意の実到達結果の保持済み effect。** 実 install の frame、解釈の保存、現在の出力クラスから、過去の `Ready` を現在の代用にせず導出する（`CurrentHistory345.retained_ready`）。同じ実終モデルで全 retained effect の出力を、effect リスト順と物理依頼順で再現し、各式を元の固定 target と由来 site/ordinal に対応させる（`CurrentBodies345.independent`）。全状態の point-only 投影を前提にしない。C238 では実の版付き据付後に旧全体 lowerer は失敗するが、target 4 の実出力は全合法事後モデルで再現できる。既知の普通ビューがあれば同じモデルに付加も可能。これらは保持済み効果であり、最終選択された辞書の認定ではない。
- **実例。** C311 の出生時無出力の子は merge 後に物理寄与元 (site 1, output 0) から名付き target `z` を継承し、選んだ現 frame の出力式が全合法モデルで成立する。C310 では実 merge 後に同じ名前・同じ target の (1,0) と (2,0) が順に二回残り、集合化では欠落することを確認。
- **実停止例の境界。** 元 C316 の root は実停止時にも current frame・RequestsDeclared・Ready を持ち、target 4 の通常式がその実モデルで成立する。それでも全ての合法終モデルで旧 root の完全な入力／where パケットは不成立。現在の出力の成功だけでは入力パケットや新しい版 stamp を捏造できない。I-62 の最新証人つき選択と旧実行の診断が同値だとは述べない。
- **未記録の current effect。** 任意の到達済み state で現在の frame と semantically committed な実パケットがあれば、同じ終モデルに現在の出力式と物理由来を結び、where の実子辺も得られる。停止済み state からの版は本当に `Installable` な current proposal を別途要求し、停止だけからパケットを作らない。C311 の上記の子は実 effect が保存されていないにもかかわらず、実 current packet が全モデルで成立して target `z` を読む例。反対に C316 元 root は Ready でもその root の実 `Installable` が存在しない。`CurrentCandidate345.actual_cut` は実 frame／一意候補から現 proposal を組み立て、既往 choice とも両立し、現モデルで出力も成立するのに、完全 raw パケットの共通モデル条件は満たせないことを分離した。
- **隔離版付き試作。** source 到達で得た登録・role 由来・Coverage は、実 mixed step と隔離 `InstallStep` を区別した有限列で保たれる。既存の stamp 番号と物理 site 番号は動かない。C319 の実二段据付と合間の実 nominal 再観測について、両方の Ready を source から導出し、固定出力 4 を維持して一つの終割当てで両 receipt を検証（`HybridPhysical345.replay_one_model`）。これは新しい実行器を定義したという主張ではない。
- **出力 RHS の出所。** コンパイラが返した receipt から、明示 RHS なら宣言内の実番号・名前、default なら role 署名にある RHS と明示同名 RHS の不在を導く。default の変数は旧端点でなく、その plan の実中心の位置で解決する（`RhsOrigin345.rhs_exact`、`default_center`）。過去の plan は過去の中心を持つため、その receipt を現 plan のものに昇格しない。

## 残りと次の切れ目

- **(4) 1群**：I-61 の独立根拠を持つ全 nested/compound、非点端点、open/closed 残余を最新の証人つき選択に接続する一般 producer。今回の Coverage は出力構文を翻訳できること。頭の独立支持、区間観測の網羅性、I-58 の実中心等式を代用しない。
- **(2) 2群**：①任意の実 raw 成功停止からの現行入力／where 版付き完全パケットと独立 source 支持（保持済み出力のところは今回前進）。②その証拠と最新の証人つき診断・順序付き辞書の一般対応。現行 root 停止を版付き隔離 trace に持ち上げる実 producer は未証明。次は C316 のように Ready は成立するが古い where パケットが成立しない分岐を、実際の実行器がどの版付き情報で区別できるかを切り出す。次いで (4) の一般 I-61 nested/compound 読みの残余を進める。
- 質問ノートなし。旧 Local 対応・停止性・Rust 実行・全体 Lean ビルドを主張しない。環境における利用量は不明。

## 検証と公開

- 証明固定点 `723476c2c87bf0e49572c44496938e5b6d43cc8e`。Lean 4.35.0、27 新規モジュールを対象とする `lake build --wfail` 成功（依存 3600 jobs）。固定点の detached exact bytes から 27 ソースと 5 独立 Audit をそれぞれ `lean --trust=0 -DwarningAsError=true`、名前付き 64 定理の公理を確認。scoped gate は非プラットフォーム宣言 104,391 件、許可標準公理のみ。
- C344 からの40変更パスの exact bytes、追加行検査、frozen 2 blob 不変を確認。凍結対象はファイル内容を読み込まず、前回・作業点・指示元の blob ID を照合。barrel の元 324,448 bytes は完全一致、今回の import 27 行だけを末尾追加。
- 記録: [focused Lake](../verification/cycle345/focused-lake.txt)、[固定ソース・独立監査](../verification/cycle345/exact-trust0.txt)、[名前付き公理](../verification/cycle345/exact-named-axioms.txt)、[scope gate](../verification/cycle345/scoped-axioms.txt)、[差分チェッカー全文](../verification/cycle345/diff-only-full.txt)、[回帰ケース索引](../verification/cycle345/regression-index.md)、[次に必要な source producer](../design/dots-cycle-345-next-source-producer.md)。
- 最終公開を 2026-11-22T13:22:31.061Z（開始後 50.03 分）に開始。対象は `work/dots-main` だけ。意味論・実行器・integration は未変更。
