# cycle260: 実出力・defaultの証明書を有限rebaseへ接続

開始 2026-11-18 16:32:21 UTC。完了時刻・所要時間は末尾の完了記録を参照。
公開先は `work/dots-main` のみ。数学の最終checkpointは
[`a1925029`](https://github.com/momota1029/yulang/commit/a1925029f56466465b89912a92b52e5780129504)。

## 結果

- **252の実associated出力**：実emitted schemaの方程式とcaptureを有限factsにし、新終点Models iff旧installed journal Modelsを**同一assignment**で証明。leaf Evidenceも構成。公開モデルの存在同値はslot3型だけの補完を許し、他の全Compと全rowを保存する。全初期assignmentを変更せず保存する主張ではない。
- **206の実role default**：packet Holdsだけでは不足するClassEffectsを実lookup/bodyVariablesから取り込み、output0型≃inputcenter1型を終点に要求する。旧bottom counterを除去し、同一assignmentの旧installation対応・Evidence・slot0型だけの補完を構成した。
- **202の反射的default**：実target1=inputcenter1なので任意assignment・任意subset stateでModelsが不変。旧kernelは既にStableでStep不可。新fact書込み一歩は**意味的stutter**で、旧install一歩やモデル集合の真の細分化と同一視しない。
- **出力の表住所**：owner/index非衝突を示し、単一body decoderが同owner複数requestを区別できない内部probeも確認。kind/requestを含む4成分住所と、requestの(name,target)による安定符号へ局所修復した。旧owner-only表との混在非衝突は主張せず、既存fixture runnerも変更していない。
- **EqualOutputs**：固定request列の同name順序付きpairを型同値schemaにし、Holds iff EqualOutputsを証明。実stateのClassEffectsをbody義務＋同schemaへ分解した。実alias requestsはnoncomputableなので、これは全traceの有限producerや実行可能一般observerではない。

全28新module・220明示宣言の名前、量化範囲、前提は
[宣言案内](../verification/cycle260/declaration-guide.md)、正確な全型は
[alltypes-final.txt](../verification/cycle260/alltypes-final.txt)。
[設計ノート](../design/2026-11-18-cycle260-output-certified-rebase.md)に選択・反例の射程・未完を記録した。

## 検証

- Lean 4.35.0、全新moduleを `--trust=0 -DwarningAsError=true` でfocused compile。
- 前cycle259の1708依存source、cycle258の1645依存sourceのSHA-256一致。
  現closure **1766 source / 3004 import行**を取得・hash化。旧数学Leanは凍結、barrel追記のみ。
- 直前closureにない**58 module**をfresh strict build。内訳は新28本と既存依存30本。
  56本のfresh build後、未変更を確認してNamedRequestとEqualOutputsを各1本追加でfresh build。
  [build log](../verification/cycle260/final-critical-build.txt)、[正確な対象](../verification/cycle260/final-critical-modules.txt)。
- `cd lean && lake env lean --trust=0 -DwarningAsError=true Audit/Cycle260{Complete,Full,Usage,Types,AllTypes,Reach}.lean`
  を**各ファイル独立に**実行し全てexit0。Audit間importなし。
- Completeは220明示宣言、Fullは生成/privateを含む**492宣言**。許可依存はpropext/Classical.choice/Quot.soundのみ。
- Usageは**18例**。Reachは34最終rootから**164/220**到達、未到達helperも列挙した。全宣言が一つの完成言語定理に繋がったという主張ではない。
- `RequestAddressProbe` と `DecoderScopeProbe` を独立strict compile。内部非要求target・未定義nameをsource到達反例とは呼ばない。run成功は特定assignmentのモデル検証ではないこと、新旧住所の混在には追加分離が必要なことも確認。
- `sorry`、新公理、`native_decide`なし。**全体lake build、verify-lean.sh、Yulang2実行は未実施**。
  [再現手順](../verification/cycle260/reproduction.md)、[監査実行記録](../verification/cycle260/final-audit-run.txt)。
- 252の7本、owner表5本、206の7本、202/bodyの6本、住所修復2本、およびRequestAddressProbeは独立**読取**レビュー済み。独立再buildではない。
  最後のEqualOutputs1本とDecoderScopeProbeはスレッド上限で独立読取を起動できず、自己点検のみ。

## T7b追加読取解析

余り時間のT7bとして、住所分離・run予算・回帰interfaceを明示した50rootでも再解析し、200/220到達を確認した。通常34rootの164/220と目的が異なり、全言語定理への統合や不要コード判定ではない。削除なし。
[解析結果](../verification/cycle260/t7b-interface-analysis.md)と[独立strict実行log](../verification/cycle260/interface-reach.txt)。

## 未完とI-52の達成範囲

部分rebase Stepの実252/206/202回帰で、実出力義務と旧モデル・Evidenceを接続した。
一般sourceのAccや完成した型検査器とは主張しない。

1. 全sourceからの固定owner/request/port候補表生成と全trace閉包。旧owner/port列挙はGenerated/Installable/novel等の条件付きで、全requests閉包ではない。
2. 複数ownerのcapture、全body要求、EqualOutputsを**一つの意味不変な固定layout**へ組み込む一般compiler。新namespaceのinstalled markerと旧owner commitmentの対応、旧tableからの移行も未完。
3. mixed-time packet、child/presence義務、I50依存cycle拒否・ground readback上界、Permittedと12性質の全移植。一般旧microstep simulationも未証明。

次の候補（優先順）：
- `GeneralNominalCenteredHeadAllocV7MergeRegression` の二つの実request/EqualOutputs回帰を、現在のversioned境界との違いを確認して有限request別表へ接続する。古いV7分類をそのまま現仕様へ転用しない。
- 実requestsを固定(name,target)候補表へ写すmembership・payload不変補題。`MixedInstallRequests235.Absorbed`は新child要求が既に表現済みという前提で、任意childへ無条件一般化しない。
- I50出力依存・固定pool閉包と上記compilerを接続して一般StepのClosedを導出する。

## 運用・制限

最新integration `926bcdece86546b484946c0ef01e76dbd362f7b9` のstanding orders/inbox I-51/I-52を再読。意味論・spec/plans変更なし、質問ノートなし。表現選択はdesignへ明記。
前cycle259は完了済み。開始時の前writer停止と公開tree一致を確認し、復旧不要。
無関係のcycle247/248回復ファイルと248/249 lockは手を触れず残した。
公開はGitHub appのexpected-head付き更新で行い、各checkpointをfetchして全tree照合。
使用量の残枠は不明。

## 完了記録

2026-11-18T17:22:23.601856+00:00 UTC、開始から50.04分。数学成果の公開・照合後、追加T7b解析と最終照合まで実施。最終報告・心拍をここで確定して公開する。

このサイクルで公開した変更・追加ファイルは118本（基準cycle259からの差分、数学28本・監査・ノート・心拍を含む）。
