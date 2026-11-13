# 次の橋: Stableではなく、現在の検査が読むsourceを輸送する

## 今回の到達点

任意の実Value到達状態と、そのjournalに実在するpacketに対して、
BindingSchemaReplay.replayは現在computed bindingsの一致とOriginsから、
変数を含む現在の名前付きschemaのModelsを示す。
MixedCarrierRefreshはこの二条件を実2→3carrier refreshで計算し、
正のモデルとともに示した。一般の検査輸送はまだ証明していない。

## 既存の事実の用途

- packet_seed: 実履歴はallocation seedを保存する。
- RecordedRequestModels.reachable_coherent / reachable_requestsKnown:
  記録requestのschema coherenceと現在のknownness。
- InstallationOrigin / SupportJournal: 記録packetの実際の導入元・可視性。
- ValueSteps.stable_committed: 現在InstallableでPacketGuardを満たすpacketは、
  StableならCommitted。過去のpacketとの同一性は結論ではない。
- stable_site / stable_merges_of_exact: 現在のsiteとmerge閉包。
- reachable_joint_instance: Jointを与えれば現在Instance。
  Jointを目的の意味論そのもので埋めるのは未解決の橋を解いたことにならない。

## 最小の次の部分目標

一般のsource-preserving embeddingについて、nominal/variableだけを辿る
正規化済みquery treeの検査結果の輸送を示す:

1. 各lookup対象のsourceに対応する現在slotを特定する。
2. Refines.nominalsが、実際に訪れるdescriptorをrenameして保持する。
3. 各captureについて、nameとsourceのlower/upper identityとoriginが保存される。
4. normalized declarationを再検査すると、computed bindingsが過去と一致し、
   Originsが満たされる。
5. BindingSchemaReplay.replayを適用する。

全carrierの同一性ではなく、queryが読む有限部分だけを要求する。
普通のextensionについてはcandidate_report_extended / bindings_reportが出発点になる。
本cycleの具体的refreshはこの部分目標の非自明な受け入れ例である。

structural viewを読むqueryでは注意が必要:
Refines.headsはRewritesを与えるが、検査に使うviewの構文形や子sourceの一致を
直接には与えない。これを勝手にrflとみなさず、別のview-transport条件か証明を作る。

## reobserveを混ぜる前の障害分析

一般のreobserveはモデルとnominal domainを保ってもdescriptorのboundsを変更しうる。
したがって証明書の意味論的な同値から、captured endpointのsource identity一致は
ただちに従わない。後でStableになったことも過去の読みを同一にする性質ではない。

これは一般輸送定理の否定を証明したという主張ではない。
現時点の証明書から欲しい構文等式を取り出す補題が無い、という設計上の障害である。
まずRefines型refreshだけに区切るか、descriptor revisionの経路を別途追跡する。
言語のreobserve規則を狭める変更はしない。

## 意味論上の質問の要否

今回の制限は証明のスコープであり、ユーザーに新しい拒否規則を選ばせる話ではない。
そのため質問ノートは増やさない。将来、source identityを同値類へ置き換える必要が
実例で確定した場合は、意味論を変える前に独立の質問ノートを作る。

## 仕様との照合メモ

spec/06-roles.mdは、関連型を新しい通常の型変数と等式として扱い、
実装選択前にもその変数へ通常の制約が積まれるとする。
そのため未知の名前付き出力を含むpacketを、最初から観測済みのscalar出力へ
置き換えて例を成立させない。本cycleの混合packetとrefreshは、実際の記録された
出力制約を保持してから新しい観測を公開する。

同章の「合流前の変数は合流した後のpayloadをそのまま捕捉する」に対して、
CapturedChildIntervalsは実cross行列とmerge等式を使う。
任意分割した捕捉を新しい前提として足していない。
ただしこの汎用補題の繰返し/nonpoint場合を、今回の正の実到達fixtureで
実測したとまでは言わない。GeneratedIntervalExampleはsingleton/point captureである。

ここでの照合は現行specとLean定義の読解である。
Yulang2のCLIをこのcycleで実行した結果ではない。
