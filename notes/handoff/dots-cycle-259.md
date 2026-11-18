# cycle259：実観測に接続した部分rebaseと有限driver

開始2026-11-18 15:29:56 UTC。最終時刻は公開記録に記載。
前writerの終了を確認し、integrationのstanding orders/inboxを再読。
開始時a44b8b310e17e3ea2ea49a664a17391471a44781、途中で
926bcdece86546b484946c0ef01e76dbd362f7b9を取得・mergeした。
16:13再取得でも同一。I51/I52に従い旧数学Lean・specを凍結し、新規追加とbarrel追記のみ。

## 今回進んだこと

28新規数学module・185明示宣言。全宣言の量化範囲・前提・日本語案内は
[宣言案内](../verification/cycle259/declaration-guide.md)、個別の正確な全型は
[型一覧](../verification/cycle259/alltypes-final.txt)を参照。

1. **I45/240の固定表を実packet reportにつないだ。** 実観測reportを初期contextへ
   投影し、decoderからlower/upper/binder/installedの5factsを計算する。
   任意段階のrunはstage0のrunと一致するので、実行側に増大履歴・段階番号を持たない。
   初回一度install・以後noop、同一のcomplete assignmentで旧current journal、
   実plan Holds、次journal、新終点Modelsを同時に構成した。
2. **239も実reportから一度installして止まる。** まず任意rowと初期0〜3の公開境界を
   保存するcompletionを構成し、同一assignmentが全旧段階journalを満たすことを証明。
   実report投影とdecoderを新Stepへ接続し、初回成功・二歩不能・以後noopを示した。
   旧completed roundの公開モデル射影と新stateの射影が双方向に対応する。
   旧239/240の無限に新しい名前を作る実行を、新関係の非停止と混同していない。
3. **中間stateも意味を明記した。** I45/239双方で、初期snapshot Modelsと
   present factsの成立を有限stateのModelsとする。任意subsetについて公開モデルの
   存在同値を証明したが、任意subsetが旧sourceから到達するとは主張しない。
   I45は初期0〜4、239は0〜3の全成分と全rowを固定し、内部binder型は補完する。
4. **basis外を黙って捨てないchecked入口と、実行可能な有限driver。**
   proposalにbasis外factがあれば内部error、なければ差分を書込む。
   複数proposalのnoopを飛ばし、最初の進捗かerrorを返すschedulerを定義。
   remaining.lengthで整礎再帰するsettleの成功時に、有限Runs、残数以内の歩数、
   終端・quiescenceを証明。全stateの全proposalがbasis内という明示Closed条件下で
   errorなく完了する。両実fixtureでClosedと初期→終点を具体的に証明した。
5. **固定batchなら順序・重複によらない。** 固定proposal列とその閉包を前提に、
   settle結果が全writeのbatchとliteral State等号で一致する。外側リストでproposal
   自体のmembershipが同じなら結果も等しい。動的observerの合流性ではない。

## 誤って一般化しないための具体probe

- [DriverProbe](../verification/cycle259/DriverProbe.lean): I45/239の実settle評価は
  remaining=0。手作りobserverは一度成功した後にunsupported999となる。
  3kernel補題で確認した。commit単位の部分書込み禁止はsettle全体のrollbackではない。
- [OutputCoverageProbe](../verification/cycle259/OutputCoverageProbe.lean): 252の実prepared
  packet reportは現在の構文decoderに受理されchecked writeも通るが、既存のbottom出力
  assignmentは初期Models＋Frameを満たしてもpacket Holdsを満たさない。
  これも3kernel補題で確認した。decoder/basis閉包の成功だけでは出力意味証明書に
  ならないという、一般compilerの具体的な未接続箇所である。
  239/I45のcertificate、I50深さ、言語停止性の反例ではなく、言語拒否例でもない。

## 検証

- fresh focused cacheで**63 module**をstrict再buildしexit0。新規28本と、前258の
  hash検証済みclosureに入っていなかった実239依存35本。残り既検証依存は再利用で、
  全1708ファイルの再buildとは言わない。[buildログ](../verification/cycle259/final-critical-build.txt)。
- `--trust=0 -DwarningAsError=true`。Completeは185明示宣言、Fullは構造体・生成/private
  を含む291宣言。propext/Classical.choice/Quot.sound以外なし。Usage23例。
  6つの監査はYulang.*だけをimportし、各々 `cd lean && lake env lean ...` で単独成功。
  [最終監査状態](../verification/cycle259/final-audit-status.txt)。2probeもstrict再検証。
- Reachは選択した28の主結果から151/185明示宣言へ到達。残り34も全件公理監査対象。
  検査用補題・別の回帰・可換則等を隠さずOUTSIDE_SELECTED_ROOTSとして列挙した。
- 実import closure1708ファイル・2893import行をhash化。前258の1645ファイル、
  前257の1615ファイル不変。旧数学Lean凍結・barrel追記を検査。
  [source検査](../verification/cycle259/source-checks.txt)。
- 全28数学moduleは6回の独立読取レビューで範囲混同なし。独立再buildは未実施。
  fresh buildはこの作業者によるもの。probeの追加レビューは別記する。
- whole lake build、verify-lean.sh、Yulang2 runtimeは実行していない。
  Lean #evalはruntime煙試験であり証明oracleではない。2probe合計6補題はkernel検証。

## 未完と次の優先

一般sourceから有限owner/basis/意味表と正しいobserverを生成するcompiler、
任意Reportの健全性・完全性、constructor/presence/child/outputの全coverage、
旧microstepとの対応、owner別置換が公開制約を失わない一般不変条件、
I50のoutput pool閉包・循環outputの拒否は未証明。
任意observerに対する有限関係Accを、言語全体の意味保存停止性と呼ばない。
一般EvidenceNode/Permitted、resolve_exact、principal typing、199/202/204/206/218/230
を含む全回帰・12性質の移植も未完。

次はdriverの抽象補題を増やすより、252のoutputを持つ実packetでfinite fact意味表と
同じinstallの対応を作り、現在の具体的なoutput certificate欠落を埋める。
[設計](../design/2026-11-18-cycle259-observed-rebase.md)末尾に選択肢と依存義務を記載。
言語の意味の変更を必要とする新事例は確認していない。
