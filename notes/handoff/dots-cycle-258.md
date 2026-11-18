# cycle258：固定再構成と、I52 の部分的 rebase Step

開始2026-11-18 14:25:58 UTC。最終時刻・所要時間は末尾の公開記録に記載。
前cycle257の公開・終了とwriter停止を確認して開始。integrationは開始時
`f894530e18ba3e50f5ed0c593a44493382ae0c40`。14:55に最新
`a44b8b310e17e3ea2ea49a664a17391471a44781` のI51/I52を取得・再読・merge。
以後、旧familyの追加有限View研究を止め、部分的でも新Stepを先に定義した。
15:08再取得時も同じintegration。旧数学Leanとspecは凍結、barrel追記のみ。

## 成果と受け入れ条件

26新規数学module、200明示宣言。個別名と日本語の量化範囲・前提は
[宣言案内](../verification/cycle258/declaration-guide.md)、全型は
[elaborated型](../verification/cycle258/alltypes-final.txt)を参照。

1. **I52：StepをLeanに定義した。** `GeneralRebaseStep258` は有限basisの
   sublistであるremaining factsを状態に持つ。任意observerが提案する固定
   owner/basis/binder factsをfilterで取り除き、真の差分がある場合だけStep。
   任意basis、任意observer、任意状態でremaining長が厳密減少しAcc。
   `GeneralRebaseBudget258` は任意runで `n + 最終remaining長 ≤ 初期remaining長`、
   初期からbasis.length以内を証明。同一proposalは冪等、再tryWriteはnone。
2. **I45具体回帰：一度installして終了。** `GeneralDictionaryRebaseStep258`
   の固定5事実を返すobserverに対し、初期→finalの一歩、二歩不能、run長≤1。
   全正段階の旧completed stateはfinalへ投影される。
   `GeneralDictionaryRebasePublic258.old_new` は任意n・公開境界に対し、
   旧completed state nとnew project nの存在公開モデルを双方向に対応させる。
   固定するのは初期0〜4全成分と全row、内部binder型は解放する。
3. **I52前の成果も検証・保全。** I45の全生成名を数値名ごとの有限探索で識別し、
   段階nや増大historyを引数に取らないfill/completeを構成。任意初期rawモデル
   から初期0〜4全成分・全rowを保存して、同じassignmentが全段階journalを
   満たすことを証明した。内部binderを固定する強い延長は提示seedで不可能。
   初期条件だけでbinder固定版が成立するとは主張していない。
4. 早期探索は旧探索と関数等号。生成index iの訪問上界i+1は対応する単独探索
   に限る。full fill両探索合計や整数演算時間の上界ではない。
5. 具体252 sourceでは初期Models＋Frameだけから任意payload Evidenceは得られ
   ない一方、未使用出力slot3の型だけをFoo(Foo(slot2))へ補完すると、任意初期
   モデルから実packet Holds・既存installation Models・leaf Evidenceを構成。
   固定閉代表の深さ4と補完後の全初期モデルでのreadbackを証明した。
   I50の反例、一般sourceのproducerや加算深さ上界ではない。

**未完を明確にする:** 現在のI45 observerは固定表で、一般の実inspectionから
proposalを作るcompilerは未接続。old_newはcompleted stageの公開モデル同値で、
全旧microstep simulationではない。Modelsのelseは中間subsetにも述語を与えるが、
その言語的正当性は主張しない。239具体回帰、constructor/presence/child coverage、
source由来の固定basisと新情報を失わない完全性、言語全体の意味保存Accは未証明。
一般observerを仮定した有限関係のAccを、これらが完成した証拠にはしない。

## 検証

- 新規25本はfresh focused cacheで15:05:12〜15:06:04に再build、全監査PASS。
  最後のBudget1本も別strict compile、以後全26本の監査を再実行。
  `--trust=0 -DwarningAsError=true`。[ログ](../verification/cycle258/final-build.txt)。
- 240〜258の実依存222本を別fresh cacheで15:06:19〜15:11:06に再buildしexit0。
  最後のBudgetを同cacheで追加再buildし、合計223本を今回fresh検証。
  古い残りの依存は再利用であり全1645本再buildではない。
  [全文](../verification/cycle258/critical-rebuild.txt)。
- Completeで200のdef/theorem/abbrevを列挙、Fullで構造体・inductive・生成/privateを含む383宣言。標準
  propext/Classical.choice/Quot.sound以外なし。Usage24例。
  Reachは選択13rootから117/200、残りも全件公理監査対象であり隠していない。
- 全依存1645ファイル/2793import行をhash化。前257の1615ファイルと前256の
  1593ファイル不変。旧数学Lean凍結、barrel追記を確認。
  [検査](../verification/cycle258/source-checks.txt)。
- I51に従い、追加AuditのimportはYulang.*のみ。六つをそれぞれ
  `cd lean && lake env lean --trust=0 -DwarningAsError=true Audit/Cycle258<Kind>.lean`
  で単独実行。最終26本はfresh223 cache上で15:12:11までに全6本exit0、
  各出力はfocused監査とbyte一致。初回はlakeのcacheに新moduleがなく失敗し、検証済みcacheを正規
  build先へリンク後に成功。Audit同士のimportで解決していない。
  ただし26本目を含むcheckpoint時はdirect lean監査が先行し、最新6本の
  lake単独再実行はcheckpoint後となった。最終公開前には完了。
- 全26数学moduleを6回の独立読取レビュー。中間subsetのModelsについて文言を
  修正した以外、範囲混同なし。独立reviewerによる再buildは未実施。
- **全体lake build、verify-lean.sh、Yulang2実行は未実施。** Lean上のrecognizer
  小例#evalのみ実施（proof oracleではない）。全体検証は監督役に委ねる。

## 次の課題（I52優先）

1. `ReportProjection257.actual_report` と実plan Holds/owner writeを束ねた
   source-derived proposal certificateを定義し、固定表observerを実観測へ接続。
2. 239のinitial4成分/binder公開境界、future upperをbottomにする旧novelty witness、
   retained定義除去を確認し、対応を証明してから有限新Step回帰を得る。
   既存238のEquivalent congruenceは再利用できるが、任意公開rowを保持する
   row-parametricモデルの義務が残ると特定した。
3. 一般sourceの有限basis producerとchild/presenceを含む意味保存・完全性。
   その後に言語的に正しい新StepのAccを主張する。

[新Step設計・残る橋](../design/2026-11-18-cycle258-rebase-step.md)。
表現をremaining sublistにしたのは変更可能な実装選択で、通るプログラムの意味を
変更する判断はしていない。新たな言語意味の質問ノートは積んでいない。

## 公開・時間・制限

公開先は `work/dots-main` のみ。全26本とfocused監査は
`8d436511bb65dad726dda81481cb3a70732a0fdf` に公開・remote tree完全照合済み。
開始、10/20/30/40分の心拍を公開。30分心拍はI51/I52切替のため約2分遅延と明記。
失われた成果なし。使用量の残枠は不明。

最終報告確定: 2026-11-18 15:16:01 UTC、開始から50.06分。
50分心拍はこのcompleted更新と同時に公開。検証・研究を終え、次cycleまで停止する。
最終差分は131ファイル（最新integration由来のinbox更新を含む）。一覧は `notes/verification/cycle258/publication-files.txt`。
