# Cycle253: I50 加算深さ・producer順序・public basisの修正候補

開始: 2026-11-18 09:28:30 UTC。50分時点まで設計、証明、使用例と境界の検査を続行。
最終公開・照合・完了時刻は `notes/verification/cycle253/publication-receipt.md`。
開始時integration42e33c1a9、10:12の最新版155c7aa0cを取り込み、I50に変更なし。
前回252の完了心拍と全tree bytesを確認済み。新規13 Leanモジュール、115明示宣言。

## 今回の結果

1. **加算上界を実構文と実例へ接続。** 任意Patternの代入、実243 Expr compilerの
   source葉について、明示したcapture深さ上界Bからtemplate深さ+Bを証明した。
   var参照のままなら深さは不変。有限pool・有限template上の実compiler結果を列挙し、
   列挙長はpool長の変数出現数乗。252の同じI45到達出力は2+2=4をちょうど満たす。
   maxが偽だったモデルや入力を差し替えてはいない。
2. **宣言のproducer呼出しに、規則から作る順序。** CheckedのProduced・Scoped・
   Patersonを用い、raw呼出しとnormalizeArgs-before-captureの呼出しを別々にAcc化。
   後者は実Associated引数と同じ順序で、既存ConservativeSmallerによる減少を使う。
   output-only binderのproducer childは入力質量が真に小さい。child入力はhead入力
   captureを固定すればoutput binder値から独立。これはjournal StepのAccではない。
3. **associated-only入力まで実readbackを拡張。** 実Frame/Holds/ground Inputsと
   正規化headのcoveredArgs=trueから、全inputNamesに有限Partを作り、各labelの
   encodeサイズと構文深さを入力labelsのmass以下に抑える。従来237のNeededのみの
   readbackより広い。非空whereは既存checkerがcoverageを供給する。coveredなleaf
   にも適用でき、252実fixtureで仮定を供給する使用例を検証した。
4. **狭いpoolの欠落を分離し、修正候補を進めた。** source名＋named output binder名
   だけのpoolでは、実238 sourceからI45のinstall一歩で到達するcompound where入力
   端点が抜ける。owner候補をいくら増やしても、このregistryのoutputNamesは空。
   その公開端点を保存するprivate-only置換では、同端点var atomはpool外に残る。
   修正候補としてpurpose2のnamed outputにchild入力3/4・clause output5を加えた。
   実source Initialから、全将来のGenerated/Installable/未Committed installの
   該当public portを覆う一つの有限listを構成し、今回の欠落は局所的に修復した。
5. **候補basisのprivate-free性。** sourceのbelow_seedとorigin purpose分離から、
   source名＋上記public port名のvar poolはpurpose0/1を読まない。固定rebaseの
   position0もversionedの任意positionも含む。union/inter正規形の全typeSources
   （rowを含む）で分離し、Supported前提がある場合は意味保存・有限列挙も同時に得る。

各定理の完全名、量化子・前提・日本語の主張は
`notes/verification/cycle253/declaration-guide.md` と
`CompleteAudit-declarations.txt` を参照。設計を先に記した
`notes/design/2026-11-18-cycle253-i50-depth-closure-plan.md` に判断の経緯を残した。

## 検査例と主張しないこと

- 21件のstrict使用例を検証。空poolでの定数template、名前だけのrename、有限列挙数、
  source到達端点の欠落と局所修復、252実packetのcovered leaf readbackを含む。
- Checkedなleafで、head=`variant 0 (var 0 | var 1)`、whereなし、associated=var0は、
  queryがCompleteでもcoveredHeadが偽となることを検証した。宣言レベルの適用範囲
  の検査であり、source非停止や言語の反例ではない。全leafを覆ったとは言わない。
- poolの診断は「実到達public端点の列挙漏れ」と「端点を保存する置換の条件付き
  不閉包」。新rebase境界でSnapshotNormalを実行して失敗するtraceではない。
- `Build`の加算和上界はtopological構成を明示的に前提にする。sourceがその構成を
  生成する完全性は未証明。node数をowner数と同一視せず、output-only binderや
  owner内の複数出力を落とさない。正増分cycleの矛盾と0増分aliasを区別した。
- 深さは各定理に記した構文・代表の深さ。後段normalizeの影響、全semantic-equivalent
  な冗長表現、row sortの構文深さへ無条件に読み替えない。
- AllHeadReadbackのcaptureは与えたmodelごとの存在。全modelに共通の実行可能な
  source readback producerや、child出力値のproducerを完成したわけではない。
- basisは候補で、operational journal/compiler定義を置き換えていない。center7/8/9、
  source refreshの構造/label vocabulary、空bottom/top、異演算を含むatom、全source
  traceのSnapshot閉包とprivate非流出は残る。normalizeのprivate-freeだけで、
  pool外atomを削る処理を意味保存と取り違えない。

## I50/I49の受入条件と次の継続

I50の局所加算、raw有限列挙、source由来の有限public名、宣言producerの順序を前進。
一方、**source Step全体のAcc、全sourceでのpool閉包・private非流出・strict新fact
進捗は未完了**。後継boundary、EvidenceNode、Permitted、12性質と199〜240回帰の
新境界への移植も完成扱いにしない。宣言callのAccと解決器の停止を混同しない。

偽と分かった狭いpoolに依存する閉包証明だけを保留し、全体を停止せず独立する
修正案・実readback・producer順序の研究を続けた。言語意味を変える選択はなく、
新しい質問ノートは作っていない。次の具体的候補は:

1. **OutputInputReadback/SelectedProducer**: Complete queryから各入力名を個別の
   source-label projectionへ戻し、coveredでないleafまで個別Part/depth boundを拡張。
   joint head質量boundとは分ける。その後NormalizedChild順と実選択候補・child出力
   readbackを接続し、履歴/aliasの整合性graphをproducer graphと混同しない。
2. **PublicBasisSourceClosure**: PublicBasis253候補を実normalizerへ接続し、必要な
   public centerも分類する。有限名だけで任意refresh構文を有限と数えず、source由来
   vocabularyとsnapshot atom閉包・実pipelineのprivate非流出を証明する。
3. **CanonicalStrictProgress**: 同内容の見直しを除き各新Stepのstrict新factを示す。
   有限状態候補だけではcycleを除けない。239/240型の回帰を新表現に接続してからAcc。

## 検証・公開・制限

Lean4.35.0。最終再検証コマンド:

```
bash notes/verification/cycle253/final-build.sh
```

全出力は`final-build.txt`、exit0。各13モジュールを依存順に
`lean --trust=0 -DwarningAsError=true` で再buildし、CompleteAudit115明示宣言、
Full276宣言（生成・private含む）をcollectAxiomsで検査。許容依存は
propext/Classical.choice/Quot.soundのみ。Usage21件も同じstrict設定でPASS。
実fixtureの未cache旧依存80モジュールもstrict buildし、command/list/logを保存。
前回1514依存source hash不変、今回import closure1653sourceを記録。
旧Lean凍結、barrel追記のみ、新規LeanとUsageの禁止語検査PASS。
全体lake build、tools/verify-lean.sh、Yulang2実機は常設指示に従い未実行。
全体PASSは監督役の検証を待つ。使用量枠は不明。

pool診断と候補修復の3モジュール・設計メモは独立read-onlyレビューで範囲を再確認。
独立再buildや残り全コードの独立レビュー済みとは言わない。詳細はindependent-review.md。

公開はGitHubアプリ経由work/dots-mainのみ。開始と約10/20/30/40/50分の心拍、
途中成果を保全。大きい検証hash一覧の読出しが一度truncateされたため、書込前に
分割読出しへ変え、全tree一致を確認して公開した。誤ったtreeを公開していない。
10:12integration取込みではbarrelと心拍に競合したが、integration barrelが手元の
完全prefixであることを確認し、253追記と稼働中253心拍を保持。取込み前後bytes一致。
既存247/248復旧quarantine、248/249 lockは公開対象外。未検証の実装候補は残さない。
公開ファイル数と最終照合はreceiptに記録する。
