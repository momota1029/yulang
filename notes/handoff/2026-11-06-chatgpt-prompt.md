# ChatGPT Pro への依頼プロンプト (2026-11-06)

新しいスレッドで貼る用。スレッドが落ちても、これだけで始められるように書いてある。
回数制なので、止まらずに進める・こまめに push する・問いは `notes/questions/` に積む、の三つを守らせる。

```text
yulang の yulang3 ブランチ(https://github.com/momota1029/yulang)を pull して、
Lean の核の拡張と Rust 実装の準備を続けてください。
これは新しいスレッドです。前の会話は引き継がれていないので、まず下の「読むもの」から始めてください。
途中で私に確認を取らずに、できるところまで自走してください。

## 進め方(重要)
- 小さな単位でこまめに commit と push をする。目安は、定理のまとまり一つ、または
  メモの節一つごとに git push origin yulang3。push が失敗したら数回やり直す。
- 仕様(spec/)が黙っていて決められない所で、止まらない。
  1. その問いを notes/questions/ の新しいファイル(例: 2026-11-07-open-questions.md)に追記する。
     1 問ずつ・例つき・選択肢つき(あなたの推奨を先頭)。どの定理や設計に効くかも書く。
  2. 仮の前提を置くなら「仮」と明記し、その前提に依存しない部分を先に進める。
  3. その問いごと push する。
- 仕様を自分で決めない。決定の文を広げて解釈しない。迷ったら問いにする。
- sorry、追加の公理、native_decide を使わない。lake build と
  lake env lean --trust=0 Audit.lean を通してから push する。
- 既存の定理の主張を弱めない。テストの期待値を書き換えて通さない。
- README の「示さないこと」の列と spec/10 の「残る義務」を、証明した範囲と一致させる。

## 読むもの(この順で)
1. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜44 の一覧と、証明してほしい主張)
2. notes/questions/2026-11-06-open-questions.md
   前のスレッドで積んだ 10 問が、すべて回答済みになりました。各 Q の「状態」の行が答えです。
3. notes/design/2026-11-06-surface-to-core-translation-draft.md(翻訳表)
4. notes/design/2026-11-06-rust-oracle-plan.md、notes/design/2026-11-06-presence-inference-integration.md
5. notes/cheatsheet/2026-11-06-yulang-cheatsheet.md
6. lean/README.md と spec/10-inference-core.md(10.27 以降)

## 作業 1: 回答済みの 10 問を反映する(最優先)
答えは spec/ に反映済みです(Q1 は 05-effects 5.2、Q2・Q9・Q10 は 03-expressions、
Q3〜Q8 は 03b-patterns)。仮の前提と答えが違うものだけ、証明を直してください。

- Q1(payload pattern の網羅性): 仮は A(静的に網羅性を要求)でしたが、答えは **B**。
  「引けるけど引かない」: operation の payload pattern が非網羅でもよく、合う arm が無い
  要求は元の継続と一緒に外へ渡され、その operation key は行から引かれず残余に残る。
  payload 全体を覆う arm(反駁不能。guard 付きは数えない)があるときだけ key を行から引く。
  → MultiOperationHandlerTyping 系の、operation ごとの payload の扱い・残余の行・
    健全性の定理を直す。決定 41(許可 mask にない key の arm は拒否)は変えない。
- Q4(record pattern の default のscope): 仮は A(外側の環境)でしたが、答えは **B**。
  default の式からは、同じ pattern でそれまでに照合して束縛した名前が見える。照合は
  field の記述順(左から右)。同名なら pattern の束縛が外側を隠す。or の各枝は自分の枝の束縛だけ。
  → CaseDataTerms.defaultEval に渡す環境、nested pattern、型環境を直す。
- Q5(先行 miss で後ろの default を省く)、Q6(or は最初に合った枝で確定、guard 偽なら次の arm)、
  Q7(同じ経路の重複束縛は静的に拒否)は、仮の前提と同じです。そのまま使えます。
- Q2(float は IEEE binary64、小数 literal は最近接・偶数丸め、厳密な有理数は std の frac)、
  Q3(float literal pattern は Eq で比較。0.0 = -0.0、NaN は自分にも合わない。網羅性に数えない)、
  Q8(反駁可能な polyvariant payload の arm を合わせて tag 全体を覆える)、
  Q9(負の list index は無効)、Q10(無効な index は名前つき error effect:
  error index_err: out_of_range int は下書き)は、新しい義務です。
  LiteralValues の float、case の網羅性、NominalListViews の index に反映してください。
- 後のスレッドで積まれた問い(notes/questions/ の 3 ファイル)も、すべて回答済みです:
  - Q11(binary64 を超える小数 literal): A。丸めた結果が有限なら受理し、無限大へ溢れる literal は静的に拒否。
  - Q12(index_err): A。`error index_err: out_of_range int` を確定。payload は無効だった index。
  - Q13(list spread): **B**(推奨と違う)。対象は任意の `Fold`。走査順に新しい list へ入れる。
    `for` と同じ role 解決・辞書・effect。無限の Fold なら終わらない。
    → list spread の型判断に `Fold 'item` の制約を足し、辞書選択・effect 行・評価順を接続する。
- 追加の仕様(質問ファイルの外で決まったもの):
  - parser pattern は pattern を書ける場所ならどこにでも書ける(spec/09-parser-dsl.md 9.1)。
  - `case:`(対象の式なし)は `\x -> case x:` の略(spec/03-expressions.md 3.7)。

## 作業 2: 翻訳表の「欠」の続き
翻訳表の「欠」「下書き」のうち残っているもの。進めた分だけ push。
- nominal 型の構築子(struct・enum・list)の残り。保留された cast 境界(決定 25)、
  Fold・Index の role との整合、list の spread・literal。
- presence 付きの data 型と旧い required-field の主型推論器の統合(統合の工程は
  notes/design/2026-11-06-presence-inference-integration.md にあります)。
- 翻訳表の更新(扱った行を「確定」に、変更点を書く)。

## 作業 3: Rust の oracle の設計メモへの追加
notes/design/2026-11-06-rust-oracle-plan.md に、まだ無ければ次の二節を追加してください。

### 3a. 推論の性能設計
Yulang2 の遅さの主因は型推論(コンパイル)でした。次の仮説が正しいか検討し、
Yulang3 の設計でどう避けるかをまとめる。
読むもの: main:notes/benchmarks/、main:notes/design/static-analysis-speed-plan.md、
main:notes/design/2026-08-04-mutable-reference-performance-investigation.md、main:bench/。
1. 標準ライブラリを毎回推論し直すコストが支配的だった。モジュール単位で scheme を cache する
   正しさの根拠として、accepted_export_independent、Scheme が具体化時に再検査しないこと、
   決定 33 を使えるか。cache の無効化の条件は何か。
2. 参照実装の let の選言(DNF)は、右辺を先に推論して純粋なら多相、でなければ単相、と
   一本に決める実装に置き換えられる。そのとき主型性(全 instance の同値)は保てるか。
3. 型 node 対の飽和を、worklist・ハッシュ・union-find で疎に実装する設計。
4. 無限の行を比べる NFA の冪集合は、有限の行や単純な ray の速い道を先に置き、
   重い判定を fallback にする。速い道が重い判定と同じ答えを出すことを、どう縛るか。
5. scheme の簡約(TypeSimplification)が、具体化のコピーのコストをどの程度抑えるか。
6. ベンチを先に決める: bench/chain_2000.yu、bench/infer_simple.yu、bench/loop_*.yu などのうち、
   Yulang3 の推論器で最初に動かすもの。
仮説が間違っていれば、その根拠を書いてください。

### 3b. host act と FFI
Yulang2 の host に触れる機能(console、time、file、net/server)の設計を読んで、
Yulang3 の oracle の host 境界を書いてください。
読むもの: main:lib/std/io/{console,file,net}.yu、main:lib/std/time.yu、
main:docs/language/{file-resource-contract,server-resource-contract,contract-v0-evidence,
contract-v1-file-evidence}.md、main:notes/design/2026-07-02-host-act-ffi-decisions.md、
host ABI v0 の記録。
1. host の操作を act の operation として宣言し、Rust 側の handler が応答する形。
2. Lean の評価器(request tree)と Rust の oracle の差分テストのために、host の応答を
   スクリプトした列として与えられる設計(記録と再生)。
3. host に触る effect が型の行に載ること、保護と解除が host の境界でどう働くか。
4. 資源の寿命(file の開閉、server の接続)の契約を、Yulang3 でどう保つか。
5. ABI を小さく保つ方針と、導入の順序(console → time → file → net の提案)。
Y2 の仕様のうち、Yulang3 で変える必要があるものは、質問にしてください(自分で決めない)。

## 最後の返信に含めてほしいこと
1. 追加・修正した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所、意図して外した所
3. ビルドと Audit の結果の末尾
4. notes/questions/ に積んだ新しい問いの一覧
```
