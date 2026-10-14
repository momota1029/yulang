# 承認済み回答 — ローカル公開、未統合

Question ID: negative-formal-permission-field-law
Question revision: q1
Approved draft ID: negative-formal-permission-field-law-answer
Approved draft revision: r1
Draft history locator: answer-draft.md（承認時の全文を保持）
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): 質問記載の a729cab9fd6e21c0303c30fa6a047b58f6ba9bf8、4555abdd4。現在との差分検証は質問者が統合前に行う。
Task/thread locator: この回答会話。メッセージID・URLは取得不可。
Governing source/section: notes/design/2026-10-10-annotation-effect-hygiene-integration.md §§1, 4、および承認された回答案内のユーザー発言。

## Exact approved draft content

# 回答案 — 未承認

Question ID: `negative-formal-permission-field-law`
Question revision: `q1`
Draft ID: `negative-formal-permission-field-law-answer`
Draft revision: `r1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): 質問記載の `a729cab9fd6e21c0303c30fa6a047b58f6ba9bf8`、`4555abdd4`。現在との差分検証は質問者が統合前に行う。
Task/thread locator: この回答会話のユーザー発言。メッセージID・URLは取得不可。
Governing source/section: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 4、および下記の現在のユーザー発言。

## ユーザーの発言

> エフェクトに関して，`io.read_int()`は内部の引数に書いてありますが，これはそもそも具体化された`io`なので引き算が効きます．これは注釈の影響ではありません．`outer(incrment)`の場合に意味があり，`outer`は`increment`の`io`を処理します．

## 回答者の解釈と回答範囲

具体的な式から分かる `io` の引き算と、反変注釈から得る局所的な差し引き許可を区別する。仮引数 `cb` の型に書かれた `[io]` は、その位置のエフェクト変数から `outer` 内で `io` を差し引く許可として意味を持つ。`outer(increment)` では、渡された `increment` に由来する `io` を `outer` が処理する。

回答者が説明に用いた `cb(io.read_int())` の `io.read_int()` は、具体的な `io` 自体により引き算が可能であり、この注釈が許可する範囲の違いを示す比較例になっていない。その例を根拠としてA/Bの選択を求める説明を撤回する。

この回答はA/B/Cの完全なフィールド対応を選定したものではない。質問者は、上記の区別を保ったうえで、既存の注釈方針からなお決まらない点があるかを再確認する。残るなら、実際の差し引き処理、許可を付ける元の注釈位置と対象変数、各案で何が異なるかを明示して質問を具体化する。

元の条件付きフィールド対応研究そのものを反証したとは扱わない。具体的な行全体の無条件な消去、ソルバ表現、ソース受理、一般定理の成立、コンパイラ実装、F5移行を承認するものではない。

## 承認と保存

承認対象は上記の回答案 `r1` 全文。明示的な承認後にのみ `approved-answer.md` を保存する。回答者はGit操作を行わず、質問者が対応する質問・回答案・承認済み回答を検証して統合する。

## Explicit approval provenance

User approval quote: OK
Approval message/thread locator: この回答会話で、回答案 r1 全文の表示と「このr1を回答として確定してよさそうかなぁ。」という承認依頼に直接続くユーザー発言。メッセージID・URLは取得不可。
Approval date/context: セッションの環境日付は2026-10-13。承認発言の正確な時刻は取得不可。
Revision explicitly approved: negative-formal-permission-field-law-answer / r1、質問 q1 に対する表示済み全文。
Authorized scope: 具体的な io 自体の引き算と反変注釈の局所的な許可の区別、回答者の比較例の撤回、質問者への残る未決定点の再確認・具体化要求。A/B/Cの完全なフィールド対応の選定、研究自体の反証、行全体の無条件消去、ソース受理・一般定理・コンパイラ実装・F5移行の承認を含まない。

Publication: 明示承認後に本ファイルを最後に保存し、ローカル公開した。回答案と承認済み回答は未ステージ・未コミットで保持する。回答者はGitを変更しない。質問者が対応する質問・回答案・承認済み回答の同一性、承認由来、前提の鮮度と範囲を検証して統合する。統合・消費の完了を意味しない。確定内容の訂正には質問者の新しい関連質問と再承認が必要。

Approved draft SHA-256: efd3752a40143f42e53dfa377d2420e0f9213ef1b58abb4649431f59f3de66ab
