# 回答案 — Call の具体案の採用

Question ID: `call-reify-registry-construction`
Question revision: `q2`
Draft ID: `call-reify-registry-construction-q2-answer`
Draft revision: `d1`
Predecessor/history: none for this draft; q1 remains pending history
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: `7b723269c`, `9979ed6c4`, `fc564e68f` (question premises)
Task/thread locator: this answering conversation; stable external identifier unavailable
Governing sources: q2/question.md; approved `original-call-argument-reify-owner/q1/d1`; `notes/progress/2026-10-10-literal-constructor-proof-review.md` §§1–3; `notes/theory/2026-10-10-original-call-reify-constructor-proof.md` §§1–3, 7

## ユーザーの言葉

この回答会話の直前のユーザーメッセージ:

> ①は具体案の採用が良さそうなのですすめてほしいかな．②は`any`って名前で組み込みにしたいね．

## 解釈と提案する決定

①を q2 の選択肢1の選択と解釈する。独立レビュー済みの具体案を、次の限定された設計段階の方針として採用する。

採用する内容は次の四点である。

1. 元のレジストリ束縛を保持し、新しい登録を型付きタグで区別した別のレジストリ種別に置く。
2. ソース構造から作る Call 引数の登録・ライセンス規則を追加する。
3. 新しい引数ペイロードに、保留した処理を扱う suspension の情報を保持する。
4. ソース所有のリテラル image の領域・節・root `J_lit` を構築する。

`f 1` の完全 Call 契約を保持する。効果、保護、admission、licensing、image その他の契約項目を弱めず、四ポートの端点求解を成功条件に置き換えない。`J_lit` と任意の旧 image `J` は別物として扱い、等しいとは主張しない。

次に、実際のソースから `P_old` を構築する責任、その完全な登録内容・lookup/inversion・旧 consumer の依存閉包、および残りの完全 Call 依存条件を、ソースに基づく構築・適合確認として進める。具体案の採用は、これらが既に成立するという認定ではない。q1 は未回答の履歴として保持する。

今回の採用は設計方針に限る。untagged `H_oldext`、完全 Call emission、O0/O1、C0/admission、完全な求解、principality、公開、コンパイラ実装、`f 1` の受理、F5 切替を成立済みまたは許可済みとは扱わない。

## 承認と受け渡し

この全文を q2/d1 として表示し、この版への明示的な承認を得てから `approved-answer.md` を保存する。現在は未承認の回答案である。

回答者は回答ファイル以外を変更せず、Git 操作を行わない。質問者が対応する質問・回答案・承認済み回答を検証して統合する。それまでは回答ファイルを未ステージ・未コミットのまま保持する。
