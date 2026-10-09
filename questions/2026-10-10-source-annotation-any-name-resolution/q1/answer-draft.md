# 回答案 — 小文字 any を組み込み型名にする

Question ID: `source-annotation-any-name-resolution`
Question revision: `q1`
Draft ID: `source-annotation-any-name-resolution-q1-answer`
Draft revision: `d1`
Predecessor/history: none for this draft
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: `2434abf06`, `95b27279b`, `1c185235c` (question premises)
Task/thread locator: this answering conversation; stable external identifier unavailable
Governing sources: q1/question.md; approved `source-annotation-typed-root-bridge/q1/d1`; `notes/theory/2026-10-10-source-owned-annotation-any-design.md` §§2–4; `notes/progress/2026-10-10-source-annotation-any-resolution-owner-audit.md` §§1–4

## ユーザーの言葉

この回答会話の直前のユーザーメッセージ:

> ①は具体案の採用が良さそうなのですすめてほしいかな．②は`any`って名前で組み込みにしたいね．

## 解釈と提案する決定

②を、選択肢1の組み込み型名方式を採用し、そのソース表記を大文字 `Any` から小文字 `any` に変更する判断と解釈する。

型名の解決で、小文字の `any` は宣言や import なしで組み込みの型に解決する。組み込みの解決を優先し、同名の型宣言・import・alias でこの意味を上書きできない。同名の宣言そのものを許すか、どう診断するかは、この回答では決めない。

選択された一例の表記を `my widened = 0 as any` とする。大文字 `Any` の組み込み別名は追加しない。大文字表記を普通の名前として扱う規則は、この回答の決定範囲外である。理論資料の意味記号 `Value(Any)` 等をソース表記と混同しない。

次に、この名前解決結果を実際のソース位置とスコープに結び付ける詳細設計を進める。完全な ordinary Value(Any) root、membership の guard・evidence、hereditary Top law、Direct proof は別途構築・確認する。この名前規則だけでそれらが成立したとは扱わない。

決定範囲はこの型名の導入・解決規則と一例の表記変更に限る。値名前空間での `any` の扱い、型の意味関係、注釈境界の振る舞い、実行時動作、コンパイラ実装、production routing、F5 切替は許可または変更しない。

## 承認と受け渡し

この全文を q1/d1 として表示し、この版への明示的な承認を得てから `approved-answer.md` を保存する。現在は未承認の回答案である。

回答者は回答ファイル以外を変更せず、Git 操作を行わない。質問者が対応する質問・回答案・承認済み回答を検証して統合する。それまでは回答ファイルを未ステージ・未コミットのまま保持する。
