# Approved answer — source-owned original registry construction

Question ID: `call-reify-registry-construction`
Question revision: `q3`
Approved draft ID: `call-reify-registry-construction-q3-answer`
Approved draft revision: `d1`
Draft history locator: `answer-draft.md` (unchanged complete displayed draft)
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: `e8e037ecf`, `fe3a73734`, `c0d304113` (approved question premises)
Task/thread locator: this answering conversation; stable external identifier unavailable
Governing sources: matching q3/question.md and the sources listed in the exact approved draft below

## Exact approved draft content

# 回答案 — ソース所有の元レジストリ構築を設計する

Question ID: `call-reify-registry-construction`
Question revision: `q3`
Draft ID: `call-reify-registry-construction-q3-answer`
Draft revision: `d1`
Predecessor/history: approved q2/d1; this draft has no earlier revision
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: `e8e037ecf`, `fe3a73734`, `c0d304113` (question premises)
Task/thread locator: this answering conversation; stable external identifier unavailable
Governing sources: q3/question.md; `notes/design/2026-10-10-call-reify-construction-direction.md`; `notes/theory/2026-10-10-selected-source-p-old-construction-attempt.md` §§4–5; `rules/design-authority.md`; `rules/compiler-engineering.md`

## ユーザーの言葉と解釈

直前のユーザーメッセージ:

> まあ2で良いと思います

これを q3 の選択肢2の選択と解釈する。

## 決定する設計範囲

ソースの登録段階が元レジストリ `P_old` の構築を所有する、明示的な設計ゲートを開く。実際の登録から元レジストリの型付きキー・ペイロードを形成し、検索・復号で同じ完全な登録情報を取り出せることを示す設計を作り、独立レビューにかける。

設計は、未登録の場合、alias・共有、元のスコープと登録の同一性を扱う。必要な登録の漏れと由来不明の登録がないこと、および利用側の完全な依存情報と規則も別の義務として明示する。既にこれらの証明や `P_old` の構築が成立したとは扱わない。

既存のソースの振る舞いと、`f 1` の完全 Call 契約を保持する。効果、保護、admission、licensing、image、provider/world、pending/future、principality の要求を弱めない。採用済み q2 の四つの選択を維持し、別種別 `N_arg`・`N_lit` の登録を元レジストリの登録と同一視しない。別の未採用 `RuleCall_L` 案も、この回答では採用しない。q1 は未回答の履歴として保持する。

許可するのは、この限定された構築設計と独立レビューである。未作成の具体規則の成立認定、コンパイラ実装、`f 1` の受理、完全な求解、公開、F5 切替は許可しない。新たなソースの振る舞いの変更が必要になれば、その部分は別の判断に戻す。

## 承認と受け渡し

この全文を q3/d1 として表示し、この版への明示的な承認後に `approved-answer.md` を保存する。現在は未承認の回答案である。

回答者は回答ファイルだけを変更し、Git 操作を行わない。回答は未ステージ・未コミットで保持し、質問者が対応する質問・回答案・承認済み回答を検証して統合する。

## Explicit approval provenance

User approval quote: 「OK」
Approval message/thread locator: user reply immediately after the assistant displayed the complete q3/d1 draft and asked 「この q3/d1 を承認する、でよさそうかなぁ？」; stable external message/thread identifier unavailable.
Approval date/context: session environment date 2026-10-09, Asia/Tokyo; precise approval timestamp unavailable. The 2026-10-10 directory/source dates are preserved source metadata.
Revision explicitly approved: `call-reify-registry-construction-q3-answer` / `d1`, matching `call-reify-registry-construction` / `q3`.
Authorized scope: select Option 2; open a bounded, independently reviewed design gate for a source-owned original registry constructor, including original typed key/payload formation, lookup/decoder correspondence, absence, alias/sharing, exhaustive entry coverage, and complete consumer laws. Preserve existing source behavior, the complete Call contract, and adopted q2 choices. No certification of unconstructed rules, compiler implementation, f 1 acceptance, complete solving, publication, or F5 cutover authority.

The embedded draft's pending-status wording is preserved verbatim as approved historical content. This provenance records its subsequent explicit approval.

Publication: finalized local answer, unstaged/uncommitted. The answering primary performs no Git mutations. The questioning primary discovers and validates the matching question/draft/answer bundle, integrates it and records consumption. Local publication does not itself establish integration or resume another goal. Preserve finalized content; corrections require a new linked question and renewed approval.
