# Approved answer: initialization order and global effect handling

Question ID: 2026-10-16-forward-definition-initialization-context
Question revision: 1
Approved draft ID: forward-definition-initialization-context-a1
Approved draft revision: 2
Approved draft SHA-256: 5169884bbcbc5fff5b4a6633c69983fdd7bf2f775780645532bb578673069b57
Draft history locator: answer-draft.md (the complete revision 2 displayed in the immediately preceding assistant response); answer-draft-revision-1.md is unapproved history excluded from this decision and integration scope
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: runtime baseline 35e87f844; question inspection 66202b0da; draft observation HEAD 2e25a510dac2cc70c85b067de8dd1485edf0ed84
Question SHA-256: 900cd3b5c946593a3738ddc97c3010cb4279f33ce4f8e7118d77a6ea30c90b07
Task/thread locator: this answering conversation; stable message/thread URL unavailable
Governing source/section: user's explicit replacement decision in the exact draft below; question.md revision 1; notes/design/2026-10-16-module-expression-source-owner.md; questions/2026-10-16-resumed-definition-materialization/approved-answer.md; notes/design/2026-10-04-questioner-integrated-answer-handoff.md §§2–4
Status: approved; finalized local publication; questioner integration pending

## Exact approved draft content

<!-- BEGIN EXACT APPROVED DRAFT -->
# 回答案：初期化順序とグローバルなエフェクト処理

Question ID: 2026-10-16-forward-definition-initialization-context
Question revision: 1
Draft ID: forward-definition-initialization-context-a1
Draft revision: 2
Predecessor/history: answer-draft-revision-1.md (unapproved history; excluded from decision scope)
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: runtime baseline 35e87f844; question inspection 66202b0da; observed HEAD 2e25a510dac2cc70c85b067de8dd1485edf0ed84
Question SHA-256: 900cd3b5c946593a3738ddc97c3010cb4279f33ce4f8e7118d77a6ea30c90b07
Task/thread locator: this answering conversation; stable message/thread URL unavailable
Governing source/section: user's explicit replacement decision below; question.md revision 1; notes/design/2026-10-16-module-expression-source-owner.md; questions/2026-10-16-resumed-definition-materialization/approved-answer.md
Status: draft; approval of this complete displayed text pending

## ユーザーの発言と出所

この回答会話でのユーザーの回答：

> エフェクトが発生していない連続した行のみが交換可能です．したがってエフェクトが発生した場合は先に初期化とかしてはいけません．
>
> エフェクトが発生した場合はグローバルハンドラが処理するか，エラーになります．グローバルハンドラは登録できてもよいのですが，今のところはnondetやioなどが自動的に処理されるのみとします．
>
> 呼び出し元のハンドラが何を意味するかは正直わからないので，選択肢をそのまま選ぶことはできません．

直後のユーザーの補足：

> エフェクトが発生した行は交換できない，が一番近いですね

第1版の全文表示後の、ユーザーによる最新の補足：

> エフェクトが発生した行同士は交換できない，ということで．それ以外はOKです

## 解釈と回答

順序規則の文言には、最新の補足「エフェクトが発生した行同士は交換できない」を用いる。先の「連続した行のみ」や「エフェクトが発生した行自体は一切移動できない」という追加の制限として固定しない。

1. エフェクトが発生した行同士は交換できない。前方参照の値が必要になったことだけを理由に、この規則に反する先行初期化は行わない。質問の両案に含まれる一律のdependency-first timingを承認する回答とはしない。
2. トップレベルの初期化から外へ出るエフェクトは、グローバルハンドラが処理するか、エラーになる。定義の値を読む箇所のハンドラを理由に、その定義の初期化エフェクトが解決されたとは扱わない。
3. グローバルハンドラを登録可能にする余地は認める。ただし現時点の範囲は、`nondet` や `io` などが自動的に処理されることとし、任意のグローバルハンドラを登録する機能の実装は今回の範囲に加えない。
4. ユーザーは「呼び出し元のハンドラ」という説明から選択肢をそのまま選べるとはしていない。本回答は選択肢1・2の選択ではなく、上記の順序・エフェクト処理規則による置き換えとして記録する。
5. 質問側は、この規則と既存の前方参照・依存関係・ソース順の実行需要を対応付け、初期化のentry/returnとエフェクト処理の構成を示す。エフェクトの有無の具体的な判定方式や、未初期化参照の扱いについて、本回答から追加の規則を推定しない。

初期化内部の通常のハンドラ意味論の変更、実装上のowner切替方式、旧A/Bの再開時保存則は本回答の対象としない。本回答だけで到達性・到達不能性・健全性・実装対応の証明やproduction切替の完了を認定しない。

## 確定手順

この回答案第2版の全文への明示的な承認後に、承認発言と正確な本文を含む `approved-answer.md` を保存する。回答ファイルは未ステージ・未コミットのまま残し、質問側のprimaryが検証・統合する。
<!-- END EXACT APPROVED DRAFT -->

## Explicit approval provenance

User approval quote: 「OK」
Approval message/thread locator: the user message immediately following the complete display of forward-definition-initialization-context-a1 revision 2 and the explicit request to finalize that text; stable message/thread URL unavailable
Approval date/context: 2026-10-16, this answering conversation (Asia/Tokyo); exact user-message timestamp unavailable
Revision explicitly approved: forward-definition-initialization-context-a1, revision 2; question revision 1
Authorized scope: the exact approved draft replaces the offered alternatives with the user's ordering and global-effect rules. Effect-producing lines cannot be exchanged with one another; this is not a rule making every effect-producing line individually immovable. Forward demand alone does not authorize initialization that violates that ordering. Effects escaping top-level initialization are processed by global handlers or produce an error. Current scope is automatic handling of nondet, io and similar effects; an arbitrary global-handler registration feature is not included. The questioner must connect the rule to existing forward references, dependencies, ordered roots and actual initialization entry/return. No additional effect-detection or uninitialized-reference rule, concrete owner-switch mechanism, old A/B publication law, proof closure or production cutover is selected.

The earlier quote requesting 「エフェクトが発生した行同士は交換できない」 and stating 「それ以外はOKです」 was followed by the saved and completely displayed revision 2. The present 「OK」 approves that complete revision. Revision 1 remains preserved unapproved history, is not part of the approved decision, and is excluded from the matching integration bundle.

The embedded draft/pending wording is preserved verbatim from the displayed draft. Approval and finalized local publication are established by this wrapper and the actual approval quote, not by changing the approved draft.

Publication: this complete finalized answer was saved after explicit approval. The question, exact approved draft and answer remain unstaged/uncommitted. The answering primary performed no Git mutation. The questioning primary must validate identities, exact contents, provenance, current premises/source revisions, worktree/branch and scope before integrating only the matching question, current approved draft and answer. Preserve the unapproved revision-1 archive without staging or integrating it. Local publication does not establish integration, consumption, proof closure or production cutover.
