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
