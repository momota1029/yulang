# 回答案 ③

Question ID: `handler-protection-release-crossing`
Question revision: `q1`
Draft ID: `handler-protection-release-crossing-answer`
Draft revision: `d1`
Status: 全文への明示的承認待ち
Predecessor/history: 本質問の先行回答案なし
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s) / Governing source/section: 同じディレクトリの `question.md` q1に記載の基準revisionと出典。未承認の編集は新しい権威として扱わない。
Task/thread locator: unavailable: この会話には安定したmessage/thread locatorが公開されていない。

## 原文と解釈

この回答会話でのユーザー発言：

> ①1 ②1 ③2A

番号の選択として記録する。以下の具体化は回答者の解釈を含み、全文の承認は未取得である。

## 決定案と範囲

1. タイミング2と寿命Aを採用する。独立に `'e` 由来と認められた寄与が、介在する計算・handler処理を経て印付きslotの外へ実際に出たsource transitionで、そのslotの保護を解除する。単なる発生やdispatch前のObserveでは解除しない。crossingの証拠を解除後のhandler imageから循環的に定義しない。
2. 解除状態は印付きtarget viewと元のreceiverに結び付ける。同じreceiverが有効で、同じviewのtyped result／latent transportが証明される間は、後の適格な観測にも引き継ぐ。解除済みviewでの各発生に新たなcrossingを要求しない。未解除viewには最初の適格なcrossingが必要である。
3. 内側のhandlerが最初の寄与を消費し再発生させず、外向きcrossingが起きなければ、その寄与は解除を起こさない。dispatch前の観測と完全な保護証拠は保持する。既に同じviewが解除済みの場合は、その状態を通常の適格性判定で用いる。
4. 後で呼ばれるlatent viewと浅いraw continuationでは、同じviewのtransportと元のreceiverの有効性が保たれる場合に解除を引き継ぐ。浅いhandlerを自動で再装着しない。繰り返す再開も同じ条件で扱う。
5. 明示的な深い再入も実際のsource展開に従う。生存する元のreceiverの同じviewの解除はtransportに従って保持するが、新しいreceiver／保護slotへ自動コピーしない。新しいviewの解除には自身の適格なcrossingを要する。この再開・再入の具体化は回答者の解釈であり、承認対象に含む。
6. receiver終了後に古い解除状態を権限として使わない。provenance、event identity、family／type arguments、row support、typed paths、attachment、元の `(nu,K,D)` と他のslotの保護を保持する。同じfamilyやlineageだけで解除を広げない。
7. 解除はhandler選択、capture権限の付与、消費、row supportの減算を行わない。完全な効果membership、新carrier、compiler実装は承認範囲に含めない。

## 承認と引き渡し

承認対象は `handler-protection-release-crossing-answer/d1` 全文。明示的承認後、この全文と実際の承認発言を含む `approved-answer.md` を最後に保存する。回答者は回答ファイルのみを書き、Git操作を行わない。未統合の回答は未ステージ・未コミットのまま残し、質問者が検証・統合する。訂正には新しい関連質問と再承認が必要となる。
