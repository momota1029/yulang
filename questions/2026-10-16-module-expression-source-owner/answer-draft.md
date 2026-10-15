# 回答案：モジュール直下の式の所属

Question ID: 2026-10-16-module-expression-source-owner
Question revision: 2
Draft ID: module-expression-source-owner-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: question baseline 6e3eb6496; HIR/solver owner baseline 0a9af0da5; observed HEAD c52345489dfc1617f70b7611f2401315ae7beeb2
Question SHA-256: 25c9d591e35f5358cceffe95b83b4f4bca8f7d3a2ed3981b4b7b33425156c430
Task/thread locator: this answering conversation; stable message/thread URL unavailable
Governing source/section: question.md revision 2, Recommended concrete extension §§1–3 and Implementation and proof gates; notes/design/2026-09-20-hir-direct-root-expression-slice.md; notes/design/2026-10-11-yulang-inference-top-level-principles.md
Status: draft; approval of this complete displayed text pending

## ユーザーの発言と出所

この回答会話の先行ユーザーメッセージ：

> ②は提案1で良いんじゃないですか．`my _ = ...`とおなじで良い

作成依頼（この回答会話の現在のユーザーメッセージ）：

> じゃあ②だけでも回答を作成してはどうですか

## 発言の解釈

`my _ = expr` との同等性は、モジュール直下の式をソース順に評価し、その結果を捨てるという動作を指す。内部表現は質問第2版の提案1に従い、元の式自身の識別情報を保持する。

## 回答

質問第2版の提案1を承認する。具体的な範囲は、上記SHA-256で特定した質問の「Recommended concrete extension」§§1–3と「Implementation and proof gates」に従う。

1. 実在する直接ルートのHIR出現箇所に結び付いた `ExpressionRootId` を持たせ、`SourceRootId` で定義と式を表す。既存の定義・出現箇所の識別情報を保持し、架空の定義やLambdaを作らない。
2. 型推論の受け渡し先を `SourceReceiver` へ拡張する。式の本体はレベル1とし、内部のローカルなレベル規則と既存の定義参照・capture/FreshUseを使う。式の結果を定義の型スキームとして一般化・公開しない。定義SCCとValue参照SCCの区別を保つ。
3. 計算を伴う定義と直接ルートの式をソース順に実行する。式が完了したら結果を捨て、次へ進む。式の結果をグローバルな定義キャッシュへ保存しない。
4. ソース上の所属と動的な実行の所属を区別する。関数呼び出し、ハンドラ設置、転送、捕捉、再開には、既存のInvocation/ModuleRunの所属規則を保つ。
5. `--run` は指定した定義を観測する既存の方式を保つ。最終式をモジュールの戻り値とする規則や、新しいCLIセレクタは追加しない。
6. 質問にある原子的なキャリア公開、必要な証拠、停止条件、費用予算を維持し、G2–G4の実装・証明・検証へ進む。本回答は証明の完了やproduction切替を認定しない。

①のresumed-definition-materializationの選択肢には回答せず、その前提や状態も本回答では変更しない。

## 確定手順

この回答案第1版の全文への明示的な承認後に、承認発言と正確な本文を含む `approved-answer.md` を保存する。回答ファイルは未ステージ・未コミットのまま残し、質問側のprimaryが検証・統合する。
