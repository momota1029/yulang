# 回答案 — 未承認

Question ID: `recursive-self-initialization`
Question revision: `q1`
Draft ID: `recursive-self-initialization-answer`
Draft revision: `d1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `3209e890a0d3c6d96121f64339e9513905f54875`（質問 q1 の記載）
Task/thread locator: unavailable; this answering conversation has no exposed thread identifier
Governing source/section: `question.md` q1 の Governing source/section に記載された資料。特に `notes/theory/successor-proof-obligations.md` REC_INIT / RAW_SOURCE、`notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` §§1, 5–8, 12、`notes/design/2026-10-02-source-result-synthesis-choice.md` §4、`notes/design/2026-10-02-typed-computation-core-elaboration.md` §§3–4, 6。

## ユーザーの発言と出所

この回答会話の直前のユーザーメッセージ:

> 1かな．型推論はできるけど型解釈後の実行を選べない

## 発言の解釈

選択肢1を提案する。型推論の結果が得られることと、実行可能な解釈が成立することを分ける。この発言は選択の意向と理由であり、本回答案 d1 全文の承認としては扱わない。

## 提案する決定と範囲

1. 質問 q1 の正確な単独再帰定義 `my f = f` は、サポートする実行可能ソースの範囲から除外する。
2. 既存の F4 の範囲における型推論と、その未 seed の自己参照に対する `Never` という推論結果は維持する。推論結果を得ても、この定義の実行許可にはならない。
3. この定義を実行対象として受理する判定で決定的に拒否し、初期化の実行および右辺の自己読み取りを開始しない。拒否理由は「この自己参照による初期化では、実際の値を構成する実行可能な解釈が成立しない」とする。具体的な診断文言や実装段階の配置は、本回答では指定しない。
4. ソースと実行の対応を示す証明では、この形の成功する実行を要求せず、上記の実行前の拒否を扱う。実行時の未初期化エラー、非停止、または特別な値の構成を、この形の実行意味として選択しない。
5. 範囲は質問 q1 の `my f = f` のみに限る。他の再帰初期化、相互再帰、再帰関数、一般の `Never` 型の式について、受理・拒否や実行規則を拡張しない。既存の型推論・結果合成・関数クロージャ構成の決定を変更しない。
6. 本回答は、この限定された意味上の選択の引き継ぎである。コンパイラ実装の開始や production cutover を単独では承認しない。質問者による検証・統合と、必要な設計記録・独立レビューの手順を経る。

## 承認対象

承認対象は質問 `recursive-self-initialization` q1 に対する本回答案 `recursive-self-initialization-answer` d1 の全文。

Pending status: 回答案は未承認。回答者は Git 操作を行わず、回答ファイルは未ステージ・未コミットのまま保存する。明示的承認後に `approved-answer.md` を最後に保存し、質問者が一致する質問・回答案・承認済み回答を検証して統合する。
