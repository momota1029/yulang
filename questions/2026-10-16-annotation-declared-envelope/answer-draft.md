# 回答案：注釈の許可と型の減算結果の区別

Question ID: 2026-10-16-annotation-declared-envelope
Question revision: 1
Draft ID: annotation-declared-envelope-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: question baseline 35e87f844; question inspection c6c7a2021; observed HEAD 64c8755568108cf2ceb7f3a61fcfbac9eabaec50
Question SHA-256: 08eba1525b88e869dc9753d650240fc4e10e6cdc8cb17cca906a766b9463488d
Task/thread locator: this answering conversation; stable message/thread URL unavailable
Governing source/section: question.md revision 1; notes/design/2026-10-10-annotation-effect-hygiene-integration.md §1; notes/design/2026-10-11-yulang-inference-top-level-principles.md §1
Status: draft; approval of this complete displayed text pending

## ユーザーの発言と出所

この回答会話での、選択肢の説明に対するユーザーの指摘：

> 実装の振る舞いによるというか型を引き算した結果を得るので，ioを許可してioが入らなければioの入らない結果が出てくるんじゃないんですか

許可・流入・減算後の型を区別する説明への、直後のユーザーの応答：

> そうでしょうね

後者は説明の方向への同意として記録する。本ファイル全文への承認とは区別する。

## 解釈と回答

ユーザーの指摘は、型制約と型の減算から結果を得る通常の推論に関するものである。回答側が提示した「実装の全将来の振る舞いを解析して狭める」という説明と、それを根拠にした選択肢1の推奨は撤回する。

1. 注釈が与える許可、制約を通じて実際に流入するエフェクト型、減算後の残余型を区別する。型制約上 `io` が流入しない場合、宣言に `io` が列挙されていることだけを根拠に残余型へ `io` を追加しない。
2. 反変位置の注釈は、その場所の指定された具体的エフェクトを関数内で処理・減算する許可を与える。実際のハンドラによる減算で、流入型が空なら残余も空、流入型が `io | write` なら `io` を引いた残余は `write` となる。共変位置の注釈は、指定された具体的エフェクトがその場所に現れることを許す。この許可を、実際のエフェクトが必ず流入するという根拠にはしない。
3. 未解決のエフェクト変数を空とはみなさず、既存の制約・減算・フィルタと象徴的な依存を保持する。この結果は通常の型制約の生成・蓄積・伝播から得る。実行トレースや本体の振る舞いを調べる特別な精密化は前提にしない。
4. 質問側は、宣言した注釈インターフェース、流入型、残余型を明示し、完全なFunction比較のどの段階で宣言した具体的メンバーを残すのか、その根拠とソースからの対応を示す。特に、型の減算で得た結果へ宣言だけを根拠に `io` を足し戻す扱いをするなら、その根拠を明示する。
5. 現行の `Support` が宣言した注釈型を表す場合と、実際の流入・残余を表す場合の対応を確認する。本回答だけでその表現の正誤や一律の削除を決めない。同じprovider・代入・型位置・共有変数・相関するFunction各部を保つ既存の比較義務も維持する。

選択肢1・2をそのまま選ぶ回答とはせず、まず上記の区別に沿って質問と構成・比較の接続を整理する。新たな振る舞い解析を承認せず、健全性・principality・FIRST-RESULT-ADEQUACY・production切替の完了も認定しない。

## 確定手順

この回答案第1版の全文への明示的な承認後に、承認発言と正確な本文を含む `approved-answer.md` を保存する。回答ファイルは未ステージ・未コミットのまま残し、質問側のprimaryが検証・統合する。
