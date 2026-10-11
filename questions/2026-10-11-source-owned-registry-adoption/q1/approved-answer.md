# 承認済み回答 — `invoke` 用のソース所有レジストリ案を限定範囲で採用する

Question ID: `source-owned-registry-adoption`
Question revision: `q1`
Approved draft ID: `source-owned-registry-adoption-q1-answer`
Approved draft revision: `d1`
Draft history locator: `answer-draft.md`（表示済みの全文 d1。変更なし）
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: question premises `18049fc9af145ebf558fa189503df07d5c2b9191`; frozen candidate integrated at `fdda52fd8`, SHA-256 `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`
Task/thread locator: この回答の会話。安定した外部識別子はない
Governing sources: `questions/2026-10-11-source-owned-registry-adoption/q1/question.md`; `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` §§1–4; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`

## 承認された回答案の全文

# 回答案 — `invoke` 用のソース所有レジストリ案を限定範囲で採用する

Question ID: `source-owned-registry-adoption`
Question revision: `q1`
Draft ID: `source-owned-registry-adoption-q1-answer`
Draft revision: `d1`
Predecessor/history: 先行する回答案なし
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: question premises `18049fc9af145ebf558fa189503df07d5c2b9191`; frozen candidate integrated at `fdda52fd8`, SHA-256 `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`
Task/thread locator: この回答の会話。安定した外部識別子はない
Governing sources: `questions/2026-10-11-source-owned-registry-adoption/q1/question.md`; `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` §§1–4; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`

## ユーザーの言葉と解釈

直前のユーザーメッセージ:

> 1で

これを、質問 q1 の**選択肢1「限定された候補 API を採用する」**の選択と解釈する。

## 決定する範囲

提案書 `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` §§1–2 と、同書が固定するレビュー済み候補（`fdda52fd8`、SHA-256 `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`）に従い、解決済みの**非再帰な formal / Name / Int の Call 前部分**に限って、次の6つの表現・API上の選択を採用する。

1. **ソースキーと完全なレシピ**: キーを「ソース版・実際の所有者出現・役割」の組で識別し、順序付きの完全なスキーマと有限の宣言トークン閉包を持たせる。終点の値が同じというだけで、キーや所有者をまとめない。
2. **型付き復号前の不変レジストリ**: ソース・文脈・レシピ構文を保持する `P_old^src = Seal(I_syn, Keys, R)` を先に作る。実行時評価値、完成済み Code、再帰的に埋め込んだ WellFormed 証明は格納しない。検索は該当レシピか、外部照会に対する正確な不在分岐を返す。WellFormed と型付き復号は、その同じ `P` から導く。
3. **ソース所有者・登録コンストラクタ**: Header から、所有ポート宣言とライセンス、完全な Value Entry、`Reg_src`、共有 invocation anchor の順に構成する。Result 登録も Header とポートを登録前に構成する。この所有者・ポート許可が与えるのは、明記された所有者、ポート、宣言全体、スコープ対応だけで、元の寄与ライセンス、C0、実行中の権限までは与えない。
4. **共有された順序付き復号とソース生成 image**: Formal の同じキーを Name 利用や alias の間で、同じソース登録と証明選択のまとまりを保って復号する。`J_a/J_f` は提案書の Data / Return / Prefix 全体に対するコンストラクタ規則と完全な局所カタログから作る。これはこの提案上のソース生成 root であり、q2 の `J_lit` や別途固定された旧 image と同一視しない。
5. **復号後の完全な consumer API**: 元の依存引数と同一の完全な `P` を SourceRef、元の application、完全レジストリ観測に渡す。既存の局所 guard、domain、証拠、選択肢、将来用フィールドを保ち、レジストリに情報があることだけで admission、guard の成立、証拠の存在を主張しない。
6. **操作全体と定義域境界**: ソース・レシピ・スキーマの各フィールド、共有された選択、提案書で定義する適法な操作を一緒に運ぶ。外部の不在は全単射な名前替えで保ち、埋め込み写像では運ばれた像の中の不在だけを保つ。単射でない置換で別々のソースキーを統合しない。

候補の7つのソース行と Law / Formal / Data / Result / Image の段階は、この定理断片の範囲を表す。プログラム全体を7行に制限したり、言語上の拒否規則や、後続の Call・再帰的所有者の代わりにしたりはしない。メモリ確保の配置、走査用コンテナ、内部実装名は、これらの定義を満たす範囲で後から選べる。

## 採用が意味しないこと

この選択は、上記 fragment について、以後の設計・ソース宣言との対応調査にこの候補表現を使うことを決めるもの。**別途固定された既存の元レジストリと同値だとは主張しない。** また、実際の Parameter / entry / Force / rebind / Int / Return / Prefix / scope / reference / world 宣言が、この API の完全な引数をすでに供給すると認定するものでもない。残るソース対応を調べ、欠けている引数や不一致があればそのまま記録する。

完全な Call 契約と q2 で採用済みの選択は維持する。したがって、この回答だけではコンパイラ実装、`f 1` の受理、型の求解、一般化、principality の完了、公開、F5 切替は許可しない。`RuleCall_L` 拡張も採用しない。完全な Call の効果・保護・admission・licensing・image・provider/world・pending/future・principality の要求も弱めない。

## 承認と受け渡し

この全文を `source-owned-registry-adoption-q1-answer` の d1 として表示し、この版への明確な承認後に `approved-answer.md` を保存する。現時点では未承認の回答案。

回答者は選択した質問の回答ファイルだけを書き、ステージ・コミット・push などの Git 操作を行わない。質問者が質問・回答案・承認済み回答を検証して統合する。


## 明示的な承認の記録

ユーザーの承認文言: 「OK」
承認の会話位置: 回答者が `source-owned-registry-adoption-q1-answer` / d1 全文を表示し、その版の承認を求めた直後のユーザー返信。安定した外部メッセージ識別子はない。
承認日・文脈: 2026-10-11、Asia/Tokyo のこの会話。正確な時刻は記録されていない。
明示的に承認された版: `source-owned-registry-adoption-q1-answer` / d1、質問 `source-owned-registry-adoption` / q1 に対応。
承認された範囲: 非再帰な formal / Name / Int の Call 前部分について、提案書 §§1–2 が特定するレビュー済みの6つの表現・API選択を採用する。既存の別個に固定された元レジストリとの同値性、実ソース宣言との完全な対応、コンパイラ実装、`f 1` の受理、求解・一般化・principality の完了、公開、F5 切替は承認範囲に含まれない。完全な Call 契約と q2 の選択を維持し、要求を弱めない。

公開状態: ローカルで確定した回答。未ステージ・未コミット。回答者は Git 操作を行わない。質問者が対応する質問・回答案・承認済み回答を発見・検証して統合する。ローカル公開だけでは統合や別会話の goal 再開を意味しない。確定後の内容は編集せず、訂正には新しい関連質問と再承認が必要。
