# C336: I-61 の異なるレコード端点から、実名の捕捉・子・出力を検証

## 今回の範囲と残り

03:30 UTC 枠。開始 2026-11-22 03:26:34 UTC。integration の固定版 3439c6ab4814e937dd58b01b484713e7203cbcbd で standing orders、inbox I-61、spec §4.3・§6.5 を再読。開始 work pin は bf7c80faefdce4b832e92b1cfa154a15247acf70。両 ref の Lean と tools は開始時点で全 blob 同一で、差は spec/06-roles.md のみだった。その最新 spec を規則に使用した。終了前にも同じ integration head を確認した。work/dots-main だけ expected-head / nonforce で更新。証明・独立監査の固定 pin は 9ef7cc13aeeeeef30fc25dadb6dff111d00e214a。

- **(4)** I-60 の従来の証人つき分類は残り 0 群。I-61 の直接 field binder + residual binder 断片は新しい区間証拠で閉じた。一般 I-61 の追補は残り **1 群**。承認済みの compound/nested head 全域の捕捉と、exact な残りを mask の外で使う場合の由来・除去・receipt を、同じ境界に統合する。実行版の新規則を導入したとは主張しない。
- **旧 Local との対応**: 旧 I-60 の成功木は同じ木、実子順、辞書で拡張判断へ写る。旧 Local との到達可能な全域対応は残り **1 群**。C334 の旧 center-withheld 反例を現行 I-61 への反例として数えない。
- **(2) 成功停止の部分正当性**: 残り **2 群**。実 solver の任意の成功停止→現通常状態・由来・literal receipt の供給と、それから返る全診断・辞書・固定出力の同一モデル射影。今回の子と出力は実 declarative compiler のものだが raw solver の成功停止ではない。停止性は扱わない。

## 支持付き端点・区間・現モデル

1. `EndpointRecord336.field_interval` は、任意の普通状態・支持関係・実 capture と、両端の支持付き spine、正規化後に要求順で読んだ field 列について、任意の同一モデルで、真ん中の**必要 field 観測**が存在して両側の実 field の型に挟まることを示す。中心の source 行・完了していない出力行は参照しない。これは単に端点を中心とした証明ではない。
2. `EndpointResidual336.exact_residuals` は同じ実中心から捕捉した label を mask で除く。両端の正規化済み未捕捉 prefix と各末尾をそれぞれ残す。exact-closed と width-open の混在を、同一モデルを持つ実 source `MixedTail336` で確認。未捕捉の任意の label で両尾の区別を保つ。
3. `EndpointProgram336.list_sound` は任意の有限個の直接 field binder と residual binder を、正規化した field 順で読み、反復する binder を落とさない。全 job の値を各元モデルから決定的に検査し、`EndpointOverlay336.approved` が普通の区間 atom と sidecar receipt にまとめて実名を付ける。旧 type/row 名と保護した関連型の出力先を保存。ここでは I-58 の共有等式をまだ足さない。中心のレコードと単一の literal RHS の同値は要求しない。
4. その区別は必要: `EndpointCase336` の実 nonpoint 入力は支持付き上下端と実モデルを持ち、中心行がない。それでも旧 literal `HeadMeaning` は、このモデルでいかなる捕捉表でも偽。required と optional の field が別々に観測されるからであり、I-61 の読み・選定自体の拒否ではない。

## 同じ実 compiler、同じ辞書、選定後だけの共有

- `EndpointBody336.calculate/sound` は C332 の `compileBody` をそのまま使う。独立に得た捕捉名の順と普通 Bounds から、where の実準備・固定 target・出力行・実子リストの意味と現 receipt を得る。旧 literal head 等式だけを前提から外した。通常の named/inline/projected ルートを残した `EndpointInput336.Inputs` に、新しい支持付き区間 record ルートを加えた。
- `EndpointSelected336` は現候補の Elected と実 compiler の結果・普通 receipt・そこに登録された projection receipt を別に要求する。実候補が採用された後の通常 tie batch がちょうど actual center 同値を足す。矛盾なら拒否、中心行が無いことによる追加保留ではない。実装口の主張: 同一の computed tie が不整合なら、その選定を受ける現モデルはない。一般、あらゆる診断が排他的・完全とはまだ述べない。
- `EndpointLink336.selected_centers` は各実 occurrence の中心と、**その body が実際に使う** binder 表の中心が同じモデルで同値であることを証明。`EndpointDictionary336.dictionary_sound` は全ての子に同じ現普通＋projection モデルを使う帰納。旧成功木は `EndpointCompatibility336.old_success` で順序も辞書もそのまま写る。
- 実回帰一: `EndpointRegression336` は異なる field 端点の原型で、レコード中心の元行なしに実際に一候補を選び、関連型の固定出力 **5=7** を発行し、そのモデル付き辞書を検証。
- 実回帰二: `EndpointChildren336` と `EndpointChildModels336` では、exact-closed 下端・width-open 上端の実親から子の実 interval **(13,8,14)** と固定 target **5** を発行。既存の支持付き int 宣言の由来は、field 投影端と singleton 集約の普通 alias を通る。根の出力 **6=11**、子の **5=8** を元 compiler が正確に計算し、両ノードの辞書が一つの実モデルで成立する。新しい field 端点行は I-61 証明由来だけを旧 origin 型へ渡す互換 adaptor で、parser の元行や完了していない出力を捏造していない。
- 実回帰三: `EndpointClashChecked336.regression` は checked な反復 binder 候補を両端で選べる上、tie 前はモデルを持つ。同じ binder の通常 field と residual の捕捉中心を等しくする実 I-58 batch にモデルがなく、`.rejected` を構成する。範囲はこの Lean 型付き宣言。Rust の型付けや実行は今回未検証。

## standalone の閉じた残りは、mask と区別する

- `EndpointResidualSemantics336`: 任意の有限・互いに素な width-open の既知残りでは、mask は standalone の普通表現と同値。exact-empty では、処理済み label の optional 観測で masked 型と standalone 型を区別できる。従って sidecar 試作の masked な出力を、一般の exact な差分としてそのまま公開言語へ使わない。
- `EndpointResidualReflect336.reflect`: 任意のモデル・有限の既知 rigid 残り二つが、同じ除去 label と互いに素であれば、mask 後の順序は standalone の部分型順序を反映する。処理済み optional 照会を両方の残りにない同じ fresh label で照合するため、端点が mixed open/closed でもよい。
- `EndpointResidualLift336.lifted/named`: その順序反映から、任意の支持付き端点・任意の現モデルについて、**元の standalone interval**に入り、外から見える masked 観測が正確な残余を、旧名を変えず保守的に名付けられる。構成は上端と「下端と masked 実残りの join」の meet。点区間、または二つとも disjoint rigid spine なら同値の意味で一意。一般の非点ではまだ一意性はない。実回帰二の入力モデルにも exact-empty と masked exact-empty の**二つの区別可能な候補**がある。これは残りの計算に必要な不在情報を特定したもので、仕様の採用範囲に対する反例や新しい選択ルールではない。

## 検証と次に

25 Lean モジュールの focused Lake --wfail、全 source の直接 trust=0、別ファイル 9 本の独立監査、159 定理の公理照合（Classical.choice / Quot.sound / propext のみ）、範囲限定 gate 65,601 宣言、宣言照合と差分監査が成功。固定 pin の source + 独立監査 34 本は byte 一致を確認し、25 個を新しい C336 オブジェクトに再ビルドして再検証した。612 個の C336 定数の型・値の依存 5,906 件を走査し、物理 solver/state/resolver への禁止依存なし。独立 fresh replay で二段の compiler 後にも支持付き中心行なし、固定の 2 出力を再確認。全ログと再現は [notes/verification/cycle336](../verification/cycle336/reproduce.md)。
凍結 lean/Audit.lean / lean/README.md は本文を読み書きせず Git blob ID を開始時・完了時に比較。lean/Yulang.lean は既存の全 bytes と digest を読み戻し、当該 import の追記以外を変えていないことを毎回確認。全 repo の Lake/Rust ビルド・実行と利用枠の残量は未確認。質問ノートはなし。§4.3 の「取り除く」を actual 型側で保持する実装・証明の残りであり、新たな言語優先順位の選択は行っていない。

次の最小義務は (a) masked モデルを単に再使用せず、普通の standalone での不在情報を保存する exact typed subtraction と authored provenance を接続すること、(b) nested/compound head へ再帰し、実 where/output まで読むこと。この二点が通ったら、(2) の実 solver 成功停止からそれらの receipt を取り出す。
