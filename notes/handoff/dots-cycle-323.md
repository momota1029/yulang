# dot cycle 323: 局所選定と固定出力の安定化、実引数の共有

2026-11-21 14:30:00 UTC 実測開始。開始時 `integration/m1-final`
`a4c650a07c20367c568fce35ab1fab72d5ab09d8`、standing orders
`7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`、inbox
`b4fd07d0bbc831f8d0b690e9074ca0757357682c`、前回の完了
`f93a1beff669633d09bf10b92dc8542e8260de41` を照合。
I-56 で宣言的な健全性、I-57 の凍結復旧。実行器・Step・journal・slot・停止性は
今回の主張に含めない。設計: [局所選定と固定出力](../design/2026-11-21-cycle323-local-vs-output-closure.md)。

## 先に得た区別: 選定と安定出力は別

- **実際の関連型 RHS と既存 target が固定されたとき、選定行の意味は正確。**
  `OutputExact323.root_exact` は registry 検査・その宣言の可視所属・実際の
  `rootFact` が単一行を返したことの下、任意の普通割当でその行が成り立つことと
  `OutputMeaning` が成立することの同値。明示定義優先と default の位置は
  実 `Supplies` による。名前は変えない。`RootClosure323.models_close` は
  全要求列の行を足すと、元のモデルのうち全出力条件を満たすものが正確に残る
  ことを示す。`OutputRequests323.child_rows_generated` は実 where 発行から
  子の出力名の適格性を自動で得る。対応する checked 宣言・metadata があれば
  その子の全 RHS がコンパイル可能で、等式がすでに真であることは仮定しない。
- **普通等式の追加は実ソースから来ており、head 選定の副条件ではない。**
  `AssocRule323.SourceEquation` は parsed explicit/default body の正規形から
  元の demand target に普通式を作る独立な規則。`AssocModel323.compiler_models_iff_source` は
  任意の状態で、元の綴りの実 compiler 行を足した時と、この source 規則の全式を
  課す時のモデル条件が同じことを示す。`RuleExact323.exact` は実選定捕捉に
  対し、普通状態が実 compiler の出力行を含意することと、独立規則の正規化済み
  出力式を全部含意することが同値。表記どおり行が残っていなくてもよい。
  `AppliedTree323.rule_sound` は任意の普通状態で、実捕捉・where が示せる
  rigid 断片について、この既定の普通規則が実選定箇所で適用済みなら、元の
  診断木に沿って任意の同一モデルに証拠を作る。木の各子の出力名適格性を
  再び仮定しない。全言語の `Local` の exactness や安定化の到達は仮定・主張しない。
- **純粋な選定前段階の反例を、実子列と固定名で確認。**
  `ProvisionalFailure323.provisional_counterexample` は元の Wrap→Container
  の実発行 (point 3, item target 5) と二段の候補／下界／非 K2 選定を保って、
  子の普通行 5=3 だけを外した。出力 5 が int で、実引数 3 は pair の
  実モデルが親の既存式 6=Wrap(5) を含む全残存制約を満たす。
  証拠の側で別の捕捉や別名の子需要を選び直しても、親までの意味が矛盾
  する。したがって「発行構文までの暫定選定だけで `Compiles`」は偽。
  これは承認済みの安定状態の受理に反例を出したものではない。
  `ProvisionalClosure323.closed_model_iff` は実行器の操作でなく普通行
  5=3 を戻すと元のモデル集合そのものに戻ると示し、同じ診断に対して
  全モデルに再帰証拠、かつ実際に一つ以上モデルがあることを検証。
- 補遺 5–7 を維持。`OutputOrigins323.backed_unchanged` と
  `probing_unchanged` は、片付いていない owner の出力行を普通状態に足しても、
  元の出所を保つ限り、支持付き下界観測・正の構文照合は変わらないと示す。
  新行自体は普通に真で、片付けば新たに支持になる。**普通グラフで判定する
  K2 は不変とは言わない。** 仮の診断を任意の追加後にも使い回せるという
  主張ではない。

## 何が同じ型変数の actual を強制するか

- **既存の普通名で真に見えた actual を共有する。**
  `TraceExpand323.expands` は任意の有限 `Trace` から、各位置の実名を消さず
  通常導出付きの実構文に展開。`TraceCapture323.anchored` は最初の実位置の
  既存名を使い、普通 alias が全同一 binder 出現をつなぐ時に
  `trace_shared` が全モデルで共有を作る。
  `RigidProbe323.direct_variable/scalar_probe/nominal_probe` はそれぞれ
  変数の明示中心、同じ scalar の二端、候補の実 nominal 許可下界 trace と
  普通上界から、実の観測列を作る。上界を候補調査の根拠にはしない。
- **共有に必要な条件と、論理名を新しくする条件を分離。**
  `RigidBatch323.batch_exact` は変数・scalar・共変 pair・不変 nominal の
  実 source 観測に対し、固定捕捉の head 全行と、各実出現の値がその捕捉に
  一致することが任意のモデルで同値。`fresh_head_iff` は必要なとき最初の
  複合項に保存的な新名を定義しても、head 全行が真になる必要十分条件は、
  元の全モデルで同一 binder の実出現が一致することだと示す。別々の
  実値を新名で隠せず、既存の関連型 target を差し替えない。
  `ActualPoint323.at_point` は普通式の共通縮退区間から同値を導く。
  `ProjectedSharing323.share` は実構文の pair/tag/nominal を通る普通の
  片方向の比較が、一度でも不変引数を通れば対象の実値で両方向になる
  ことを証明。共変の位置だけでは含意しないモデルも検証。区間の
  交差条件や上下端の一致だけを、実中心の一致に読み替えない。
- **検査済み実例で二箇所を一つに。**
  `RepeatedResolve323.genuine_repeated_inhabited` は二引数の同一 binder
  nominal head を持つ実チェック済み宣言で、lower の投影名 3 と 7 を
  普通の 7=3 でつなぐ。actual の root 1/11 の式を仮定しない。
  最初の実名 3 の同じ点三端で where 子を一つ発行し、同じ辞書を
  普通モデルで証明する。別名の actual を一つのモデルの選択で捏造していない。

## 正規化源への追加の接続

- `RecordWalk323.closed_record` と `StructuralScan323.head_row_exact`: 閉じた
  field 正規列（同じラベルを重ねない）や単一 tag は実投影に対して正確。
  `RecordResidual323.reconstruct_with_terminal` は既知の正準 record から
  指定 field だけを引いた残りを計算する。幅終端と exact 終端を混ぜず、
  独立して保存する。`RecordHead323.permuted_head` はその残差を実 tail に
  読み、可視 field の source 順が違っていても、所与の対応を使い実 head 行
  を証明。任意の開いた goal の差し引きを求めたり、尾が未知のまま候補を
  選んだりする規則ではない。exact 終端を保つ inhabited な実 source
  断片を `RecordFixture323.closed_nonempty` で検証。
- `PlainCapture323.actual_probe/tag_head`: 承認済みの同じ tag の plain
  変数群は、実 `GeneralNominalInspection.translate` が一つの payload を
  複数の binder に渡すので、各名が**全体**を取る。通常の union 等式だけでは
  分割された別値を排除できないことを `PlainFixture323` のチェック済み
  source 例で区別。`PlainK2323.k2_exact` はこの実 query で K2 が調べる
  のは tag の根だけで、payload の変数位置をさらに調べないことを示す。
  任意の複数 tag・残存 join の全正規化は未証明。

## 受け入れ状況と次に残る橋

- **(4) 宣言的健全性: 残り 1 本（一般 source の局所 exactness）。** 木を
  同じモデルで組む部分と、固定した出力 RHS がどの通常規則から来るかは
  切り分けて証明。一般の承認済み候補判定から、全可視候補の消去／保留、
  lower support と K2 の実際の正規化、非 rigid を含む actual 投影と
  同一 binder の共有・集約端、複合 where 名および選定出力の適用済み状態までを
  一つの独立した source 定理に結ぶ義務は残る。RHS の追加前の反例は
  新しい拒否規則を要するものではない。C321 の未決診断優先順位は決めて
  いない。他の承認が必要な言語選択は見つけなかったので質問ノートなし。
- **(2) 停止時の部分正当性: 残り 2 本。** solver 到達状態からの普通状態の
  正確な射影と、成功停止時の診断木がその状態の宣言的分類と一致する証明。
  この周は着手していない。停止性、Rust、物理 solver 全体は証明・実行なし。

## I-57 と検証

凍結ファイル `lean/Audit.lean` と `lean/README.md` は、復旧のみの commit
`f41f5e330d0c088dc63e3cf73a29450295ebf642` で integration の既存
Git blob ID `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9` と
`9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a` を参照して戻した。
復旧 commit の変更パスはこの二つだけ、work branch の読戻しで ID が
一致。以降の公開対象から両パスを除外した。本体の本文を読み書きしていない。

- [検証一式](../verification/cycle323/)。対象 44 module の `lake build … --wfail`
  は 1104 jobs / 0（新 module 名を指定した scoped build、全体ビルドは未実行）。
  44 本全ての個別 source `--trust=0 -DwarningAsError=true`、相互 import なしの
  5 本の独立 audit、新旧 source 発行名を別ファイルで検査した exact readback
  の全終了コードは 0。`#check` の 210 定理の型（暗黙引数を含む）は
  `theorems-00.txt`〜`theorems-10.txt`。
- Scoped axiom gate: 61,734 宣言、0。新しい宣言の型・値の依存を別に辿ると
  576 宣言 / 5,402 依存定数、禁止した実行器・帳簿への依存なし。
  `bash tools/verify-lean.sh . acc3ba790 --no-build` は 0。
  REVIEW 1 件は doc comment の行頭の「syntax;」への機械反応で、該当箇所を
  人手で確認し構文拡張ではない。Lean 差分に削除行はなく、barrel に新 module
  全 44 本を同じ変更内で追加。凍結復旧は別 commit、本サイクルの Lean 差分は
  両凍結パスを含まず、切詰めを示す目印も検出しなかった。
- 進捗・中間成果は心拍付きで複数回公開した。最大ハートビート間隔 9 分 24 秒弱。
  報告前に実 live head `d6eed682d0efff096887f4e9c33b9b06d1a00aff` の
  84 変更パスと barrel 44 行をバイト単位で再照合した。
- 15:20 UTC（開始から 50 分）に報告作成。使用量上限の残りは不明。
