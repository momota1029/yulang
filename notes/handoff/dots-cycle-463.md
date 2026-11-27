この周に閉じた G の行: **なし。G04 は部分進捗。I-88 で GD が独立し、全24行・残り20行。**

# C463 引継ぎ

- 実開始 2026-11-27T10:30:06.264Z、通常終了下限 2026-11-27T11:20:06.264Z。writer 解放は、この報告と同 commit の completed heartbeat。使用量の枠は不明。
- I-88（inbox `edad65a04924cbc43237401e8952df6eda394782`）で宣言安定性を GD に分離。今回はその入力を使う G04 のみ。権威 `integration/m1-final@e1bee141b33caabcc9b810251c249fc9a9a942b9` / Lean `067944a8e790e8590393e07a2ea1b8715fad22bf` は開始時に C462 を exact に統合済み。今回の [凍結した成果](https://github.com/momota1029/yulang/commit/2360ac05dc28f18061be97905df003f50f854cc8) / Lean `f46b939c052876ad999d19e79629335009aec9c6` は work/dots-main で照合済み。
- 設計: [検査済み宣言と元の訪問位置](../design/dots-cycle-463-i88-author-physical-plan.md)、[同じ raw row と元 AST](../design/dots-cycle-463-i88-original-native-rows.md)、[検査済み head と whole-read](../design/dots-cycle-463-i88-prechecked-head-boundary.md)。

## 実装した証明支援とその境界

- **GD は入力として一度だけ検査**。`prepareTable` は外部から finite data verifier とその健全性を受け、実の解決済み宣言全体を照合し、供給された全証明書が通るとき・そのときに限り同じ順序の表を返す。GD の completeness、任意の StableSmaller 判定は証明していない。request には GD 証明書も key もなく、元 point/role/位置で表を読むだけ。見かけが同じ numeric ID では別の宣言の証明を流用しない。同じ membership なら request の全 read は不変。exact な authoredRegistry の等式のもと、異なる Current でも同じ表を verifier の再実行なしで移す。
- **構造 read の元と物理 row は同じ hop**。`checked_source_and_actual_indexed_report_iff_finite_witness` は外部の表、独立の元 source と、同じ state の exact raw ordinal/Alias/ChildAt/選択位置/terminal K2/report/stamp を有限データに反映し、逆も示す。その同じ row ordinal と元の issuer/route を、全 FitsFull でそれぞれ保持する。単に同じ形の別 row を選ぶ証明ではない。
- **実際に訪問した field の元位置**。`exact_located_report_iff_same_original_finite_wire` は既存の構造 read に元の path の列を添えても、消せば全 wire で元 report/stamp/row と同じであることを示す。既設構造経路なら少なくとも一つ元の literal path がある。返した全候補は同じ最終正規化項になり、`any_located_literal_candidate_zips_with_its_identical_native_rows` は元 path と同じ raw row の実 model evidence を各 hop で対にする。重なった同じ正規化の join の両方は元順で保持し、表示位置に一つを選ばない。既定の構文正規化は必要な構文を見るが、新しい raw open や未訪問子の循環検査は行わない。
- **元 roster の head 位置**。旧 report 支援の単一候補/point/一 where の入口はそのまま。補助 `prechecked_head_field_iff_finite_exact_wire` では全可視候補の実 ordinal と point head 引数 ordinal を合わせ、where なし・複数候補・複数引数でも同じ構造証跡を読む。実対照は二候補・二引数の (1,1) で成功し、用意済みだが変数の (0,1) は field を読まない。これは候補 matching、選定、全候補の K2 の拒否優先の完成ではない。既設累積 checker は全入力に対しそのまま。新しい canonical result/witness 分岐は追加していない。
- **実物の穴**。`Cycle463I74WholeReadBoundary`: 閉じた元 `{30:{40:'a}}`、真正 Ready と表 lookup、実 ordinary SourceHead（`Center.direct` / `EquationRead.whole`）、同じ fitting model と raw slot5 の実 K2 があっても、point4 に inline の row しかなく named な子への raw edge がなければ最初の訪問を証明できない。任意の準備表/全有限 head wire で受領は none。値の同値だけから slot5 をこの元位置と同定しない。Yulang の yes/no を変更する結果ではない。

## 残りと exact 検証

- 実際に訪問すべき inline/bound 元 syntax から named raw row とその issuer/route を生む上流の checked producer、複数候補の matching に接続した K2 の曖昧性前の優先、既存 visitor にない残余 join の境界が G04 に残る。whole-read と older allocator の制限を先に分離し、同じ raw 値・意味だけから新 raw 訪問は足さない。開いた tail は G06/G07、非 point・一般 mode/kind/多引数は G20/G21 のまま。GD、G05、一般 NFR、parser/solver は未着手。spec/表示位置に新判断、質問ノートともなし。
- 実対照: 同じ fitting model、同じ raw rows、同じ field/terminal の plain と元同一 tag 2 箇所、および wrong raw row / wrong 位置 / 同 ID 別宣言 / 空表 / nonpoint / 順序変更・元位置を捨てる対照。元の whole-inline barrier は成功 fixture の欠落判定とは別。
- Lean 4.35.0 `--trust=0 -DwarningAsError=true`: immutable Git byte で focused production 16、独立 Audit 19、公理照合 62（標準のみまたはなし）、guard 7 群（構文 4 と実 read 3）。**Audit の import: Yulang.* 以外 0 件**。旧 production 7847 と旧 Audit 2281 は blob まで全て不変、集約は末尾 16 import 追記のみ。Lean 35追加 + 集約、設計 3、心拍、報告で正確に 41 path。全体 Lake/Rust/`verify-lean.sh`／Yulang2 実機はこの worker では実行していない。
