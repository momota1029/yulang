# C443 / I-80: 宣言的な選択に対する NoFalseRejection と一般化 G

**設計案。未承認・未実装。** 正本 `integration/m1-final@1e763e450d233042505ce99a2ef93c4d98a466a2`、Lean tree `54677fdcb38877f141f5065ea342fd362471afdd`。I-80 inbox `d63b159f0d85bc83ba874602bbf6e755c1f950d1`。[旧 C 一覧の原形](dots-cycle-423-c-coverage.md)、[C442 の保持検証](dots-cycle-442-c22-retention-next.md)。I‑74 の狭い C 一覧は **C01–C21 の代表断片で終了**、C22 は未実装の G00 へ移す。古い C の報告を書き換えず、C22 や一般の完全性を「済」と数えない。C03–C06、C09、C17、C19 の checker true は拒否／保留／曖昧等の正確な**報告**の検査成功で、言語上の受理例ではない。C13 にも独立した拒否側がある。

## 1. 固定する statement の案（Lean 風、定義・定理ともまだ無い）

入力領域は §6 の role 需要を持つ **正準の全 source snapshot** とその実出現。名前解決・可視範囲、実 root/where 出現、B6 が与える元の型付き項、すでにある制約と全出力指定を保つ。型付けや source から B6 への接続を B4 内で再実装しない。データの整合性は checker と独立な `CanonicalFullProblem` として、構文・source 由来・宣言された kind/署名・要求の source 位置一致だけを述べる。局所形状、候補数、出力数、検査可能性、モデルが存在すること、選択に都合のよい規則／候補だけ、終状態を solver が既に作ったことは仮定にしない。正準化が別に必要なら、coverage で「全ての well-formed 原 source/state/request に、保存・反映を満たす表現がある」を証明する。未実装形を input type から消さない。

```lean
-- Proposed interfaces, not implementations or new axioms.
-- P.state is the canonical full declarative state of the SAME source; P.root its request.
def NoFalseRejection : Prop :=
  ∀ (P : FullProblem) (d : Dictionary),
    CanonicalFullProblem P →
    ClassifiesFull R_full P.state P.root (.selected d) →
    ∃ (r : Result) (w : WitnessData),
      ExactSelectedReport_full R_full P.state P.root d r ∧
      check_full P r w = true

def NoFalseRejectionExactReport : Prop :=
  ∀ (P : FullProblem) (d : Dictionary) (r : Result),
    CanonicalFullProblem P →
    ExactSelectedReport_full R_full P.state P.root d r →
    ∃ w : WitnessData, check_full P r w = true
```

第一文は source で選ばれた **同じ辞書 d** の正確な報告の存在 (A)。第二文は指定された**任意の正確な報告 r** を受理できる (B)。この案は A を I‑80 の最小主張、B を明示した追加目標とする。B から A には選択導出から exact report を作る別の補題が要る。A から B には同じ選択の正準な報告一意性（または個々の導出の witness 構成）が要る。旧 checker の report uniqueness を流用して B と同一視しない。scope に対する r の同値性を許す場合も、先に独立な等値／canonical serialize を明記し、勝手に weakened comparison にしない。

`ExactSelectedReport_full` は独立な**一つの**元導出から同時に出る `r.tree`, `r.verdict = .selected d`, `r.writes` を束ねる。正しい d だけ、出力集合だけ、同値な値だけでは足りない。元の occurrence と literal where ordinal、選択 decl/元 registry ordinal、各 output ordinal・名前・既出固定先・元 Body（default の位置置換も）・型付き ordered tree、各書込み位置と multiplicity を保持する。表示用の元 clause 順と、§6.3 の兄弟連言の評価順非依存は別の義務。完了根拠を読む support proof は where 子や書込みに追加しない。merge された需要は元の出現を失わず、正しい合流先の診断位置を持つ。現 `Check408.encodedEventWrites/traceWrites` の元順は参照実装。仕様が言わない wire 発行順は serialization の提案に留める。

`WitnessData` は有限な行・位置・経路・比較・整合／不整合証人等のデータのみを持つ。`ClassifiesFull` や全適合モデルの命題、モデルを入れた witness、決定結果を真として信じるフラグ、`check_full r w = true` をコンストラクタ条件にする仕掛けは認めない。`check_full` は将来の入口で現 `RefPositions441.check`（R21）とは同一でない。入力・表示・kernel とは別に、各木ノードでデータを同じ P から再照合する。

**有限データが課す実効性の監査。** 正準 source の表現と report/wire が有限に符号化でき、`check_full` が全域 Boolean なら、(B) の対象は wire を列挙して半決定できる。(A) は report と wire の組を列挙する。独立な `full_check_sound` を合わせて初めて「探索で見つかったものは正しい」とも言える。失敗側まで決定する、または効率よく witness を合成できる、とは言わない。特に acceptance 導出に現れる型比較・不一致・head 既知／未読の区別・raw 非循環・候補の非該当・merge 後整合／不整合には、必要な極性ごとに**有限の表現と証明になる checker の完全性**が要る。単なる `∀m, …` の意味命題や、合格証人の存在自体を `CanonicalFullProblem` に隠さない。§10 の有限・正則・制約族に限った決定結果を、より広い意味領域全体の有限反映と取り違えない。表現制限が残れば、その正確な source fragment と欠けた極性を当該 G 行に残す。

保留・曖昧・拒否の `ExactDiagnosticReport_full …` と対応する `∀ r, … → ∃ w, check_full P r w = true` は**別の成果**。完全な診断側は元の位置・理由・既に生成された場合の写像も独立に合わせる。旧診断 fixture の no-write が全ての診断に当てはまるとはしない。未対応で check false は意味論的な拒否ではない。qualified な要求が未解決のまま残ることと、具体化された role の selected を混ぜない。EOF でも唯一の impl で未定型を補完しない（§10.14.4）。

## 2. 独立 `R_full` の構成／それぞれの境界

入力を正本 §6.1–6.3、§6.5 の role 規則で分類するものとして定義する。R0〜R21 の branch の和、check の受理集合、`DictionaryEvidence` が成立する入力集合の別名にしない。

1. **Scope と元の正規化**: 呼出し側の module/import/access、EOF の自ファイル可視性、引数の種別と exact 宣言の署名／B6 入力；同じ宣言の重複 import と異なる二宣言を別扱い。グローバル coherence を足さない。相手へ渡された辞書がある場合は勝手に再選択しない。record の hidden field と variant の同タグ合流、nominal の mode と row/value の区別は source の実位置で記述（§10.14, §10.25, §10.27–28）。
2. **観測・K2・候補**: 初めに元 ordinary graph そのものの根 K2（関連型未完の等式も除外しない）。許された実候補観測または実 where 子で踏む非変数位置に対し、循環位置と帰路を独立に示す。nominal は body を開かず、仕様で実際に検査した引数だけを踏む。根／実到達の K2 を通常の選択・曖昧性で覆わない。候補 tape は完全な可視集合の各元構文に対する match / definitive mismatch / blocked / required cycle の証拠付き。failed read、順位の足りなさ、代表例外だけで mismatch を作らない。未完出力の ordinary 等式を K2 で使うことと、候補展開に使わないことを分離。
3. **完了と安定**: 同じ source state の有限 `where` 森と、それより小さい**宣言的な** producer の選択導出で支持された head を区別する（I‑67）。root 葉か否かではなく、すべての依存を確認した completed derivation。solver の release/version/manifest/grant を宣言側に置かない。検査器は必要な場合だけそれらを元の source 由来と完了と照合する。兄弟更新の途中の曖昧／拒否を最終とみなさない。spec の安定を ordinary・view・候補に対する観測の独立な判断で定義し、ある回数回して止まったことや `check=true` の名称にしない。安定後の子の全射と同じ fitting model への transport を用意する。初めから必要な独立根拠で head が読めるなら未完の中心行を待たない。
4. **合流と選択後の等式**: role と名前なし arg 全位置の原 source 同一性／根拠ある等式で merge、出力は候補を絞らない。§6.3 L251 の重複候補の曖昧性と merged output conflict の優先を保ち、§6.3 / K2 に明記された拒否・展開優先もその適用位置で保つ。別段階の診断を新たな全順序にしない。選択前に中心の型や既出出力値で候補を選ばず、選択後に repeated binder の実中心と関連 RHS の固定先に実等式を追加する（§6.5）。元制約と連言し、loaded target を上書きしない。空欄は同名 explicit がないときに限り role の元 default、正確な元位置。
5. **証拠の折り畳み**: independent source node とその grade・exact ordered receipts を構成し、同じ全 state の **任意の** fitting model で head の意味、RHS、保持された target 等式を証明。順のある診断子と支持 producer を別の有限森にし、導出の互いに小さい部分へ下る相互帰納で `FullDictionaryEvidence`／`FullReportEvidence`。適合モデルで偶然同値だから元 source/key/slot/ordinal が同じという逆向き推論はしない。I‑65 外形は維持し現在の証明・意味を無断で変更しない。

`R_full` の clause に spec 実際の未決点を見つけた時だけ質問ノート（遅延案先頭）。この案では端点、K2、merge、可視性、保持の既決規則を分けた。言語の新しい判断は出していない。

## 3. 旧規則からの持ち上げと完全性の分離

正本の [FixedGoal402](../../lean/Yulang/GeneralDeclarativeI65I72FixedGoal402.lean)、[R0 inclusions](../../lean/Yulang/GeneralDeclarativeI65I73RuleUnionInclusions407.lean)、[統一 checker](../../lean/Yulang/GeneralDeclarativeI65I73UnifiedEntry408.lean)、[現 R21](../../lean/Yulang/GeneralDeclarativeI65I74RefPositionEntry441.lean)。既存 `include_fixed_family_trace_R0` は実 `SourceTrace`・両方の森・receipt を同じ索引で運ぶ構造上の先例であり、`FixedEvidenceFamily407` を前提とする。これを全部の spec 順への輸送として引用しない。`Checker408.checked_report_is_unique408` も旧受理済み checker の一意性であって independent full report の一意性でない。既存の `check_sound` は各階層の**全入力**に対する true の健全性、全 source coverage でも以下の full theorem でもない。C14/18–21 などは同一型の `SourcePrimitives` だけの増築でない（endpoint/additive completed evidence、後の outcome 和）。`Rn` は以下では各正式入口の対応する実 judgment を略記する。

| 補題（どれも提案・未証明） | 狙い |
| --- | --- |
| `canonical_old_problem_reflects_whole_source` | 明示的 canonical transport `liftProblem`／同値な source relation を作る。全可視候補（宣言 identity・ordinal 付き）、元の名前なし arg と既出出力、普通の制約/K2 observations、kind付き B6 木、default/where source、exact report を保存・反映。旧受理に有利な別状態・候補部分集合や追加仮定を存在量化しない。旧 State で出ていない型付き保持は G00 として新しい source の表現義務、古い Fits に捏造しない。同じ semantic phase の対応は一方向 projection で済ませず、同じ元制約を保持することを示す。 |
| `local_Rn_case_in_full` (`n=0…21`) | 各実 local constructor / wrapper case を、同じ原 source の `R_full` の各規則へ証拠付き写像。旧埋込みをケースごとに再利用。診断 evidence、exact report の木と元書込み、support の完了を含む。endpoint leaf と completed lane は evidence 型の明示変換。全状態で両方向同値、全部の old hypotheses を new admission とする、という命題でない。 |
| `old_trace_embeds_exact_report` | 上の局所補題 + 原 `SourceTrace / WhereForest / SupportForest` と additive lanes 上で有限帰納。旧成功が full にも同じ選択として、旧診断が対応する独立規則の同じ報告として成り立つ。診断側では例えば「同じ時点で真に unfinished-only」「同じ到達 site が K2」「候補の全範囲が変わらず同じ曖昧性」「同じ merge 位置で同じ矛盾」を別々に保存する。途中 snapshot の診断を full の最終診断と同一視しない。conservative transport が足りなければ論点を分離し、general full soundness を既存判定から閉じたとはしない。 |
| `previous_bool_preserved` | 各 prior witness への既存 .previous Bool は全入力でそのまま。将来の full checker にその支流を入れる場合、同じ old data を再投影する **exact faithful** `embedProblem` 上で Boolean equality と exact report transport を別々に示す。同じ全可視候補・全 raw atom/alias・retained facts・安定/確定 phase を保存・反映する、真の埋込みに限る。full 入力に追加候補、保持行、制約がある場合、都合のよい射影から過去の合格／診断を転送しない。full domain 側の正準対応を証明できない入力へ旧合格規則を広げたり、既存入口での old true を silent false にしたりしない。既存 R21 入口そのものは変更せず残す。 |
| `full_dictionary_sound` / `full_check_sound` | I‑65 と同じ外形：`ClassifiesFull R_full s q (.selected d) → ∀m, FitsFull s m → FullDictionaryEvidence s m q d`；`check_full P r w = true → ExactFullReport … r ∧ ∀m, FitsFull P.state m → FullReportEvidence … r`。前者は全規則の独立な意味・保持補題、後者は実検査が同じ source derivation と厳密 report を再生する反映。旧 `dictionary_sound_Rn` は各実局所保存で利用するが、それだけで新規則の全称健全性は出ない。 |
| `reify_same_finite_derivation` | 独立 selected derivation と、その正準表現・各 G の完全な certificate relation から、有限データ (w) を得る（各局所 `readC(emitC a)` の source/ordinal 保存と mixed 森の帰納）。決定結果を witness の場に仮定しない。A を得る最上段；extensional/A と given-exact-report/B の違いは §1。 |

**存在、実合成、停止**の境界: 上の存在定理で既に渡された有限導出を帰納するだけなら、raw solver の停止は要らない。各 leaf のデータ存在（例えば本当に到達した raw K2 cycle／有限比較証人）と data-only replay reflection は要る。証明対象の `ClassifiesFull` を Prop に置く場合、古典的な存在証明をそのまま実行可能抽出とみなさない。実合成には要る部分の有限 trace/code を明示データとして構成し、その反映定理を持たせる。実関数 `synthesize : FullProblem → …` が raw source から witness を作ること、全安定 snapshot を operational saturation が見つけること、または定義した source semantics が有限導出を与えることを別に主張するときだけ、探索・固定点到達・安定性の実装と停止を証明する。停止をまだ示せなければ **その合成定理に限って** 紙の補題 `terminates_relevant_search/ reaches_stable_snapshot` を named hypothesis にする。停止性を NoFalseRejection の主張から外さず隠れて仮定したり、既に得た有限木から無条件の solver 停止を導いたりしない。§10.14 の旧小さい resolver の Paterson だけで新 mixed source solver の飽和停止を主張しない。

## 4. G 一覧（この周は 0 行閉鎖）

各 Gnn は旧 Cnn の入口／独立規則との対応。G00 は C22 を移した最初の行。旧 module 名は `lean/Yulang/GeneralDeclarativeI65[I74/I75]...` の suffix を示す。下の検査はすべて **元の狭い例の再検査だけではない**、その制限外の一つ以上の正／負（診断 row は exact な報告の正検査と誤報の負）。行を閉じるには、(i) source independent な新規則の元 domain と保/反映、(ii) 実 data-only checker の exact 意図された true/false、(iii) same-state exact report と all-Fits soundness の preservation、およびその行の定義済み範囲で witness reification を同時に示す。依存は局所補題への依存（行全体を機械的に一周で証明できるとの約束ではない）。一周一行、それ以上は残りを明示、statement を縮めて閉鎖数を稼がない。

| G / 旧足場 | 現行の実制限と外す規則、その行の独立試験 |
| --- | --- |
| **G00 / C22**, C442 `MixedFixed{Read,Companion,Dictionary}442` | **最初**。元の where 無し singleton、出力 1 の typed row/value RHS は照合できるが `Fits` は保持を含まない。二 Fits の同じ RHS/observations と異なる target .1。§6.3・I‑71：同じ出現/宣言番号/出力番号/本文/既出 target と kind を保つ canonical typed retention writer/Models を提案。旧 view 独立、flat `Expr` に落とさない。既存 `GeneralNominalState.Descriptor` は実 source/rowSource の別名と typed 等式を読む候補だが authority・Models transport を別証明。完了/release は別 (G18)。新 typed equality が original ordinary/K2 観測に寄与する場合の source-to-raw 対応も別補題で示し、単に旧 raw を固定して新しい実循環を隠さない（G02/G04/G17 の局所観測接口）。試験: signed row を保持する target が真正保持で true、同じ RHS を別 slot の記録で代用は false。既出 Int 制約と混合 ref は **連言**で不適合；上書きや新診断にしない。 |
| G01 / C01 [`NamedEntry409.bareName`](../../lean/Yulang/GeneralDeclarativeI65I74NamedEntry409.lean) | 空 arity nominal、入力 1、全可視 singleton、空 where/output、元直接名。§6.2/6.3 の本体 opaque な named 観測を一般の exact call-site candidate set の中で扱う（候補一覧、G10、args を読むとき G20/21）。試験: 隠れた同名 impl を増やしても正しい実 named 選択 true、可視実 rival を増やして旧選択 report は false。nominal body を開かない。 |
| G02 / C02 [`ListEntry410.listLeaf`](../../lean/Yulang/GeneralDeclarativeI65I74ListEntry410.lean) | 一つの invariant list point、plain binder/単一候補、空 where/write。raw no-return の現 witness にも限界（C410 の実 one-way Bound/flat 反例）。§6.3：元の inspected sites に対する完全な per-site K2 証人、binder 下の未観測 cycle を全 graph の rank で排除しない。試験: 多枝と alias 混合で根非循環だが見ない payload が循環なら true、実 alias return を足せば同じ選択 false。 |
| G03 / C03 [`WhereListEntry411.whereChild`](../../lean/Yulang/GeneralDeclarativeI65I74WhereListEntry411.lean) | 一つの同 role の literal where 変数、単一 parent list point、空出力、実 child root K2。任意の原 clause の位置・実再構成された子に一般化（G02, G15–16）。試験: 子 2 のみ raw K2 の exact 親/子報告 true、親自身 K2 に置き換えた report は false。 |
| G04 / C04 [`RecordEntry412.fieldCycle`](../../lean/Yulang/GeneralDeclarativeI65I74RecordEntry412.lean) | 二段の閉じた record point、単一候補、where 一つ/出力無し、実 field site の K2。§6.3：任意有限 bound pattern 内 actual visited field と provenance の帰納、開かない site は非原因。試験: 深さ 3 の alias 経由の実 field 循環 report true、非到達 field を差し替えた証明は false。 |
| G05 / C05 [`MixedRecordEntry413.mixedHead`](../../lean/Yulang/GeneralDeclarativeI65I74MixedRecordEntry413.lean) | 実 nested 候補一つ＋plain 一つ以上、record 同点、root 留保なし。全候補 tape の actual visit/election を任意 ordinal・複数 rigid と未確定 candidate へ一般化（G04, G10, G17）。試験: 複数形の rival の実 K2 を候補順を変えても exact 拒否 true、単なる可能 site の cycle を渡すなら false。 |
| G06 / C06 [`OpenTailEntry414.openTail`](../../lean/Yulang/GeneralDeclarativeI65I74OpenTailEntry414.lean) | 単一の点、明示 int field と未知 tail、可視候補一つ/同名 binder の where 一つ、対応 tail に既存行等なし。§6.3/§10.25–28：一般の根拠付き未知を、既知不一致・完了根拠・行の相関と分けて扱う (G04/G07/G17)。試験: 開いた tail を使う候補の正確な保留 true、同じ undecided marker を既知 tail または raw 根 K2 に被せる報告は false。 |
| G07 / C07 [`ClosedResidualEntry415.closedRows`](../../lean/Yulang/GeneralDeclarativeI65I74ClosedResidualEntry415.lean) | 二 field の有限閉じた入力、exact split 残部、親・**別 role** 子各 singleton、空出力。任意の residual の field masking（hidden/width/open を混同しない）と正しい値/端点/where。G06/G14/G15。試験: 三 field のうち指定 field のみ除いた残部と実 where 成功 true、隠れた同名 field を復活または別の residual name を供給は false。 |
| G08 / C08 [`PlainMergedEntry416.plainMerged`](../../lean/Yulang/GeneralDeclarativeI65I74PlainMergedEntry416.lean) | 一点 `tick int`・二 plain binder、真正 raw variant/int/join・singleton・no writes。§6.3：任意の payload 全体の合流後捕捉、plain と nonplain（nominal の承認済み構造だけ）を区別、分割しない。G05/G20。試験: 三 plain binder と非 Int payload に同じ実合流値を捕捉して true、arm の個別値に按分した witness false。 |
| G09 / C09 [`X6AmbiguousEntry417.x6Ambiguity`](../../lean/Yulang/GeneralDeclarativeI65I74X6AmbiguousEntry417.lean) | same tag の plain + ground Int の実二候補、同じ payload と no K2、空書込み。異なる形を含む全候補の安定した曖昧性と順位（G05/G08/G10/G17）。試験: 三つの本物の候補で曖昧報告 true、同じ宣言の重複 import を独立 rival とする報告 false。出力指定で曖昧を解消しない。 |
| G10 / C10 [`RigidRivalEntry418.rigidRival`](../../lean/Yulang/GeneralDeclarativeI65I74RigidRivalEntry418.lean) | 実一 winner + rigid str 一 rival / Int payload、where/write 無し。多数の候補で完全な match/mismatch/defer の反映と ordinal；未読は不一致でない（G01/G04/G05、G17 は pending の意味、G09 は診断側）。試験: 真に根拠付けた不一致を持つさらに複数 rival の下の exact 選択 true、未解決 rival を落とした winner report false。 |
| G11 / C11 [`ExplicitPickEntry419.explicitPick`](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickEntry419.lean) | 二 field record 点、一明示 RHS、一固定 target、singleton/where 無し、旧 Expr reification がある。§6.1/6.3：任意の実明示 output 写像を元 B6 tree と有限 ordinal で検査（G00, G14, G15）。試験: 複数出力かつ record/nominal の typed 複合 RHS で真、出力の順・固定先・本文のいずれかを交換して偽。literal `char` を代用しない。 |
| G12 / C12 [`RoleDefaultEntry420.roleDefault`](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultEntry420.lean) | 実 unary role の一出力、位置0の元引数、点二 field record、singleton/空 where。§6.1・§10.7: 可変 arity の元位置置換、同名 explicit だけが default に勝つ。G00/G11。試験: 二番目の引数を読む default と別名 explicit の同居 true、同名 explicit が実在するのに古い default を使う報告 false。 |
| G13 / C13 [`RepeatedCentersEntry421.repeatedCenters`](../../lean/Yulang/GeneralDeclarativeI65I74RepeatedCentersEntry421.lean) | 二非点 arg、同一 binder、共通上側 example と singleton、空 where/output、post-choice 既存 Eq/同タグ Int/Bool 境界。§6.5：各 repeated group の実中心を選んだ後だけ同値にし、複数 group/複数 arg の source 構造と一般の制約適合を記録。G10/G00。試験: 三出現の本物の中心 tie を保つ report true、同じ端点だけで一つ中心 Eq が無いのに選択済みを主張は false。 |
| G14 / C14 [`ProjectedRule426.projectedRecord`](../../lean/Yulang/GeneralDeclarativeI65I75ProjectedRule426.lean) | actual 非点 record、元の endpoint leaf、required field 向きと observer/mask、狭い出力保持。§6.5 の required/optional・残余のモデル法へ一般化、中心の literal 名を捏造せず、点 legacy 併存。G00/G06/G07。試験: 中心観測のない異なる上下端で required/optional の実射影と mask residual を保持して true、違う field/mask/固定先で代用は false。中心の literal 名が無いだけで正例を落とさない。 |
| G15 / C15 [`StructuralWhereEntry431.originalStructuralWhere`](../../lean/Yulang/GeneralDeclarativeI65I74StructuralWhereEntry431.lean) | 実構造 where 一つ、可視 singleton と scoped 子、零 support/零 write の exact 形（同 role X10 全域ではない）。§6.3：任意の実 literal clause、post-selection source synthesis、複数 ordered 子と support 森の区別。G02/G04/G10。試験: 多子・異なる構造位置の exact 報告 true、同じ型でも誤 clause/子順や support を診断子として挿入は false。 |
| G16 / C16 [`StructuralWhereAssociatedEntry432.associatedWrap`](../../lean/Yulang/GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432.lean) + C433 | actual Wrap + 一 where child の元出力を親に接続、狭い named/typed row と受理できる配置、順序・scope 制約。`Sibling…433` は表示順と model 値保存の局所足場。§6.3：複数 actual completed 子から親・許された既存 sibling slot へ exact typed write を同じ state で流す。G00/G11/G15 と G18 の完了根拠の局所接口（G18 行全体の閉鎖を要しない）。試験: 二子で一つの旧 slot を安定させた exact 木/固定行 true、異なる owner/ordinal 行または新 anonymous 入力捏造は false。 |
| G17 / C17 [`PendingAssociatedEntry434.pendingAssociated`](../../lean/Yulang/GeneralDeclarativeI65I74PendingAssociatedEntry434.lean) | 実 unary list、自分の where 1・関連出力の狭い issuer、真の unfinished のみと raw escape。§6.3 L157–213：SCC 内外／acyclic unfinished chains の支持を、独立 authored/completed の有無と分離。G02/G06/G15。試験: 循環成分から下流への unfinished-only 正確な保留 true、独立完成根拠あり／未完 Eq 由来 root K2 を同じ保留にする報告 false。 |
| G18 / C18 [`CompletedLowerEntry438.completedLower`](../../lean/Yulang/GeneralDeclarativeI65I74CompletedLowerEntry438.lean) | 独立別 producer の finite exact Seed leaf（where なし・保持 1 output）、consumer singleton unary、authored upper/actual center・保持 lower、空 consumer where/write。§6.3/I79：任意の小さい completed source 森から exact typed output を読み、適切な authorized port を再開。G00/G15/G17。試験: 複数段 producer と元の where を経た真正保持で true、同じ値でも更新前 version/違う出現・未完・保持だけのポートは false。論理完了と実 release は混同しない。 |
| G19 / C19 [`MergedOutputEntry439.mergedOutput`](../../lean/Yulang/GeneralDeclarativeI65I74MergedOutputEntry439.lean) | 実 P int の literal 二 where、同じ nullary role の int vs variant 出力、単一候補、局所 exact merged-child 拒否。§6.3 L231–259：任意 arity の同じ source 入力と元複数 output class、一般の整合／矛盾証明と exact occurrence。G00/G09/G10/G15。試験: 三元 clause の真の合流先矛盾 exact 報告 true、同じ端点だけを共有する別 input／複数可視候補／重複子の誤報は false。 |
| G20 / C20 [`NestedInvariantEntry440.nested`](../../lean/Yulang/GeneralDeclarativeI65I74NestedInvariantEntry440.lean) | singleton の二段 nominal、共通外端点の scoped 実例、内非点と declared mode、空 where/output。§6.5：任意有限深度・異なる compatible 窓・inherited invariant と本来の cov/contra/unused を分ける。G02/G10/G13/G21 部分（G21 は kind 位置読みだけ、循環依存にしない）。試験: 三段・別外端点の actual report true、四つの必要 crossing の一つを欠いた証人 false。旧 X14 literal Float source と X17 function simplifier を既に実装したとは扱わない。 |
| G21 / C21 [`RefPositionEntry441.reference`](../../lean/Yulang/GeneralDeclarativeI65I74RefPositionEntry441.lean) | 実 `ref _ 'a` 二 binder、row cov/value inv の順序、singleton の point origin、空 where/output。literal `ref _ int` は既存 rigid-scalar DeepRead が未表現、rank‑2 は B3。§4.6/§6.2/§10.9.6：任意の actual declared position/kind と compound/rigid source の証拠（G00/G10/G20 の比較 kernel を利用）、自由 row と value の名表を混同しない。試験: 本物の rigid scalar を保持した mixed nominal の actual 選択 true、引数位置交換／誤った種類・場所を示す証人 false。rank‑2 lowering を B4 の witness に隠さない。 |

まず G00 の canonical writer/model transport を設計審査に出す。その後に表中の番号を機械的に順に実装するのでなく、以下の局所接口の証明を依存として一つずつ用いる。この接口は新たな G 行や独立意味論の仮定を増やすものではない。

1. **同じ State／有限 graph の照合**（G00/G01/G02 の基礎）: source・型付き tree・全候補を投影した canonical table の faithful lookup、raw 観測と exact alias/structural graph、actual entered が決まったときの per-site cycle/escape の有限証人。全候補の verdict はここでは定義しない。
2. **局所 head・比較・case evidence**（G04/G06/07/G08/G13/G14/G20/21）: 共通 graph／kind-site から実 visit、typed match または根拠ある mismatch/blocked を構成。G20 と G21 は「source kind 位置読み → 任意有限深度の比較 → 各 scoped source 例への統合」の順で、相手の全行閉鎖を前提にしない。record 残余表現と未知の区別は別補題。
3. **候補列の反映と判定**（G01/G05/G09/G10）: 下位の各実候補 evidence を元の全 list に結び、候補単独の case を証明した後に K2／最終選択等を合成。G01 の opaque read は G10 の全 matcher なしで下位から供給できる。上位の iff に未実装の局所比較があれば G10 全体を closed としない。
4. **同じ source の where・完了／保持**（G03/G11/12/G15/16/17/18/19）: G15 の原 clause emission → 同じ trace で G18 の小さい完了 producer の読み → G16 のその retained RHS の消費（小さい導出上の相互帰納）。G17 は完了の判断を使う側、G18 が G17 の全診断表を先に証明するという循環にしない。最後に元の report/writes の反映と合流を実 checker で試す。

依存する局所接口が無ければ、一周で閉じられない行は未完とし、先に依存の rooted な補題を進める。一行の試験は既存例の成功の再掲ではなく、元の制限を実際に越え、誤った報告・番地・順位を拒む対照である。試験だけで coverage を証明済みにしない。

### leaf の有限証明を設計審査するときの共通テスト

- **lookup、kind、source 位置**: 同じ形でも異なる宣言 identity・visibility・版・出力先を取り違えない。可視宣言の順列は source ordinal の転送を伴う時だけ報告を対応させる。欠けた B6 term は representation false で、独立な invalidity の証明ではない。
- **比較／矛盾**: 正常・不一致・未確定を分け、declarative の comparison/constraint judgment の対象と偽入力を実入力で検証する。必要側が有限証明化できることは別の補題。有限項だから任意の射影、再帰行、不変混合、モデルの無存在が自動的に決定可能とはしない。
- **K2 と支持経路**: raw reachability の yes/escape は同じ実有限 graph に対する証明。nominal body を展開せず、実 entered 根拠と循環上の位置 を別々に照合。unfinished producer に依存する等式を raw から消す負例、単なる可能位置の positive cycle を受理する負例を置く。
- **保持と exact Rhs/Report**: semantic 値が偶然同じ対照で target/owner/ordinal を差し替えても false。既存制約と混合 type を実際に連言する。元の where text を入れ替えて独立な連言の結果は対応しても、実 report の literal 順は新しい source への対応であって、元 P の witness を誤順のまま true にしない。
- **保守性の範囲**: 全ての正例で元の narrow wrapper を true から変えない検査と、scope 外の正例が将来 true になる試験は別。checker soundness は `true` を理由に独立 role の verdict を証明するのであって、同じ判定を `R_full` の定義へ戻さない。

## 5. 検証の境界と審査をお願いする点

I‑80 下の本周は **ノート一本のみ**。証明、Lean/state/spec 変更、新 witness、全体ビルドは無し。現在の Git 正本の実各入口と監査報告、§6（可視性・merge/完了・raw K2）・§10（種類/可視性/EOF/型推論の責任）の読み合わせを根拠とした。G の制限を外すテストはまだ実行していない。審査では最小 A と追加 B の区別、G00 の状態表現/モデル対応、source 独立な安定・診断輸送、whole-solver 合成を別契約にすることを先に確認してほしい。

**C は終了（C22 は G00 へ移動）。G は提案 22 行、0 閉鎖。NoFalseRejection は未証明。**
