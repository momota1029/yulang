import Yulang.CommonRoleNamedPath
import Yulang.CommonRoleStatefulPathParent
import Yulang.CommonRoleSettledResolver
import Yulang.CommonRoleOpenRecursivePass
import Yulang.CommonRoleOpenPassStability
import Yulang.CommonDeclarationVarianceRegistry
import Yulang.CommonSourceOptionalX22
import Yulang.CoreCommonInference
import Yulang.CommonDeclaredCastCost

/-!
# M1 の主張を読む窓口 — 証明済み断片、2026-11-08

**これは全言語 M1 の完成宣言でも、全体 statement の承認要求を省いた代用品でもない。**
以下は実在する入口と独立判断を、元の量化子・前提を保って再掲する。
B4 の一般区間・共有 source graph・関連型・飽和・最終辞書を合わせた判断は
まだ存在しないので、旧点モデルや任意の oracle をその代わりに置かない。
全体 statement の範囲は承認済みだが、その carrier と独立判断の Lean 定義は未接続。

読む順序：settled B4 → open pass → variance 表 → X22 → 現在の Core。
局所的な意味安定性の目標は末尾の `OpenPassSemanticStabilization`。
これは B4 の全体 statement ではない。B3 と B5/B1 の全 source/nominal/cast 接続も
ここで証明したとは主張しない。

実行（既存 lakefile を変更しない）：
`cd lean && lake build Main --wfail`
inbox I-3 の明示許可により root Main に昇格。全言語の完成宣言ではない。
-/
namespace Yulang.Main

/-- **証明済み、settled 断片のみ（B4 全体ではない）。**
任意の slot 数 n、宣言チェックを満たす registry、settled request q、四方向の result
について、実外側 classify が result を返すことと、独立 Classify が同じ結果を導く
ことが同値。frontier exactness、fuel、Acc、成功、辞書を外部前提にはしない。
ただし request の型自体が等しい上下端点の断片を表す。共有変数へ関連型を流し込み
更新する一般区間は対象外。spec/06-roles.md 6.3–6.5。
証明本体：CommonRoleSettledResolver.resolve_exact。-/
theorem settled_role_exact (registry : CommonRoleSettledFrontier.Registry)
    (q : CommonRoleSettledFrontier.Request n) (result : CommonRoleOutermostResolver.Result) :
    CommonRoleSettledResolver.classify registry q = result ↔
      CommonRoleOutermostResolver.Classify
        (CommonRoleSettledFrontier.Local registry.declarations) q result :=
  CommonRoleSettledResolver.resolve_exact registry q result

/-- **証明済み、同じ settled 断片の停止性。**
任意の n、checked registry、request q について、実局所判断の子関係は q で accessible。
降下は宣言時 Paterson 検査から導かれ、呼出側に rank や Acc は要求しない。
一般 open producer の飽和停止性とは別の主張。spec 6.3、6.5。
証明本体：CommonRoleSettledResolver.accessible。-/
theorem settled_role_accessible (registry : CommonRoleSettledFrontier.Registry)
    (q : CommonRoleSettledFrontier.Request n) :
    Acc (CommonRoleOutermostResolver.Child
      (CommonRoleSettledFrontier.Local registry.declarations)) q :=
  CommonRoleSettledResolver.accessible registry q

/-- **証明済み、open 区間の一回の再帰 pass に限る。**
任意の n、checked registry、外部 Allocation n、request q、開始状態 s、trace、最終状態
final について、実 run の返値が (trace,final) である iff 独立 Runs がそれを導く。
外部 FrontierExact や Acc は不要。ただし Allocation は依然外部入力で、両端を独立
inspect する断片である。関連型による一般 narrowing、動的 allocator の閉包、飽和、
最終 selected/pending/ambiguous/rejected と辞書の exactness は結論に含まれない。
spec 6.3 の兄弟再計算の一段階。証明本体：CommonRoleOpenRecursivePass.run_exact。-/
theorem open_pass_exact (registry : CommonRoleOpenProducer.Registry)
    (allocate : CommonRoleOpenPropagation.Allocation n)
    (q : CommonRoleOpenProducer.Request) (s : CommonRoleSettledConstraints.State n)
    (trace : CommonRoleOpenRecursivePass.Trace) (final : CommonRoleSettledConstraints.State n) :
    CommonRoleOpenRecursivePass.run registry allocate q s = (trace, final) ↔
      CommonRoleOpenRecursivePass.Runs registry.declarations allocate q s trace final :=
  CommonRoleOpenRecursivePass.run_exact registry allocate q s trace final

/-- **証明済み、宣言方程式から variance 表を作る橋（B5/B1 全体ではない）。**
任意の Index/Formal 型とその DecidableEq、Program、解析 Universe、元の順序付き
headers、結果 registry について、計算した registry と結果が等しい iff 独立な
RegistryJudgment が成り立つ。元 header の kind・位置は保持される。
Program を全 source 宣言から組み立てること、nominal carrier、全 cast 費用と
unrestricted family 回収まで同時に証明する主張ではない。spec/04-types.md の
宣言別 variance。証明本体：CommonDeclarationVarianceRegistry.registry_exact。-/
theorem declaration_variance_registry_exact {Index Formal : Type}
    [DecidableEq Index] [DecidableEq Formal]
    (program : CommonDeclarationVarianceSyntax.Program Index Formal)
    (pool : CommonDeclarationVarianceOccurrences.Universe Index Formal)
    (headers : List (CommonDeclarationVarianceLowering.Header Formal))
    (result : CommonDeclaredNominalInspection.Registry) :
    CommonDeclarationVarianceRegistry.registry program pool headers = result ↔
      CommonDeclarationVarianceRegistry.RegistryJudgment program headers result :=
  CommonDeclarationVarianceRegistry.registry_exact program pool headers result

/-- **証明済み、有限 cast plan の費用上界（B5/B1 全体ではない）。**
任意の node 数 n、Plan n、実 check の受理証明、node、cost と実 Run の導出について、
cost はその plan のみから計算する budget 以下。leaf cast 内部やユーザー関数の
実行時間はこの費用に含まれない。宣言別 variance からこの plan を生成し check が
通るという橋は前提に隠さず、未接続として残す。受理前提を除いた一般 cast の
定理ではない。証明本体：CommonDeclaredCastCost.run_bound。-/
theorem checked_cast_cost_bound (plan : CommonDeclaredCastCostGraph.Plan n)
    (accepted : CommonDeclaredCastCostGraph.check plan = true)
    (node : Fin n) (cost : Nat) (execution : CommonDeclaredCastCost.Run plan node cost) :
    cost ≤ CommonDeclaredCastCost.budget plan accepted node :=
  CommonDeclaredCastCost.run_bound plan accepted execution

/-- **証明済み、新しい structural source 入口での具体例 X22。**
固定した source arms に対する生成制約は固定 assignment で成立し、空 record は
第1 arm を miss して80を返す。さらに任意の整数 port に対し present program は
その port を返す。旧 strict 入口の MISMATCH を変更した主張ではなく、B2 全体の
効果・網羅性・停止性を述べるものでもない。spec/03b-patterns.md 3b.3。
証明本体：CommonSourceOptionalX22.x22_proved。-/
theorem optional_source_x22 :
    (CommonSourceArmsSolved.principal [] CommonSourceOptionalX22.arms).Holds Common.model
      CommonSourceOptionalX22.assignment ∧
    (ScopedCaseDataProgram.eval Empty.elim [] CommonSourceOptionalX22.absentProgram).result =
      .ok (some (.literal (.int 80))) ∧
    (∀ port : Int,
      (ScopedCaseDataProgram.eval Empty.elim [] (CommonSourceOptionalX22.presentProgram port)).result =
        .ok (some (.literal (.int port)))) :=
  CommonSourceOptionalX22.x22_proved

/-- **証明済み、現在の CommonSyntax model の公開 Core 入口（新版 B6 の完了ではない）。**
任意の元 Core.Required.Term expression と任意の Common 計算型 result について、空環境
での Core.Typing iff 実 Core.infer が返すある scheme と、その unrestricted parameters
による instantiate が result 以下。追加の support・成功・fuel 前提はない。
ただし型付け判断の model は現存 CommonSyntax.model であって、区間・遅延・宣言別
variance を全 source 構文に統合した承認済み B6 の判断と同一であるとは未証明。
証明本体：Core.infer_principal。-/
theorem current_core_principal (expression : Core.Required.Term)
    (result : Core.PresenceGeneration.Comp Common.model) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result ↔
      ∃ scheme ∈ Core.infer expression, ∃ parameters : scheme.Parameters,
        Core.PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) result :=
  Core.infer_principal expression result

/-- 一回の既存 pass が返した ordinary state。これは最終解決器ではない。-/
def passState (registry : CommonRoleOpenProducer.Registry)
    (allocate : CommonRoleOpenPropagation.Allocation n)
    (q : CommonRoleOpenProducer.Request) (s : CommonRoleSettledConstraints.State n) :
    CommonRoleSettledConstraints.State n :=
  (CommonRoleOpenRecursivePass.run registry allocate q s).2

/-- 開始状態から k 回、既存 pass だけを繰り返した状態。
停止の fuel として k を要求する solver ではなく、目標を記述する有限反復。-/
def passStates (registry : CommonRoleOpenProducer.Registry)
    (allocate : CommonRoleOpenPropagation.Allocation n)
    (q : CommonRoleOpenProducer.Request) (s : CommonRoleSettledConstraints.State n) :
    Nat → CommonRoleSettledConstraints.State n
  | 0 => s
  | k + 1 => passState registry allocate q (passStates registry allocate q s k)

/-- 二つの ordinary states が、すべての元 slot assignment に対し同じモデルを持つ。
atom list の重複や順番だけが変わることは、意味上の変化とは数えない。-/
def SameModels (before after : CommonRoleSettledConstraints.State n) : Prop :=
  ∀ assignment : Fin n → Core.PresenceGeneration.Comp Common.model,
    PresenceNormalForm.All Common.model assignment before.atoms ↔
      PresenceNormalForm.All Common.model assignment after.atoms

/-- **局所的な意味安定性の目標。B4Statement ではない。**
任意の n、checked registry、Allocation n、q、s について、有限回 k の既存 pass 後に、
次の pass と同じ全 assignment のモデルを持つ状態へ達する、という Prop。
k の存在は結論であり、呼出側の fuel・成功前提ではない。しかしこの命題を証明しても、
source allocator の意味保存・一般 narrowing・独立な最終 Classify・有限辞書の正しさ
は得られない。cycle 2 の固定 structural producer について下で k=1 を証明する。-/
def OpenPassSemanticStabilization : Prop :=
  ∀ (n : Nat) (registry : CommonRoleOpenProducer.Registry)
    (allocate : CommonRoleOpenPropagation.Allocation n)
    (q : CommonRoleOpenProducer.Request) (s : CommonRoleSettledConstraints.State n),
    ∃ k, SameModels (passStates registry allocate q s k)
      (passStates registry allocate q s (k + 1))

/-- 固定 structural producer の ordinary models は一回のpassで安定する。
全source narrowingやtrace/atom列の構文的な固定点を述べるものではない。-/
theorem open_pass_stabilizes : OpenPassSemanticStabilization := by
  intro n registry allocate q s
  refine ⟨1, ?_⟩
  intro assignment
  exact (CommonRoleOpenPassStability.run_semantically_idempotent
    registry allocate q s assignment).symm

end Yulang.Main

namespace Yulang.Main

/-- 任意の旧 ordinary state、任意の有限 dependency path、任意の結果について、
実 source seed・状態更新・solver・Parent 辞書の入口と独立 Final が同値。
成功・Models・fuel の外部前提はない。有限 path は入力で、一般 B4 飽和ではない。 -/
theorem stateful_finite_path_parent_exact (outputs : List (Fin n)) (receiver : Fin n)
    (s out : CommonRoleSettledConstraints.State n) (argument : Roles.Term)
    (answer : RoleDictionaries.Answer) :
    CommonRoleStatefulPathParent.run outputs receiver s = some (out, argument, answer) ↔
      CommonRoleStatefulPathParent.Final outputs receiver s out argument answer :=
  CommonRoleStatefulPathParent.outer_exact outputs receiver s out argument answer

/-- 固定した Right seed と逆順の兄弟更新の具体例。全ての結果について実入口と
独立した辞書判断が iff。2 pass はこの例の bound で、一般停止性を表さない。 -/
theorem stateful_reverse_siblings_exact (out : CommonRoleSettledConstraints.State 3)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    CommonRoleStatefulParentExample.run = some (out, argument, answer) ↔
      CommonRoleStatefulParentExample.Final out argument answer :=
  CommonRoleStatefulParentExample.outer_exact out argument answer

end Yulang.Main

namespace Yulang.Main
/-- 名前付き有限pathについて、slotと同一性制約を入口自身が計算する。
任意の旧状態・結果に対する iff であり、成功・model・allocation の外部前提はない。
固定 Index(box str) seed の断片で、一般source parserの定理ではない。 -/
theorem named_finite_path_exact (seed : Nat) (names : List Nat)
    (s out : CommonRoleSettledConstraints.State (CommonRoleNamedPath.table seed names).length)
    (argument : Roles.Term) (answer : RoleDictionaries.Answer) :
    CommonRoleNamedPath.run seed names s = some (out, argument, answer) ↔
      CommonRoleNamedPath.Final seed names s out argument answer :=
  CommonRoleNamedPath.outer_exact ..
end Yulang.Main

/-!
# 承認済み B4 主張の未証明ターゲット

**これは一般 B4 の証明でも、具体 source carrier の実装でもない。**
草稿の量化子と五項を落とさず、まだ存在しない source/graph/propagation の境界を
明示的なパラメータにした target schema である。`SourceBoundary` の具体的な実装は未接続。
caller 提供の oracle をこの境界に入れた定理を「全 B4 完了」と呼んではならない。

`Classify` は実行関数を参照しない帰納的判断。草稿にない親子failure伝播は追加しない。
このため、唯一候補の子が非selectedのときの全体分類は質問ノートの未決事項であり、
現状のschemaが一般sourceについて証明可能だとは主張しない。

`Executor` に fuel/Acc/成功前提はない。`B4Statement` 自身は未証明の Prop で、
以下にはその定義の射影補題だけを置く。未証明の穴は置かない。
-/
namespace Yulang.B4Target

open CommonRoleOutermostResolver
universe u

/-- 一般source carrierの未接続境界。registryは可視有限宣言、stateはordinary制約と
共有graph、demandは正規化済み区間引数、modelはsource割当を表す予定。
これらを旧settled carrierで代用した全体完成宣言はしない。 -/
structure Vocabulary where
  Registry : Type u
  State : Type u
  Demand : Type u
  Model : Type u

/-- 実行版を参照しない独立境界。各フィールドの具体sourceインスタンスは未実装。
`Step` は再生成を含む実情報更新の進行stepとして接続する必要があり、任意rankや
fuelを仮定するためのフィールドではない。`Reorders` はvisible順/where順の変更だけ。
`DictionaryEquivalent` は義務に対応した証拠の観察同値であり、全辞書を同一視しない。 -/
structure SourceBoundary (v : Vocabulary) where
  Checked : v.Registry → Prop
  Models : v.State → v.Model → Prop
  Step : v.Registry → v.Demand → v.State → v.State → Prop
  Stable : v.Registry → v.State → v.Demand → Prop
  Generated : v.Registry → v.State → v.Demand → v.Demand → Prop
  RootPending : v.Registry → v.State → v.Demand → Prop
  RootK2 : v.Registry → v.State → v.Demand → Prop
  CandidateK2 : v.Registry → v.State → v.Demand → Prop
  InspectionPending : v.Registry → v.State → v.Demand → Prop
  Survivor : v.Registry → v.State → v.Demand → Nat → List v.Demand → Prop
  Evidence : v.Registry → v.State → v.Model → v.Demand → Dictionary → Prop
  Reorders : v.Registry → v.Registry → Prop
  DictionaryEquivalent : Dictionary → Dictionary → Prop

/-- 草稿の拒否理由だけ。where子の失敗を勝手に第四の理由に加えない。 -/
def RejectReason (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (d : v.Demand) : Prop :=
  b.RootK2 r s d ∨ b.CandidateK2 r s d ∨
    (∀ key children, ¬ b.Survivor r s d key children)

/-- 検査完了とK2優先。普通の曖昧性より先にK2を排除する。 -/
def SafeKnown (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (d : v.Demand) : Prop :=
  ¬ b.RootPending r s d ∧ ¬ b.RootK2 r s d ∧
  ¬ b.CandidateK2 r s d ∧ ¬ b.InspectionPending r s d

/-- 実行版を使わない唯一候補。子は捕捉・同一source変数併合後の全where需要を
`Survivor` が供給する義務を負う。フィールドの忠実性はまだ未接続。 -/
def Unique (b : SourceBoundary v) (r : v.Registry) (s : v.State)
    (d : v.Demand) (key : Nat) (children : List v.Demand) : Prop :=
  b.Survivor r s d key children ∧
    ∀ key' children', b.Survivor r s d key' children' →
      key' = key ∧ children' = children

/-- 独立な四方向分類。唯一候補の全where子がselectedの場合だけ有限辞書を構成。
親に辞書がない場合の追加規則は未決のまま。`run`/solverの返値を定義に埋め込まない。 -/
inductive Classify (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → Result → Prop where
  | pending : b.RootPending r s d → Classify b r s d .pending
  | rejected : RejectReason b r s d → Classify b r s d .rejected
  | ambiguous : SafeKnown b r s d →
      b.Survivor r s d key₁ children₁ → b.Survivor r s d key₂ children₂ →
      key₁ ≠ key₂ → Classify b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children →
      All₂ (fun child dictionary => Classify b r s child (.selected dictionary))
        children dictionaries →
      Classify b r s d (.selected (.node key dictionaries))

/-- 実step列の有限到達。外部から与えるfuelはない。 -/
inductive Steps (step : α → α → Prop) : α → α → Prop where
  | refl : Steps step s s
  | tail : Steps step s t → step t u → Steps step s u

/-- 実飽和入口を接続する場所。全registry/state/demandに対して結果を返し、
checked・fuel・Acc・成功・Models証明をcallerへ要求しない。具体実装は未接続。 -/
structure Executor (v : Vocabulary) where
  run : v.Registry → v.State → v.Demand → v.State × Result

/-- 各結果のtagを保存し、selectedは独立な辞書観察同値で比較する。
where順が変われば子Listのliteral equalityとは一般には違うため、同値の具体定義は未接続。 -/
def SameOutcome (b : SourceBoundary v) : Result → Result → Prop
  | .pending, .pending => True
  | .rejected, .rejected => True
  | .ambiguous, .ambiguous => True
  | .selected first, .selected second => b.DictionaryEquivalent first second
  | _, _ => False

/-- (1)停止・存在・安定閉包・モデル減少。全checked registry、全旧state、全需要に対し、
実進行stepのAcc、返値への有限実到達、rootと全生成需要の安定、全modelの包含を要求。
Paterson/K2からこれを示す必要があり、任意のrankを前提に追加していない。 -/
def SaturationTotal (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand),
    Acc (fun next current => b.Step r d current next) s ∧
    Steps (b.Step r d) s (e.run r s d).1 ∧
    b.Stable r (e.run r s d).1 d ∧
    (∀ child, b.Generated r (e.run r s d).1 d child →
      b.Stable r (e.run r s d).1 child) ∧
    (∀ model, b.Models (e.run r s d).1 model → b.Models s model)

/-- (2)健全性/完全性。任意のchecked registry、旧state、需要、四方向結果について、
実返値と独立分類がiff。成功・Models・FrontierExact・Accは外部仮定にない。 -/
def Exact (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand) (outcome : Result),
    (e.run r s d).2 = outcome ↔ Classify b r (e.run r s d).1 d outcome

/-- (3)順序独立。可視宣言/whereのみを並べ替えた任意のchecked registry同士で、
同じ旧state・需要の最終結果が独立な観察同値を満たす。辞書内容の同値は明示境界。 -/
def OrderIndependent (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r r' : v.Registry), b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ (s : v.State) (d : v.Demand),
      SameOutcome b (e.run r s d).2 (e.run r' s d).2

/-- (4)辞書健全性。任意の最終モデルにおいて、selected辞書はroot headへの代入と
全where子を整合して証明する。Evidenceは実行版と独立にsourceから実装すべき境界。 -/
def DictionarySound (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand)
    (dictionary : Dictionary),
    Classify b r (e.run r s d).1 d (.selected dictionary) →
    ∀ model, b.Models (e.run r s d).1 model →
      b.Evidence r (e.run r s d).1 model d dictionary

/-- (5)偽拒否なし。任意のchecked registry、旧state、需要について、実rejectedなら
草稿のroot K2・candidate K2・全候補消滅の少なくとも一つが最終状態で実際に成立。 -/
def NoFalseRejection (b : SourceBoundary v) (e : Executor v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (d : v.Demand),
    (e.run r s d).2 = .rejected → RejectReason b r (e.run r s d).1 d

/-- 未証明targetの5項。全B4の証明を表す定理定数ではない。
必要な具体sourceインスタンスを外部oracleで置換した成果を完成と称しない。 -/
def Statement (b : SourceBoundary v) (e : Executor v) : Prop :=
  SaturationTotal b e ∧ Exact b e ∧ OrderIndependent b e ∧
    DictionarySound b e ∧ NoFalseRejection b e

/-- 補助のみ：targetを仮定すればその健全性方向を取り出せる。
`Statement b e` 自体を証明したという主張ではない。 -/
theorem statement_sound (b : SourceBoundary v) (e : Executor v)
    (target : Statement b e) (r : v.Registry) (checked : b.Checked r)
    (s : v.State) (d : v.Demand) (outcome : Result)
    (returned : (e.run r s d).2 = outcome) :
    Classify b r (e.run r s d).1 d outcome :=
  (target.2.1 r checked s d outcome).mp returned

/-- 補助のみ：targetを仮定すればその完全性方向を取り出せる。
一般sourceの完全性の新証明ではない。 -/
theorem statement_complete (b : SourceBoundary v) (e : Executor v)
    (target : Statement b e) (r : v.Registry) (checked : b.Checked r)
    (s : v.State) (d : v.Demand) (outcome : Result)
    (derived : Classify b r (e.run r s d).1 d outcome) :
    (e.run r s d).2 = outcome :=
  (target.2.1 r checked s d outcome).mpr derived

end Yulang.B4Target

namespace Yulang.Main
/-- **未証明 B4 ターゲットschema。** 承認済み素描の五項を全量化して記述する。
具体source boundary/executorの構成と忠実性は未接続であり、これらを任意oracleで
埋めて完成とするものではない。質問ノートの親子分類と辞書同値を未決のまま明示する。 -/
def B4Statement (boundary : B4Target.SourceBoundary vocabulary)
    (executor : B4Target.Executor vocabulary) : Prop :=
  B4Target.Statement boundary executor
end Yulang.Main
