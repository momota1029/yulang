import Yulang.CommonRoleSettledResolver
import Yulang.CommonRoleOpenRecursivePass
import Yulang.CommonRoleOpenPassStability
import Yulang.CommonDeclarationVarianceRegistry
import Yulang.CommonSourceOptionalX22
import Yulang.CoreCommonInference
import Yulang.CommonDeclaredCastCost

/-!
# M1 の主張を読む窓口 — 草稿、2026-11-08

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
`cd lean && lake build Yulang.MainStatementsDraft --wfail`
root の Main*.lean 配置は verify gate の更新待ち。現在はこの新規モジュールに置く。
-/
namespace Yulang.MainStatements

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

end Yulang.MainStatements
