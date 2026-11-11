import Yulang.CommonRoleOrdinaryKnownness
import Yulang.RoleDictionaries

/-!
# 単一 scalar 宣言の辞書から全 ordinary モデルへ

int/str、一引数、whereなしの可視宣言1個だけの断片。
receiverは実ordinary paired boundsから得る。候補の一意性から型を推測しない。
実ordinary solverと既存dictionary elaboratorを実行し、実際の宣言identityと
空のwhere列を含む辞書が、すべてのCommonモデルでheadに整合することを示す。
method bodyの実行意味、一般区間、関連型、一般B4は対象外。
-/
namespace Yulang.CommonRoleScalarDictionaryModels
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (materialize)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open RoleDictionaries (Plan Answer Dictionary)

inductive Scalar where
  | int
  | str
  deriving DecidableEq, Repr

def Scalar.base : Scalar → Inference.Base
  | .int => .int
  | .str => .str

def Scalar.term : Scalar → Roles.Term
  | .int => .app 0 []
  | .str => .app 1 []

def declaration (role key : Nat) (scalar : Scalar) : Roles.Impl :=
  ⟨role, [scalar.term], [], key⟩

def goal (role : Nat) (term : Roles.Term) : Roles.Goal := ⟨role, [term]⟩

def plan (role key : Nat) (scalar : Scalar) : Plan := .node (declaration role key scalar) []

theorem wellFormed (role key : Nat) (scalar : Scalar) :
    Roles.WellFormed [declaration role key scalar] := by
  intro d member
  have same : d = declaration role key scalar := by simpa using member
  subst d
  simp [Roles.Impl.WellFormed, declaration]

/-- 独立な一方向head照合は、元のscalar termとの一致だけを要求する。 -/
theorem matches_exact (role key : Nat) (scalar : Scalar) (term : Roles.Term) :
    Roles.Matches (declaration role key scalar) (goal role term) ↔ term = scalar.term := by
  cases scalar <;> simp [Roles.Matches, declaration, goal, Scalar.term,
    Roles.substArgs, Roles.Term.subst, eq_comm]
  all_goals constructor
  all_goals first | exact fun ⟨_, h⟩ => h | exact fun h => ⟨fun name => .var name, h⟩

theorem unique (role key : Nat) (scalar : Scalar) :
    Roles.candidates [declaration role key scalar] (goal role scalar.term) =
      [declaration role key scalar] := by
  have matched := (Roles.matches_iff _ _).mpr ((matches_exact role key scalar scalar.term).mpr rfl)
  simp [Roles.candidates, Roles.distinct, matched]

/-- 実headと空whereから、既存の型付き辞書を構成する。 -/
def dictionary (role key : Nat) (scalar : Scalar) :
    Dictionary [declaration role key scalar] (goal role scalar.term) :=
  .impl (declaration role key scalar) (unique role key scalar)
    (fun _ impossible => False.elim (List.not_mem_nil impossible))

/-- 任意の返却planに対するiff。辞書の形や宣言identityは外部入力にしない。 -/
theorem elaborate_exact (role key : Nat) (scalar : Scalar) (term : Roles.Term) (out : Plan) :
    RoleDictionaries.elaborate [declaration role key scalar] (wellFormed role key scalar)
      (goal role term) = .resolved out ↔ term = scalar.term ∧ out = plan role key scalar := by
  rw [RoleDictionaries.elaborate_success_iff]
  constructor
  · rintro ⟨evidence, erased⟩
    cases evidence with
    | impl chosen chosenUnique children =>
        have member := Roles.mem_candidates.mp (chosenUnique ▸ List.mem_singleton_self chosen)
        have same : chosen = declaration role key scalar := by simpa using member.1
        subst chosen
        refine ⟨(matches_exact role key scalar term).mp member.2, ?_⟩
        simpa [RoleDictionaries.Dictionary.erase, declaration, plan] using erased.symm
  · rintro ⟨rfl, rfl⟩
    exact ⟨dictionary role key scalar, rfl⟩

/-- ordinary solver、実paired-bound materializer、実dictionary elaboratorの順。 -/
def run (role key : Nat) (scalar : Scalar) (receiver : Fin n) (state : State n) : Option Answer :=
  if CommonRoleOpenPropagation.consistent state then
    (materialize state.atoms receiver).map fun term =>
      RoleDictionaries.elaborate [declaration role key scalar] (wellFormed role key scalar) (goal role term)
  else none

/-- 健全性/完全性: 任意のstate/receiver/planで、実成功 iff 整合性・実materialization・実辞書。
成功やModelsを外部の前提としない。 -/
theorem run_exact (role key : Nat) (scalar : Scalar) (receiver : Fin n) (state : State n) (out : Plan) :
    run role key scalar receiver state = some (.resolved out) ↔
      state.Models ∧ materialize state.atoms receiver = some scalar.term ∧ out = plan role key scalar := by
  unfold run
  by_cases consistent : CommonRoleOpenPropagation.consistent state = true
  · have models := (CommonRoleOpenPropagation.consistent_exact state).mp consistent
    simp only [consistent, ↓reduceIte, Option.map_eq_some_iff, models, true_and]
    constructor
    · rintro ⟨term, found, elaborated⟩
      obtain ⟨rfl, same⟩ := (elaborate_exact role key scalar term out).mp elaborated
      exact ⟨found, same⟩
    · rintro ⟨found, same⟩
      exact ⟨scalar.term, found, (elaborate_exact role key scalar scalar.term out).mpr ⟨rfl, same⟩⟩
  · have notModels : ¬ state.Models := fun models => consistent ((CommonRoleOpenPropagation.consistent_exact state).mpr models)
    simp [consistent, notModels]

/-- 実行版を含まない辞書の意味。一つのscalar headに対する実モデルの整合性、
実宣言identity、全where子列（空）を同時に保持する。 -/
inductive Implements (role key : Nat) (scalar : Scalar) (argument : Common.Ty) : Plan → Prop where
  | leaf : Common.Equivalent argument (.base scalar.base) →
      Implements role key scalar argument (plan role key scalar)

/-- 健全性: 返された実辞書は、solverが選んだ一つでなく、旧stateの全モデルで成り立つ。 -/
theorem run_all_models (role key : Nat) (scalar : Scalar) (receiver : Fin n) (state : State n)
    (out : Plan) (returned : run role key scalar receiver state = some (.resolved out))
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment state.atoms) :
    Implements role key scalar (assignment receiver).1 out := by
  obtain ⟨_, materialized, rfl⟩ := (run_exact role key scalar receiver state out).mp returned
  obtain ⟨base, decoded, equal⟩ :=
    CommonRoleOrdinaryKnownness.materialize_sound state.atoms receiver scalar.term materialized assignment models
  have same : base = scalar.base := by
    cases scalar <;> simpa [Scalar.term, Scalar.base, CommonRoleAssociatedStateFlow.scalar] using decoded.symm
  subst base
  exact .leaf equal

/-- 成功 iff 整合性と明示的なreceiverのmaterialization。全モデル証拠も同時に得る。 -/
theorem successful_dictionary_exact (role key : Nat) (scalar : Scalar) (receiver : Fin n) (state : State n) :
    (∃ out, run role key scalar receiver state = some (.resolved out) ∧
      ∀ assignment : Fin n → Comp Common.model, All Common.model assignment state.atoms →
        Implements role key scalar (assignment receiver).1 out) ↔
      state.Models ∧ materialize state.atoms receiver = some scalar.term := by
  constructor
  · rintro ⟨out, returned, _⟩
    exact ((run_exact role key scalar receiver state out).mp returned).imp_right (fun h => h.1)
  · rintro ⟨models, materialized⟩
    have returned := (run_exact role key scalar receiver state (plan role key scalar)).mpr ⟨models, materialized, rfl⟩
    exact ⟨plan role key scalar, returned, run_all_models role key scalar receiver state _ returned⟩

/-- 宣言が唯一でもreceiverのordinary evidenceがなければ辞書は生成しない。 -/
theorem empty_pending (role key : Nat) (scalar : Scalar) (receiver : Fin n) :
    run role key scalar receiver State.empty = none := by
  unfold run
  split <;> rfl

end Yulang.CommonRoleScalarDictionaryModels
