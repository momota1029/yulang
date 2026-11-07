import Yulang.CommonPresence
import Yulang.PresenceBoundCoalescing

/-!
# Elimination of finite bounds in the independent common carrier

The finite topology is `LayerBoundTemplates`: lower bounds, variable edges,
upper bounds, and comparisons between fixed bounds. Bounds and parameters are
arbitrary `Common.Ty`, including masks, records, defaults, arrows and regular
graphs. No finite catalogue of data values or contextual types is used.

`rigidComparisons` eliminates every variable edge. Its output contains only
the original rigid comparisons and lower/upper pairs connected by a variable
path. If those finite comparisons hold, every assignment to the parameters of
`expand` is a solution. Conversely every independent solution is recovered up
to common demand equivalence by substituting that solution for the parameters.

The bounds are held fixed in this theorem. Applying it to recursive constructor
definitions additionally requires solving the resulting shared equations and
compiling their rigid comparisons; those obligations are not hidden in the
meaning of a parameter.
-/

namespace Yulang.CommonBoundCoalescing

open LayerBoundTemplates
open Common (Ty Subtype Equivalent)

universe u
variable {n : Nat} {Bound : Type u}

def Holds (evaluate : Bound → Ty) (value : Fin n → Ty) : Constraint n Bound → Prop
  | .lower bound target => Subtype (evaluate bound) (value target)
  | .flow source target => Subtype (value source) (value target)
  | .upper source bound => Subtype (value source) (evaluate bound)
  | .check source target => Subtype (evaluate source) (evaluate target)

def Models (evaluate : Bound → Ty) (problem : Problem n Bound) (value : Fin n → Ty) : Prop :=
  ∀ constraint ∈ problem, Holds evaluate value constraint

theorem bottom_le (type : Ty) : Subtype .bottom type := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  exact fun rank _ obs _ => CommonFinite.probeAt_bottom rank obs

theorem le_top (type : Ty) : Subtype type .top := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;>
    simp_all [Common.observeTy, CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt,
      CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem le_union_left (first last : Ty) : Subtype first (.union first last) :=
  (Common.common_union_is_join first last (.union first last)).mp
    (Common.subtype_refl _) |>.1

theorem le_union_right (first last : Ty) : Subtype last (.union first last) :=
  (Common.common_union_is_join first last (.union first last)).mp
    (Common.subtype_refl _) |>.2

theorem inter_le_left (first last : Ty) : Subtype (.inter first last) first :=
  (Common.common_inter_is_meet first last (.inter first last)).mp
    (Common.subtype_refl _) |>.1

theorem inter_le_right (first last : Ty) : Subtype (.inter first last) last :=
  (Common.common_inter_is_meet first last (.inter first last)).mp
    (Common.subtype_refl _) |>.2

def joinTypes : List Ty → Ty
  | [] => .bottom
  | type :: rest => .union type (joinTypes rest)

def meetTypes : List Ty → Ty
  | [] => .top
  | type :: rest => .inter type (meetTypes rest)

theorem joinTypes_le_iff (types : List Ty) (target : Ty) :
    Subtype (joinTypes types) target ↔ ∀ type ∈ types, Subtype type target := by
  induction types with
  | nil =>
      simp only [joinTypes, List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (bottom_le target)
  | cons type rest ih =>
      simp only [joinTypes, Common.common_union_is_join, ih, List.mem_cons, forall_eq_or_imp]

theorem le_meetTypes_iff (source : Ty) (types : List Ty) :
    Subtype source (meetTypes types) ↔ ∀ type ∈ types, Subtype source type := by
  induction types with
  | nil =>
      simp only [meetTypes, List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (le_top source)
  | cons type rest ih =>
      simp only [meetTypes, Common.common_inter_is_meet, ih, List.mem_cons, forall_eq_or_imp]

theorem member_le_joinTypes {type : Ty} {types : List Ty} (member : type ∈ types) :
    Subtype type (joinTypes types) :=
  (joinTypes_le_iff types _).mp (Common.subtype_refl _) type member

theorem meetTypes_le_member {type : Ty} {types : List Ty} (member : type ∈ types) :
    Subtype (meetTypes types) type :=
  (le_meetTypes_iff _ types).mp (Common.subtype_refl _) type member

def lower (evaluate : Bound → Ty) (problem : Problem n Bound) (target : Fin n) : Ty :=
  joinTypes ((lowerBounds problem target).map evaluate)

def upper (evaluate : Bound → Ty) (problem : Problem n Bound) (source : Fin n) : Ty :=
  meetTypes ((upperBounds problem source).map evaluate)

def variablePart (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (target : Fin n) : Ty :=
  joinTypes ((ancestors problem target).map fun source =>
    .inter (parameters source) (upper evaluate problem source))

def expand (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (target : Fin n) : Ty :=
  .union (lower evaluate problem target) (variablePart evaluate problem parameters target)

theorem lower_le_iff (evaluate : Bound → Ty) (problem : Problem n Bound)
    (target : Fin n) (type : Ty) :
    Subtype (lower evaluate problem target) type ↔
      ∀ bound ∈ lowerBounds problem target, Subtype (evaluate bound) type := by
  simp only [lower, joinTypes_le_iff, List.forall_mem_map]

theorem le_upper_iff (evaluate : Bound → Ty) (problem : Problem n Bound)
    (source : Fin n) (type : Ty) :
    Subtype type (upper evaluate problem source) ↔
      ∀ bound ∈ upperBounds problem source, Subtype type (evaluate bound) := by
  simp only [upper, le_meetTypes_iff, List.forall_mem_map]

theorem variablePart_le_iff (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (target : Fin n) (type : Ty) :
    Subtype (variablePart evaluate problem parameters target) type ↔
      ∀ source, Reaches problem source target →
        Subtype (.inter (parameters source) (upper evaluate problem source)) type := by
  simp only [variablePart, joinTypes_le_iff, List.forall_mem_map, mem_ancestors]

private theorem mem_successors (problem : Problem n Bound) (source target : Fin n) :
    target ∈ successors problem source ↔ .flow source target ∈ problem := by
  simp only [successors, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | flow start finish =>
        change (if start = source then some finish else none) = some target at found
        split at found
        · rename_i equal
          subst start
          have equal : finish = target := Option.some.inj found
          subst finish
          exact member
        · cases found
    | _ => cases found
  · intro member
    exact ⟨.flow source target, member, by simp⟩

theorem reaches_le {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value)
    {source target : Fin n} (path : Reaches problem source target) :
    Subtype (value source) (value target) := by
  induction path with
  | nil => exact Common.subtype_refl _
  | @cons source middle target edge rest ih =>
      exact Common.subtype_trans
        (model (.flow source middle) ((mem_successors problem source middle).mp edge)) ih

theorem lower_below {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (target : Fin n) :
    Subtype (lower evaluate problem target) (value target) := by
  apply (lower_le_iff _ _ _ _).mpr
  intro bound member
  obtain ⟨source, seed, path⟩ := (PresenceBoundCoalescing.mem_lowerBounds problem target bound).mp member
  exact Common.subtype_trans (model (.lower bound source) seed) (reaches_le model path)

theorem upper_above {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (source : Fin n) :
    Subtype (value source) (upper evaluate problem source) := by
  apply (le_upper_iff _ _ _ _).mpr
  intro bound member
  obtain ⟨target, seed, path⟩ := (PresenceBoundCoalescing.mem_upperBounds problem source bound).mp member
  exact Common.subtype_trans (reaches_le model path) (model (.upper target bound) seed)

theorem lower_lower (evaluate : Bound → Ty) (problem : Problem n Bound)
    (bound : Bound) (target : Fin n) (member : .lower bound target ∈ problem) :
    Subtype (evaluate bound) (lower evaluate problem target) := by
  apply member_le_joinTypes
  exact List.mem_map.mpr ⟨bound,
    (PresenceBoundCoalescing.mem_lowerBounds problem target bound).mpr
      ⟨target, member, .nil target⟩, rfl⟩

theorem lower_flow (evaluate : Bound → Ty) (problem : Problem n Bound)
    (source target : Fin n) (member : .flow source target ∈ problem) :
    Subtype (lower evaluate problem source) (lower evaluate problem target) := by
  apply (lower_le_iff _ _ _ _).mpr
  intro bound lowerMember
  obtain ⟨start, seed, path⟩ :=
    (PresenceBoundCoalescing.mem_lowerBounds problem source bound).mp lowerMember
  apply member_le_joinTypes
  exact List.mem_map.mpr ⟨bound,
    (PresenceBoundCoalescing.mem_lowerBounds problem target bound).mpr
      ⟨start, seed, path.append (.cons ((mem_successors problem source target).mpr member)
        (.nil target))⟩, rfl⟩

theorem lower_models_of_models {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) :
    Models evaluate problem (lower evaluate problem) := by
  intro constraint member
  cases constraint with
  | lower bound target => exact lower_lower evaluate problem bound target member
  | flow source target => exact lower_flow evaluate problem source target member
  | upper source bound => exact Common.subtype_trans (lower_below model source) (model _ member)
  | check source target => exact model _ member

/-- This finite output contains no variable occurrences. -/
def rigidComparisons (problem : Problem n Bound) : List (Bound × Bound) :=
  problem.flatMap fun
    | .lower _ _ | .flow _ _ => []
    | .upper source bound => (lowerBounds problem source).map fun lowerBound => (lowerBound, bound)
    | .check source target => [(source, target)]

def Consistent (evaluate : Bound → Ty) (problem : Problem n Bound) : Prop :=
  ∀ comparison ∈ rigidComparisons problem,
    Subtype (evaluate comparison.1) (evaluate comparison.2)

theorem rigid_comparisons_exact (evaluate : Bound → Ty) (problem : Problem n Bound) :
    Consistent evaluate problem ↔ Models evaluate problem (lower evaluate problem) := by
  constructor
  · intro checked constraint member
    cases constraint with
    | lower bound target => exact lower_lower evaluate problem bound target member
    | flow source target => exact lower_flow evaluate problem source target member
    | upper source bound =>
        apply (lower_le_iff _ _ _ _).mpr
        intro lowerBound lowerMember
        exact checked (lowerBound, bound)
          (List.mem_flatMap.mpr ⟨.upper source bound, member,
            List.mem_map.mpr ⟨lowerBound, lowerMember, rfl⟩⟩)
    | check source target =>
        exact checked (source, target)
          (List.mem_flatMap.mpr ⟨.check source target, member, by simp⟩)
  · intro model comparison member
    obtain ⟨constraint, originalMember, contributed⟩ := List.mem_flatMap.mp member
    cases constraint with
    | lower | flow => cases contributed
    | upper source bound =>
        obtain ⟨lowerBound, lowerMember, rfl⟩ := List.mem_map.mp contributed
        exact (lower_le_iff _ _ _ _).mp (model (.upper source bound) originalMember) lowerBound lowerMember
    | check source target =>
        have same : comparison = (source, target) := List.mem_singleton.mp contributed
        subst comparison
        exact model (.check source target) originalMember

private theorem contribution_below (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) {source target : Fin n} (path : Reaches problem source target) :
    Subtype (.inter (parameters source) (upper evaluate problem source))
      (variablePart evaluate problem parameters target) := by
  apply member_le_joinTypes
  exact List.mem_map.mpr ⟨source, (mem_ancestors problem source target).mpr path, rfl⟩

/-- Consistency mentions only fixed bounds; every common type parameter is free. -/
theorem expand_satisfies {evaluate : Bound → Ty} {problem : Problem n Bound}
    (consistent : Consistent evaluate problem) (parameters : Fin n → Ty) :
    Models evaluate problem (expand evaluate problem parameters) := by
  have lowerModel := (rigid_comparisons_exact evaluate problem).mp consistent
  intro constraint member
  cases constraint with
  | lower bound target =>
      exact Common.subtype_trans (lower_lower evaluate problem bound target member) (le_union_left _ _)
  | flow source target =>
      apply (Common.common_union_is_join _ _ _).mpr
      constructor
      · exact Common.subtype_trans (lower_flow evaluate problem source target member) (le_union_left _ _)
      · apply (variablePart_le_iff _ _ _ _ _).mpr
        intro start path
        exact Common.subtype_trans
          (contribution_below evaluate problem parameters
            (path.append (.cons ((mem_successors problem source target).mpr member) (.nil target))))
          (le_union_right _ _)
  | upper source bound =>
      apply (Common.common_union_is_join _ _ _).mpr
      refine ⟨lowerModel _ member, ?_⟩
      apply (variablePart_le_iff _ _ _ _ _).mpr
      intro start path
      apply Common.subtype_trans (inter_le_right _ _)
      apply meetTypes_le_member
      exact List.mem_map.mpr ⟨bound,
        (PresenceBoundCoalescing.mem_upperBounds problem start bound).mpr ⟨source, member, path⟩, rfl⟩
  | check source target => exact lowerModel _ member

/-- The original slot assignment is recovered, including negative occurrences. -/
theorem expand_retraction {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (target : Fin n) :
    Equivalent (expand evaluate problem value target) (value target) := by
  constructor
  · apply (Common.common_union_is_join _ _ _).mpr
    refine ⟨lower_below model target, ?_⟩
    apply (variablePart_le_iff _ _ _ _ _).mpr
    intro source path
    exact Common.subtype_trans (inter_le_left _ _) (reaches_le model path)
  · apply Common.subtype_trans (middle := .inter (value target) (upper evaluate problem target))
    · exact (Common.common_inter_is_meet _ _ _).mpr ⟨Common.subtype_refl _, upper_above model target⟩
    · exact Common.subtype_trans (contribution_below evaluate problem value (.nil target))
        (le_union_right _ _)

theorem models_congr (evaluate : Bound → Ty) (problem : Problem n Bound)
    {first last : Fin n → Ty} (same : ∀ index, Equivalent (first index) (last index)) :
    Models evaluate problem first ↔ Models evaluate problem last := by
  constructor
  · intro model constraint member
    cases constraint with
    | lower bound target => exact Common.subtype_trans (model _ member) (same target).1
    | flow source target =>
        exact Common.subtype_trans (same source).2 (Common.subtype_trans (model _ member) (same target).1)
    | upper source bound => exact Common.subtype_trans (same source).2 (model _ member)
    | check source target => exact model _ member
  · intro model constraint member
    cases constraint with
    | lower bound target => exact Common.subtype_trans (model _ member) (same target).2
    | flow source target =>
        exact Common.subtype_trans (same source).1 (Common.subtype_trans (model _ member) (same target).2)
    | upper source bound => exact Common.subtype_trans (same source).1 (model _ member)
    | check source target => exact model _ member

theorem consistent_iff_satisfiable (evaluate : Bound → Ty) (problem : Problem n Bound) :
    Consistent evaluate problem ↔ ∃ value, Models evaluate problem value := by
  rw [rigid_comparisons_exact]
  exact ⟨fun model => ⟨_, model⟩, fun ⟨_, model⟩ => lower_models_of_models model⟩

/-- No solver model or predicate on the parameters remains on the right. -/
theorem all_instances_exact (evaluate : Bound → Ty) (problem : Problem n Bound)
    (value : Fin n → Ty) :
    Models evaluate problem value ↔
      Consistent evaluate problem ∧
        ∃ parameters, ∀ index, Equivalent (expand evaluate problem parameters index) (value index) := by
  constructor
  · intro model
    exact ⟨(consistent_iff_satisfiable evaluate problem).mpr ⟨value, model⟩,
      value, expand_retraction model⟩
  · rintro ⟨consistent, parameters, same⟩
    exact (models_congr evaluate problem same).mp (expand_satisfies consistent parameters)

end Yulang.CommonBoundCoalescing
