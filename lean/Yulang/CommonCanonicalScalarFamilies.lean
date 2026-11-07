import Yulang.CommonCanonicalParameters
import Yulang.CommonBoundCoalescing

/-!
# Canonical scalar instance families with fixed weak parameters

The scalar lattice syntax is unchanged. Its first `weak` slots are ambient
or weak parameters: their simultaneous assignment is held fixed. Only the
remaining `generalized` slots are independently quantified at instantiation.
The two counts are not identified, and compared families may have different
generalized arities, including zero.

Every exact instance family is precisely the order interval between the two
expressions obtained by replacing all generalized slots with bottom or top.
Every upward instance family is determined by the lower endpoint alone.
Thus finite canonical codes decide both family equivalences over all weak
assignments and all common types, not merely same-arity alpha equivalence.

The result is specific to a covariant scalar lattice expression. Shared
negative occurrences, row expressions, qualified role requirements and
regular public interface bodies require additional joint reasoning. No
public printer or encoding for that larger grammar is claimed here.
-/

namespace Yulang.CommonCanonicalScalarFamilies

open ProducerCanonicalOpen (Expr Atom)
open Common (Ty Subtype Equivalent)
open CommonCanonicalOpen (instantiate)
open CommonCanonicalParameters (substituteExpr instantiate_substituteExpr)
open CommonFinite (ProbeAt)

variable {weak generalized other : Nat}

def environment (ambient : Fin weak → Ty) (parameters : Fin generalized → Ty) :
    Fin (weak + generalized) → Ty := Fin.addCases ambient parameters

def replacement (high : Bool) : Fin (weak + generalized) → Expr weak :=
  Fin.addCases (fun index => .atom (.var index)) (fun _ => if high then .top else .bottom)

def endpoint (high : Bool) (expression : Expr (weak + generalized)) : Expr weak :=
  substituteExpr (replacement high) expression

def lower (expression : Expr (weak + generalized)) : Expr weak := endpoint false expression
def upper (expression : Expr (weak + generalized)) : Expr weak := endpoint true expression

theorem endpoint_eval (high : Bool) (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) :
    instantiate ambient (endpoint high expression) =
      instantiate (environment ambient (fun _ => if high then .top else .bottom)) expression := by
  rw [endpoint, instantiate_substituteExpr]
  congr 1
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro index
    simp only [replacement, environment, Fin.addCases_left, instantiate, CommonCanonicalOpen.atomType]
  · intro index
    simp only [replacement, environment, Fin.addCases_right]
    cases high <;> rfl

theorem lower_eval (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) :
    instantiate ambient (lower expression) =
      instantiate (environment ambient (fun _ => .bottom)) expression := endpoint_eval false expression ambient

theorem upper_eval (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) :
    instantiate ambient (upper expression) =
      instantiate (environment ambient (fun _ => .top)) expression := endpoint_eval true expression ambient

theorem instantiate_mono (expression : Expr n) (first last : Fin n → Ty)
    (below : ∀ index, Subtype (first index) (last index)) :
    Subtype (instantiate first expression) (instantiate last expression) := by
  induction expression with
  | atom entry =>
      cases entry with
      | var index => exact below index
      | base => exact Common.subtype_refl _
  | bottom | top => exact Common.subtype_refl _
  | union _ _ ihf ihl => exact Common.common_union_mono ihf ihl
  | inter _ _ ihf ihl => exact Common.common_inter_mono ihf ihl

theorem lower_le_instance (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty)
    (parameters : Fin generalized → Ty) :
    Subtype (instantiate ambient (lower expression)) (instantiate (environment ambient parameters) expression) := by
  rw [lower_eval]
  apply instantiate_mono
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro index
    simpa only [environment, Fin.addCases_left] using Common.subtype_refl (ambient index)
  · intro index
    simpa only [environment, Fin.addCases_right] using CommonBoundCoalescing.bottom_le (parameters index)

theorem instance_le_upper (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty)
    (parameters : Fin generalized → Ty) :
    Subtype (instantiate (environment ambient parameters) expression) (instantiate ambient (upper expression)) := by
  rw [upper_eval]
  apply instantiate_mono
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro index
    simpa only [environment, Fin.addCases_left] using Common.subtype_refl (ambient index)
  · intro index
    simpa only [environment, Fin.addCases_right] using CommonBoundCoalescing.le_top (parameters index)

theorem lower_le_upper (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) :
    Subtype (instantiate ambient (lower expression)) (instantiate ambient (upper expression)) := by
  rw [lower_eval]
  exact instance_le_upper expression ambient (fun _ => .bottom)

private def probe (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (observation : Common.Observation) (type : Ty) : Prop :=
  ProbeAt Common.rowLe rank env (Common.observeTy depth type) observation

private theorem probe_bottom (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (observation : Common.Observation) : probe depth rank env observation .bottom :=
  CommonFinite.probeAt_bottom rank observation

private theorem not_probe_top (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (observation : Common.Observation) (nontrivial : observation ≠ .trivial) :
    ¬ probe depth rank env observation .top := by
  cases rank <;> cases observation <;>
    simp_all [probe, Common.observeTy, CommonSyntax.Layer.evalAt, ProbeAt,
      CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

private theorem instantiate_probe_congr (expression : Expr n) (first last : Fin n → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (observation : Common.Observation)
    (same : ∀ index, probe depth rank env observation (first index) ↔
      probe depth rank env observation (last index)) :
    probe depth rank env observation (instantiate first expression) ↔
      probe depth rank env observation (instantiate last expression) := by
  induction expression with
  | atom entry => cases entry with
    | var index => exact same index
    | base => rfl
  | bottom | top => rfl
  | union _ _ ihf ihl =>
      simpa only [instantiate, probe, Common.observeTy, CommonSyntax.Layer.evalAt,
        CommonFinite.probeAt_union] using and_congr ihf ihl
  | inter _ _ ihf ihl =>
      simpa only [instantiate, probe, Common.observeTy, CommonSyntax.Layer.evalAt,
        CommonFinite.probeAt_inter] using or_congr ihf ihl

/-- Any candidate between the two endpoints is recovered by assigning that
same candidate to every generalized slot. This also covers zero slots. -/
theorem diagonal_retract (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty)
    (target : Ty) (below : Subtype (instantiate ambient (lower expression)) target)
    (above : Subtype target (instantiate ambient (upper expression))) :
    Equivalent (instantiate (environment ambient (fun _ => target)) expression) target := by
  apply (CommonCanonicalShapes.equivalent_iff_probes _ _).mpr
  intro depth rank env observation
  change probe depth rank env observation _ ↔ probe depth rank env observation target
  by_cases trivial : observation = .trivial
  · subst observation
    simp [probe]
  by_cases accepted : probe depth rank env observation target
  · have same := instantiate_probe_congr expression
      (environment ambient (fun _ => target)) (environment ambient (fun _ => .bottom))
      depth rank env observation (by
        intro index
        refine Fin.addCases ?_ ?_ index
        · intro index; simp only [environment, Fin.addCases_left]
        · intro index
          simp only [environment, Fin.addCases_right]
          exact ⟨fun _ => probe_bottom depth rank env observation, fun _ => accepted⟩)
    have bound := (CommonFinite.producerLe_iff_probe _ _).mp (below depth) rank env observation accepted
    rw [lower_eval] at bound
    exact ⟨fun _ => accepted, fun _ => same.mpr bound⟩
  · have same := instantiate_probe_congr expression
      (environment ambient (fun _ => target)) (environment ambient (fun _ => .top))
      depth rank env observation (by
        intro index
        refine Fin.addCases ?_ ?_ index
        · intro index; simp only [environment, Fin.addCases_left]
        · intro index
          simp only [environment, Fin.addCases_right]
          exact iff_of_false accepted (not_probe_top depth rank env observation trivial))
    have excluded : ¬ probe depth rank env observation (instantiate ambient (upper expression)) :=
      fun present => accepted ((CommonFinite.producerLe_iff_probe _ _).mp (above depth) rank env observation present)
    rw [upper_eval] at excluded
    exact iff_of_false (fun present => excluded (same.mp present)) accepted

def ExactInstances (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) (target : Ty) : Prop :=
  ∃ parameters : Fin generalized → Ty, Equivalent (instantiate (environment ambient parameters) expression) target

def Instances (expression : Expr (weak + generalized)) (ambient : Fin weak → Ty) (target : Ty) : Prop :=
  ∃ parameters : Fin generalized → Ty, Subtype (instantiate (environment ambient parameters) expression) target

/-- Exact generalized instances form the complete interval, with arbitrary
common regular/masked/function types permitted both as parameters and targets. -/
theorem exact_instances_iff_bounds (expression : Expr (weak + generalized))
    (ambient : Fin weak → Ty) (target : Ty) :
    ExactInstances expression ambient target ↔
      Subtype (instantiate ambient (lower expression)) target ∧
        Subtype target (instantiate ambient (upper expression)) := by
  constructor
  · rintro ⟨parameters, same⟩
    exact ⟨Common.subtype_trans (lower_le_instance expression ambient parameters) same.1,
      Common.subtype_trans same.2 (instance_le_upper expression ambient parameters)⟩
  · rintro ⟨below, above⟩
    exact ⟨fun _ => target, diagonal_retract expression ambient target below above⟩

/-- Only generalized slots disappear. Ambient/weak values remain fixed and
are retained in the lower expression, even if used only positively. -/
theorem instances_iff_lower (expression : Expr (weak + generalized))
    (ambient : Fin weak → Ty) (target : Ty) :
    Instances expression ambient target ↔ Subtype (instantiate ambient (lower expression)) target := by
  constructor
  · rintro ⟨parameters, below⟩
    exact Common.subtype_trans (lower_le_instance expression ambient parameters) below
  · intro below
    refine ⟨fun _ => .bottom, ?_⟩
    simpa only [lower_eval] using below

def ExactFamilyEquivalent (first : Expr (weak + generalized)) (last : Expr (weak + other)) : Prop :=
  ∀ ambient : Fin weak → Ty, ∀ target : Ty,
    ExactInstances first ambient target ↔ ExactInstances last ambient target

def FamilyEquivalent (first : Expr (weak + generalized)) (last : Expr (weak + other)) : Prop :=
  ∀ ambient : Fin weak → Ty, ∀ target : Ty,
    Instances first ambient target ↔ Instances last ambient target

theorem exact_family_iff_endpoints (first : Expr (weak + generalized)) (last : Expr (weak + other)) :
    ExactFamilyEquivalent first last ↔
      CommonCanonicalOpen.Equivalent (lower first) (lower last) ∧
        CommonCanonicalOpen.Equivalent (upper first) (upper last) := by
  constructor
  · intro same
    have endpoints (ambient : Fin weak → Ty) :
        Equivalent (instantiate ambient (lower first)) (instantiate ambient (lower last)) ∧
          Equivalent (instantiate ambient (upper first)) (instantiate ambient (upper last)) := by
      have firstLower := (exact_instances_iff_bounds first ambient _).mpr
        ⟨Common.subtype_refl _, lower_le_upper first ambient⟩
      have lastLower := (exact_instances_iff_bounds last ambient _).mpr
        ⟨Common.subtype_refl _, lower_le_upper last ambient⟩
      have firstUpper := (exact_instances_iff_bounds first ambient _).mpr
        ⟨lower_le_upper first ambient, Common.subtype_refl _⟩
      have lastUpper := (exact_instances_iff_bounds last ambient _).mpr
        ⟨lower_le_upper last ambient, Common.subtype_refl _⟩
      exact ⟨⟨((exact_instances_iff_bounds first ambient _).mp ((same ambient _).mpr lastLower)).1,
          ((exact_instances_iff_bounds last ambient _).mp ((same ambient _).mp firstLower)).1⟩,
        ⟨((exact_instances_iff_bounds last ambient _).mp ((same ambient _).mp firstUpper)).2,
          ((exact_instances_iff_bounds first ambient _).mp ((same ambient _).mpr lastUpper)).2⟩⟩
    exact ⟨fun ambient => (endpoints ambient).1, fun ambient => (endpoints ambient).2⟩
  · rintro ⟨lowerSame, upperSame⟩ ambient target
    rw [exact_instances_iff_bounds, exact_instances_iff_bounds]
    constructor
    · rintro ⟨below, above⟩
      exact ⟨Common.subtype_trans (lowerSame ambient).2 below,
        Common.subtype_trans above (upperSame ambient).1⟩
    · rintro ⟨below, above⟩
      exact ⟨Common.subtype_trans (lowerSame ambient).1 below,
        Common.subtype_trans above (upperSame ambient).2⟩

theorem family_iff_lower (first : Expr (weak + generalized)) (last : Expr (weak + other)) :
    FamilyEquivalent first last ↔ CommonCanonicalOpen.Equivalent (lower first) (lower last) := by
  constructor
  · intro same ambient
    exact ⟨(instances_iff_lower first ambient _).mp
        ((same ambient _).mpr ((instances_iff_lower last ambient _).mpr (Common.subtype_refl _))),
      (instances_iff_lower last ambient _).mp
        ((same ambient _).mp ((instances_iff_lower first ambient _).mpr (Common.subtype_refl _)))⟩
  · intro same ambient target
    rw [instances_iff_lower, instances_iff_lower]
    exact ⟨fun below => Common.subtype_trans (same ambient).2 below,
      fun below => Common.subtype_trans (same ambient).1 below⟩

/-- Codes have no generalized-arity index. They retain the original shared
weak-slot IDs, whose assignment is universally quantified. -/
def exactCanonicalEncoding (expression : Expr (weak + generalized)) :
    List (List (Atom weak)) × List (List (Atom weak)) :=
  (CommonCanonicalOpen.canonicalEncoding (lower expression), CommonCanonicalOpen.canonicalEncoding (upper expression))

def canonicalEncoding (expression : Expr (weak + generalized)) : List (List (Atom weak)) :=
  CommonCanonicalOpen.canonicalEncoding (lower expression)

theorem exactCanonicalEncoding_exact (first : Expr (weak + generalized)) (last : Expr (weak + other)) :
    ExactFamilyEquivalent first last ↔ exactCanonicalEncoding first = exactCanonicalEncoding last := by
  rw [exact_family_iff_endpoints]
  simp only [exactCanonicalEncoding, Prod.mk.injEq, ← CommonCanonicalOpen.canonicalEncoding_exact]

theorem canonicalEncoding_exact (first : Expr (weak + generalized)) (last : Expr (weak + other)) :
    FamilyEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last :=
  (family_iff_lower first last).trans (CommonCanonicalOpen.canonicalEncoding_exact _ _)

namespace Examples

/-- Both generalized slots occur, but one unrestricted slot has the same
exact instance range. The codes compare different generalized arities. -/
theorem used_union_parameters_merge :
    exactCanonicalEncoding (weak := 0) (generalized := 2)
      (.union (.atom (.var 0)) (.atom (.var 1))) =
    exactCanonicalEncoding (weak := 0) (generalized := 1) (.atom (.var 0)) := by decide +kernel

theorem weak_slot_is_not_generalized :
    canonicalEncoding (weak := 1) (generalized := 1) (.atom (.var 0)) ≠
      canonicalEncoding (weak := 1) (generalized := 1) (.atom (.var 1)) := by decide +kernel

theorem weak_union_retained :
    canonicalEncoding (weak := 1) (generalized := 1)
      (.union (.atom (.var 0)) (.atom (.var 1))) =
      CommonCanonicalOpen.canonicalEncoding (n := 1) (.atom (.var 0)) := by decide +kernel

end Examples

end Yulang.CommonCanonicalScalarFamilies
