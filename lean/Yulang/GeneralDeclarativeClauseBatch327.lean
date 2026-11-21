import Yulang.GeneralDeclarativeFreshInputs325
import Yulang.GeneralDeclarativeGrowth327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeClauseBatch327
open GeneralDeclarations (Clause Declaration DeclarationChecked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeFreshInputs325 (prepared names_observed names_bounded whole_input_projection)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeSparseWhere325 (plan atPosition bodies planned compound_job)
open GeneralDeclarativeGrowth327 (Extends trans facts restrict)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (Expr translateMany)
open GeneralDeclarationPatterns (Constructors normalize)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

structure Port where
  code : List Expr
  input : Nat → Capture

def make (s : State) (protect : List Nat) (cap : Nat → Capture) (cl : Clause) (codes : List Expr) : Port :=
  let jobs := plan cl.arguments codes
  ⟨codes,atPosition (seed s protect cap jobs) jobs⟩

/-- Compile the independent visible syntax of all ordered where inputs
in one growing ordinary frame. Missing translation is a missing read,
not a verdict. This does not install or resolve any child. -/
def prepare (c : Constructors) (i : Interpretation) (protect : List Nat) (cap : Nat → Capture)
    (s : State) : List Clause → Option (State × List Port)
  | [] => some (s,[])
  | cl::rest => do
    let codes ← translateMany c i (cl.arguments.map normalize)
    let next := prepared s protect cap (plan cl.arguments codes)
    let (final,other) ← prepare c i protect cap next rest
    pure (final,make s protect cap cl codes :: other)

def Input (s : State) (c : Constructors) (i : Interpretation) (cap : Nat → Capture)
    (cl : Clause) (port : Port) : Prop :=
  translateMany c i (cl.arguments.map normalize) = some port.code ∧
  ∀ pos p e, cl.arguments[pos]? = some p → port.code[pos]? = some e → Compound p →
    Bounds s (port.input pos) ∧ Origin s (port.input pos).lower (logical cap .lower e) ∧
    Origin s (port.input pos).center (logical cap .actual e) ∧
    Origin s (port.input pos).upper (logical cap .upper e)

theorem reflexive (s : State) : Extends s s := ⟨fun _ h => h,fun _ h => h,fun _ h => h⟩

theorem make_grows (s : State) (protect : List Nat) (cap : Nat → Capture) (jobs : List (Option Expr)) :
    Extends s (prepared s protect cap jobs) :=
  ⟨fun _ h => h,fun _ h => List.mem_append_left _ h,fun _ h => List.mem_append_left _ h⟩

theorem past_origin {s t : State} (grows : Extends s t) (read : Origin s n e) : Origin t n e := by
  obtain ⟨src,linked,stored⟩ := read
  exact ⟨src,GeneralDeclarativeGrowth327.aliases grows linked,grows.equations stored⟩

theorem stored_port {s t : State} (grows : Extends (prepared s protect cap (plan cl.arguments codes)) t)
    (printed : translateMany c i (cl.arguments.map normalize) = some codes) :
    Input t c i cap cl (make s protect cap cl codes) := by
  refine ⟨printed,?_⟩
  intro pos p e pAt eAt compound
  have job := planned pAt eAt
  rw [compound_job compound] at job
  have observed := names_observed (s := s) (protect := protect) (cap := cap) job
  exact ⟨GeneralDeclarativeGrowth327.fits grows (names_bounded job),
    past_origin grows observed.1,past_origin grows observed.2.1,past_origin grows observed.2.2⟩

theorem read_order {s t : State}
    (actual : prepare c i protect cap s cs = some (t,ports)) :
    Extends s t ∧ All₂ (Input t c i cap) cs ports := by
  induction cs generalizing s ports with
  | nil =>
    have same : (s,[]) = (t,ports) := Option.some.inj actual
    cases same
    exact ⟨reflexive _, .nil⟩
  | cons cl rest ih =>
    cases viewed : translateMany c i (cl.arguments.map normalize) with
    | none => simp [prepare,viewed] at actual
    | some codes =>
      let next := prepared s protect cap (plan cl.arguments codes)
      cases more : prepare c i protect cap next rest with
      | none => simp [prepare,viewed,next,more] at actual
      | some pair =>
        obtain ⟨final,remaining⟩ := pair
        have same : (final,make s protect cap cl codes :: remaining) = (t,ports) := by
          simpa [prepare,viewed,next,more] using actual
        cases same
        obtain ⟨advance,ordered⟩ := ih more
        exact ⟨trans (make_grows s protect cap _) advance,
          .cons (stored_port advance viewed) ordered⟩

theorem all_read {s : State} {cs : List Clause}
    (given : ∀ cl ∈ cs, ∃ codes, translateMany c i (cl.arguments.map normalize) = some codes) :
    ∃ t ports, prepare c i protect cap s cs = some (t,ports) := by
  induction cs generalizing s with
  | nil => exact ⟨s,[],rfl⟩
  | cons cl rest ih =>
    obtain ⟨codes,obs⟩ := given cl List.mem_cons_self
    obtain ⟨last,more,trail⟩ :=
      ih (s := prepared s protect cap (plan cl.arguments codes)) (fun cl h => given cl (List.mem_cons_of_mem _ h))
    exact ⟨last,make s protect cap cl codes :: more,by simp [prepare,obs,trail]⟩

/-- Conservative extension for every ordered source clause, not merely
each in isolation. The original protected names survive every fold
step, including the caller's fixed associated targets. -/
theorem lift_model {s t : State} {cs : List Clause}
    (checked : DeclarationChecked c roles decl) (belongs : cs ⊆ decl.requirements)
    (bounds : ∀ n ∈ decl.inputNames, Bounds s (cap n))
    (actual : prepare c i protect cap s cs = some (t,ports)) (m)
    (initial : Models s m) :
    ∃ next, Models t next ∧ ∀ n ∈ protect, next n = m n := by
  induction cs generalizing s ports m with
  | nil =>
    have same : (s,[]) = (t,ports) := Option.some.inj actual
    cases same
    exact ⟨m,initial,fun _ _ => rfl⟩
  | cons cl rest ih =>
    cases viewed : translateMany c i (cl.arguments.map normalize) with
    | none => simp [prepare,viewed] at actual
    | some codes =>
      let next := prepared s protect cap (plan cl.arguments codes)
      cases more : prepare c i protect cap next rest with
      | none => simp [prepare,viewed,next,more] at actual
      | some pair =>
        obtain ⟨final,remaining⟩ := pair
        have same : (final,make s protect cap cl codes :: remaining) = (t,ports) := by
          simpa [prepare,viewed,next,more] using actual
        cases same
        have interval : ∀ n ∈ decl.inputNames, Bounds next (cap n) := fun n used =>
          GeneralDeclarativeGrowth327.fits (make_grows s protect cap _) (bounds n used)
        have projection := whole_input_projection (cap := cap) checked (belongs List.mem_cons_self)
          viewed bounds protect m
        obtain ⟨mid,valid,retained⟩ := projection.mp initial
        obtain ⟨latest,witness,still⟩ := ih
          (fun _ here => belongs (List.mem_cons_of_mem _ here)) interval more mid valid
        exact ⟨latest,witness,fun n keep => (still n keep).trans (retained n (List.mem_append_right _ keep))⟩

theorem exact_projection {s t : State}
    (checked : DeclarationChecked c roles decl) (belongs : cs ⊆ decl.requirements)
    (bounds : ∀ n ∈ decl.inputNames, Bounds s (cap n))
    (actual : prepare c i (stateNames s ++ protect) cap s cs = some (t,ports)) (m) :
    Models s m ↔ ∃ next, Models t next ∧ ∀ n ∈ stateNames s ++ protect, next n = m n := by
  constructor
  · exact lift_model checked belongs bounds actual m
  · rintro ⟨next,good,kept⟩
    exact (preserves_models s (fun n used => kept n (List.mem_append_left _ used))).mp
      (restrict (read_order actual).1 next good)

end Yulang.GeneralDeclarativeClauseBatch327
