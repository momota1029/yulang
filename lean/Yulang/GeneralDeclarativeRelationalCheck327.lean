import Yulang.GeneralDeclarativeFrontierView327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRelationalCheck327
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativePriority321 (Candidates Local Recurs Blocked)
open GeneralDeclarativeFrontier327 (Unique)
open GeneralDeclarativeFrontierView327 (decision ExactInputs)
open CommonRoleOutermostResolver (Frontier)

structure Flags where
  lower : Bool
  k2 : Bool
  passes : Declaration → Bool
  waiting : Declaration → Bool

structure Observes (s : State) (r : Registry) (i : GeneralNominalInspection.Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) (d : Demand) (f : Flags) : Prop where
  lower : f.lower = true ↔ Ready p d
  k2 : f.k2 = true ↔ Recurs s r i tests d
  passes : ∀ decl ∈ r.declarations, decl.role = d.role → (f.passes decl = true ↔ tests.viable d decl)
  waiting : ∀ decl ∈ r.declarations, decl.role = d.role → (f.waiting decl = true ↔ tests.unresolved d decl)

inductive Tag where
  | pending
  | ambiguous
  | rejected
  | elected (key : Nat)
  deriving DecidableEq

def tag : Frontier Demand → Tag
  | .pending => .pending
  | .ambiguous => .ambiguous
  | .rejected => .rejected
  | .selected key _ => .elected key

def blank : Tag → Frontier Demand
  | .pending => .pending
  | .ambiguous => .ambiguous
  | .rejected => .rejected
  | .elected key => .selected key []

/-- This computes only an election/terminal tag. The elected
constructor is not a selected frontier without a separately certified
literal ordered child list. -/
def guard (r : Registry) (d : Demand) (f : Flags) : Option Tag :=
  (decision r d f.lower f.k2 f.passes f.waiting (fun _ => some [])).map tag

def EmptyGeneration (_ : Demand) (_ : Declaration) (kids : List Demand) : Prop := kids = []

theorem empty_inputs {s : State} {p : Supported s done}
    (which : Observes s r i p tests d flags) :
    ExactInputs s r i p tests d EmptyGeneration flags.lower flags.k2 flags.passes flags.waiting
      (fun _ => some []) :=
  ⟨which.lower,which.k2,which.passes,which.waiting,
    fun _ _ _ _ _ _ => ⟨fun eq => (Option.some.inj eq).symm,fun eq => congrArg some eq.symm⟩⟩

theorem exact_guard {s : State} {p : Supported s done} (checked : Checked r)
    (which : Observes s r i p tests d flags) :
    guard r d flags = some code ↔ Local s r i p tests EmptyGeneration d (blank code) := by
  constructor
  · intro reported
    unfold guard at reported
    cases h : decision r d flags.lower flags.k2 flags.passes flags.waiting (fun _ => some []) with
    | none => simp [h] at reported
    | some raw =>
      have actual : tag raw = code := by simpa [h] using reported
      subst code
      have deriv := (GeneralDeclarativeFrontierView327.exact checked (empty_inputs which)).mp h
      cases deriv with
      | unsupported wait safe => exact .unsupported wait safe
      | recursive ready recurs => exact .recursive ready recurs
      | unresolved ready safe blocked => exact .unresolved ready safe blocked
      | noCandidate ready safe clear nowhere => exact .noCandidate ready safe clear nowhere
      | ambiguous ready safe clear a b apart => exact .ambiguous ready safe clear a b apart
      | selected ready safe clear unique sole none => exact .selected ready safe clear unique sole rfl
  · intro prior
    have computed := (GeneralDeclarativeFrontierView327.exact checked (empty_inputs which)).mpr prior
    cases code <;> simp [guard,computed,tag,blank]

def check (r : Registry) (d : Demand) (f : Flags) (emits : Nat → List Demand → Bool)
    (claim : Frontier Demand) : Bool :=
  decide (guard r d f = some (tag claim)) &&
    match claim with
    | .selected k kids => emits k kids
    | _ => true

/-- The relational validator checks a proposed list instead of producing
one; multiple correct lists are permitted. Correctness is needed at
the unique surviving role candidate only, not for forged/nonvisible keys. -/
def Verifies (s : State) (r : Registry) (i : GeneralNominalInspection.Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) (d : Demand)
    (generates : Demand → Declaration → List Demand → Prop) (emits : Nat → List Demand → Bool) : Prop :=
  Ready p d → ¬Recurs s r i tests d → ¬Blocked r tests d →
    ∀ decl, Unique r tests d decl → ∀ kids, emits decl.id kids = true ↔ generates d decl kids

theorem at_exact {s : State} {p : Supported s done} (checked : Checked r)
    (which : Observes s r i p tests d flags) (validator : Verifies s r i p tests d generates emits) :
    check r d flags emits claim = true ↔ Local s r i p tests generates d claim := by
  have compare := exact_guard checked which (code := tag claim)
  unfold check
  rw [Bool.and_eq_true]
  constructor
  · intro h
    have observed := compare.mp (of_decide_eq_true h.1)
    cases claim with
    | pending =>
      cases observed with
      | unsupported lack safe => exact .unsupported lack safe
      | unresolved r safe blocked => exact .unresolved r safe blocked
    | rejected =>
      cases observed with
      | recursive r rec => exact .recursive r rec
      | noCandidate r safe clear absent => exact .noCandidate r safe clear absent
    | ambiguous =>
      cases observed with
      | ambiguous r safe clear a b apart => exact .ambiguous r safe clear a b apart
    | selected key kids =>
      cases observed with
      | selected r safe clear winner only _ =>
        exact .selected r safe clear winner only ((validator r safe clear _ ⟨winner,only⟩ kids).mp h.2)
  · intro derive
    cases derive with
    | unsupported lack safe =>
      exact ⟨decide_eq_true (compare.mpr (.unsupported lack safe)),rfl⟩
    | recursive r rec =>
      exact ⟨decide_eq_true (compare.mpr (.recursive r rec)),rfl⟩
    | unresolved ready safe blocked =>
      exact ⟨decide_eq_true (compare.mpr (.unresolved ready safe blocked)),rfl⟩
    | noCandidate r safe clear absent =>
      exact ⟨decide_eq_true (compare.mpr (.noCandidate r safe clear absent)),rfl⟩
    | ambiguous r safe clear a b apart =>
      exact ⟨decide_eq_true (compare.mpr (.ambiguous r safe clear a b apart)),rfl⟩
    | selected r safe clear winner only built =>
      exact ⟨decide_eq_true (compare.mpr (.selected r safe clear winner only rfl)),
        (validator r safe clear _ ⟨winner,only⟩ _).mpr built⟩

end Yulang.GeneralDeclarativeRelationalCheck327
