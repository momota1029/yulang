import Yulang.GeneralDeclarativeOpaqueSingle328
import Yulang.GeneralDeclarativeInPlace327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueBatch328
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralSourceState (Output)
open GeneralDeclarativeOpaqueNested328 (Builds run)
open GeneralDeclarativeOpaqueSingle328 (linear compiler_head)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClauseBatch327 (prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)

def captureCode (a : Capture) : Nat × Nat × Nat := (a.lower,a.center,a.upper)
def outputCode : Output → Nat × Nat
  | ⟨key,target⟩ => (key,target)
def demandCode (d : Demand) :
    Nat × List (Nat × Nat × Nat) × List (Nat × Nat) :=
  (d.role,d.arguments.map captureCode,d.outputs.map outputCode)

theorem inject_map {f : α → β} (h : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro a b same
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => cases same
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at same
      cases h same.1
      cases ih same.2
      rfl

theorem capture_code_inj : Function.Injective captureCode := by
  rintro ⟨a,b,c⟩ ⟨x,y,z⟩ yes
  simp only [captureCode,Prod.mk.injEq] at yes
  obtain ⟨rfl,rfl,rfl⟩ := yes
  rfl

theorem output_code_inj : Function.Injective outputCode := by
  rintro ⟨a,b⟩ ⟨x,y⟩ yes
  simp only [outputCode,Prod.mk.injEq] at yes
  obtain ⟨rfl,rfl⟩ := yes
  rfl

theorem demand_code_inj : Function.Injective demandCode := by
  rintro ⟨a,b,c⟩ ⟨x,y,z⟩ yes
  simp only [demandCode,Prod.mk.injEq] at yes
  obtain ⟨rfl,arguments,outputs⟩ := yes
  cases inject_map capture_code_inj arguments
  cases inject_map output_code_inj outputs
  rfl

def check (compiled proposed : List Demand) : Bool :=
  decide (compiled.map demandCode = proposed.map demandCode)

theorem check_exact : check generated proposed = true ↔ generated = proposed := by
  simp only [check,decide_eq_true_eq]
  exact ⟨fun same => inject_map demand_code_inj same,congrArg _⟩

/-- An independently generated ordered child list can be compared to a
supplied selection for one explicit supported head and placement. This
is not a choice of one global canonical placement. Actual where/root
writes must already be ordinary rows of the *same* current state. -/
theorem accepted {s t current : State} {d : Demand} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (head : impl.head = [pat]) (args : d.arguments = [arg]) (span : Bounds s arg)
    (built : Builds s keep arg plan) (noRepeat : (names plan.code).Nodup)
    (printed : translate r.constructors i (normalize pat) = some plan.code)
    (fallback : Nat → Capture) (targets) (protect : List Nat)
    (growHead : Extends (run keep s arg plan).state current) (growWhere : Extends t current)
    (generated : prepare r.constructors i protect
      (sourceNames impl (targetsOnly targets) (linear keep s arg plan fallback)).input
      (run keep s arg plan).state impl.requirements = some (t,ports))
    (whereRows : whole r i impl
      (sourceNames impl (placement impl.requirements ports targets) (linear keep s arg plan fallback)) targets = some ws)
    (whereHere : ws ⊆ current.equations)
    (rootRows : collect (one r i impl d
      (sourceNames impl (placement impl.requirements ports targets) (linear keep s arg plan fallback)).input)
      d.outputs = some rs)
    (rootHere : rs ⊆ current.equations)
    (verified : check (children impl
      (sourceNames impl (placement impl.requirements ports targets) (linear keep s arg plan fallback))
      (placement impl.requirements ports targets)) proposed = true) :
    let cap := (sourceNames impl (placement impl.requirements ports targets) (linear keep s arg plan fallback)).input
    Result current (facts r i cap impl d proposed) ∧
      (∀ m, Models current m → Meaning r i m d impl cap proposed) ∧
      ∀ child ∈ proposed, Declared r child := by
  dsimp
  have placed := (check_exact.mp verified).symm
  subst proposed
  obtain ⟨known,headRead⟩ := compiler_head checked visible head args span built noRepeat printed
    fallback (placement impl.requirements ports targets) growHead
  obtain ⟨compiles,sound⟩ := GeneralDeclarativeInPlace327.current_sound checked covered visible role declared
    generated growWhere whereRows whereHere rootRows rootHere known headRead
  exact ⟨compiles,sound,fun _ present => GeneralDeclarativeOutputRequests323.child_declared checked visible present⟩

end Yulang.GeneralDeclarativeOpaqueBatch328
