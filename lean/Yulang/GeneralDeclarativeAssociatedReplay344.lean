import Yulang.GeneralDeclarativeEffectiveReplay344
import Yulang.GeneralDeclarativeWhereOutputBatch327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAssociatedReplay344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (normalize)
open GeneralWhereVersionCompiler317 (emit emissions allocation schema)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedFrame231 (capture)
open GeneralNominalVersionedPlans231 (variables)
open GeneralDeclarationDemands (outputTarget)
open GeneralNominalMaterialization (Request rootRequests)
open GeneralNominalCenteredHeadMatSchemas (emissionRequests generated_equation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value translate_complete)
open GeneralDeclarativeRawCapture344 (rawCap operands)
open GeneralDeclarativeRawReplayArgs344 (names)
open GeneralDeclarativeCommitModes344 (emitted_mem)
open GeneralDeclarativeCommitCoverage344 (used)
open GeneralDeclarativeNormalizedPort344 (translate_at)
open GeneralDeclarativePolarCompiler344 (normalized_codes)
open GeneralDeclarativeModeCongruence344 (expression)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralDeclarativeWhereOutputBatch327 (entry alreadyNamed whole)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeSourceEmission322 (useOutput)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

def request (p : Plan rs) (cl : Clause) (eq : GeneralDeclarations.Equation) : Request :=
  ⟨eq.rhs,outputTarget p.packet.declaration (capture p.packet) (allocation p cl).outputs eq,.actual⟩

theorem exists_request (p : Plan rs) (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (eq : GeneralDeclarations.Equation) (there : eq ∈ cl.outputs) :
    request p cl eq ∈ rootRequests p.packet.declaration p.packet.site.occurrence ++
      (emissions p).flatMap emissionRequests := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨emit p cl sig,emitted_mem p cl inside sig,?_⟩
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨⟨eq.id,eq.name,eq.rhs,outputTarget p.packet.declaration (capture p.packet)
    (allocation p cl).outputs eq⟩,?_ ,rfl⟩
  exact List.mem_map.mpr ⟨eq,there,rfl⟩

theorem exact_associated (p : Plan rs) (m : Assignment) (fit : GeneralWhereVersionSemantics317.Holds p m)
    (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements) (eq : GeneralDeclarations.Equation)
    (there : eq ∈ cl.outputs) :
    ∃ rows, entry p.packet.registry p.packet.context.interpretation p.packet.declaration
      (names p) (allocation p cl).outputs eq = some rows ∧
      ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  let sig := p.packet.checked.signature.2.2.2 cl inside
  have listed := exists_request p cl inside sig eq there
  obtain ⟨raw,actual⟩ := translate_at fit.materialized listed
  have rawCode : translate p.packet.registry.constructors p.packet.context.interpretation eq.rhs = some raw := actual
  obtain ⟨canon,printed⟩ := translate_complete (normalize_covered (used eq.rhs rawCode))
  let row : Equation := ⟨(request p cl eq).target,logical (rawCap p) .actual canon⟩
  have rawValue := generated_equation fit.rows listed actual
  have later := eqv_trans rawValue (normalized_codes (variables := variables p m) rawCode printed .actual)
  have final := eqv_trans later (expression _ _ .actual canon (operands p m .actual canon))
  have checked : GeneralDeclarativeEntailment320.Holds m row := by
    change CommonNominalFullCarrier.Equivalent (m (request p cl eq).target).1
      (value (GeneralDeclarativeHead320.environment m) .actual (logical (rawCap p) .actual canon))
    rw [logical_value]
    exact final
  by_cases already : alreadyNamed p.packet.declaration eq = true
  · exact ⟨[],by simp [entry,printed,already],by intro _ impossible; cases impossible⟩
  · refine ⟨[row],?_,?_⟩
    · simp [entry,printed,already,row,request,names,useOutput,GeneralDeclarativeSourceEmission322.Names.old,outputTarget]
    · intro e used
      cases List.mem_singleton.mp used
      exact checked

theorem collect_checked {α : Type} (f : α → Option (List Equation)) (xs : List α) (m : Assignment)
    (all : ∀ x ∈ xs, ∃ rows, f x = some rows ∧
      ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row) :
    ∃ rows, collect f xs = some rows ∧ ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  induction xs with
  | nil => exact ⟨[],rfl,by intro _ no; cases no⟩
  | cons hd tl ih =>
    obtain ⟨first,one,truth₁⟩ := all hd List.mem_cons_self
    obtain ⟨last,two,truth₂⟩ := ih (fun x h => all x (List.mem_cons_of_mem _ h))
    exact ⟨first++last,by simp [collect,one,two],fun row found =>
      (List.mem_append.mp found).elim (truth₁ row) (truth₂ row)⟩

/-- The real ordinary associated-output pass for all where clauses
can be read back in the *same* raw model. Direct already-named
writes keep the existing omission rule; no new target is chosen. -/
theorem output_batch (p : Plan rs) (m : Assignment)
    (fit : GeneralWhereVersionSemantics317.Holds p m) :
    ∃ rows, whole p.packet.registry p.packet.context.interpretation p.packet.declaration
      (names p) (fun cl => (allocation p cl).outputs) = some rows ∧
      ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  unfold whole
  apply collect_checked
  intro cl inside
  apply collect_checked
  intro eq there
  exact exact_associated p m fit cl inside eq there

end Yulang.GeneralDeclarativeAssociatedReplay344
