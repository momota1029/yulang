import Yulang.GeneralDeclarativeAssociatedReplay344
import Yulang.GeneralDeclarativeNormalizeAssoc324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRootReplay344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralWhereVersionInstall317 (Journal)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralDeclarativeStoppedPaired341 (activeDemand)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture positional compile_exact)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeCommitCoverage344 (used)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralDeclarativePolarCompiler344 (normalized_codes)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value translate_complete)
open GeneralNominalCenteredHeadMatEffects (Ready bodySchema compileBody defaultVariables)
open GeneralNominalVersionedEffects231 (ClassEffects BodyHolds bodyVariables actual_value)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadOutputs (requests)

noncomputable def actualDemand (p : Plan rs) (j : Journal rs) :=
  activeDemand j.mixed p.input

theorem requests_exact (p : Plan rs) (j : Journal rs) :
    (actualDemand p j).outputs = requests j.mixed.core p.packet.site.occurrence := by
  unfold actualDemand activeDemand
  simp only [p.input_exact]

theorem default_exact (p : Plan rs) (j : Journal rs) (m : Assignment) (idx : Nat) :
    defaultVariables p m .actual idx =
      GeneralDeclarativeWhere319.variables (positional (actualDemand p j)) m .actual idx := by
  unfold defaultVariables GeneralDeclarativeWhere319.variables positional actualDemand activeDemand demand
  simp only [List.getElem?_ofFn]
  split <;> rfl

theorem same_actual (p : Plan rs) (j : Journal rs) (m : Assignment) (body : Body) (idx : Nat) :
    bodyVariables p m body .actual idx =
      GeneralDeclarativeWhere319.variables (bodyCapture (actualDemand p j) (rawCap p) body) m .actual idx := by
  cases body with
  | explicit eq =>
    exact (GeneralNominalVersionedExpressionFrame236.variable_value p m .actual idx).trans rfl
  | default role name term => exact default_exact p j m idx

/-- Reads the actual ordered class demand and a real completed output
schema. A missing body or unsupported translation is not treated as
an empty successful body. Defaults read the registered actual centers. -/
theorem output (p : Plan rs) (j : Journal rs) (m : Assignment)
    (sameRoles : p.packet.registry.roles = rs)
    (ready : Ready j.mixed.core p.packet.site.occurrence p)
    (effects : ClassEffects j.mixed.core p.packet.site.occurrence p m)
    (out : GeneralSourceState.Output) (wanted : out ∈ (actualDemand p j).outputs) :
    ∃ row, one p.packet.registry p.packet.context.interpretation p.packet.declaration
      (actualDemand p j) (rawCap p) out = some [row] ∧ row.left = out.target ∧
      GeneralDeclarativeEntailment320.Holds m row := by
  have live : out ∈ requests j.mixed.core p.packet.site.occurrence := (requests_exact p j) ▸ wanted
  obtain ⟨body,look,complete⟩ := ready out live
  have compiled : ∃ raw, compileBody p body = some raw := by
    cases e : compileBody p body with
    | some term => exact ⟨term,rfl⟩
    | none => simp [bodySchema,e] at complete
  obtain ⟨raw,ran⟩ := compiled
  have rawPrinted : translate p.packet.registry.constructors p.packet.context.interpretation (bodyPattern body) = some raw := by
    refine (compile_exact p.packet.registry.constructors p.packet.context.interpretation body).trans ?_
    cases body <;> exact ran
  obtain ⟨canon,normalized⟩ := translate_complete (normalize_covered (used _ rawPrinted))
  have facts := effects.1 out live body look
  unfold BodyHolds at facts
  rw [show bodySchema p out.target body = ⟨[⟨out.target,.actual,raw⟩],false⟩ by simp [bodySchema,ran]] at facts
  have rawEq : CommonNominalFullCarrier.Equivalent (m out.target).1
      (value (bodyVariables p m body) .actual raw) := facts _ List.mem_cons_self
  have ordinary := eqv_trans rawEq (normalized_codes rawPrinted normalized .actual)
  have atTarget := actual_value (bodyVariables p m body)
    (GeneralDeclarativeWhere319.variables (bodyCapture (actualDemand p j) (rawCap p) body) m)
    (same_actual p j m body) canon
  let row : Equation := ⟨out.target,logical (bodyCapture (actualDemand p j) (rawCap p) body) .actual canon⟩
  refine ⟨row,?_,rfl,?_⟩
  · unfold one
    rw [sameRoles,look]
    simp [normalized,row]
  · change CommonNominalFullCarrier.Equivalent (m out.target).1
      (value (GeneralDeclarativeHead320.environment m) .actual row.right)
    unfold row
    rw [logical_value]
    rwa [atTarget] at ordinary

theorem batch (p : Plan rs) (j : Journal rs) (m : Assignment)
    (sameRoles : p.packet.registry.roles = rs)
    (ready : Ready j.mixed.core p.packet.site.occurrence p)
    (effects : ClassEffects j.mixed.core p.packet.site.occurrence p m) :
    ∃ rows, GeneralDeclarativeBatch320.collect
      (one p.packet.registry p.packet.context.interpretation p.packet.declaration (actualDemand p j) (rawCap p))
      (actualDemand p j).outputs = some rows ∧
      rows.map Equation.left = (actualDemand p j).outputs.map GeneralSourceState.Output.target ∧
      ∀ row ∈ rows, GeneralDeclarativeEntailment320.Holds m row := by
  generalize eq : (actualDemand p j).outputs = assigned
  have checked : ∀ out ∈ assigned, ∃ row,
      one p.packet.registry p.packet.context.interpretation p.packet.declaration
        (actualDemand p j) (rawCap p) out = some [row] ∧ row.left = out.target ∧
        GeneralDeclarativeEntailment320.Holds m row := by
    intro out found
    exact output p j m sameRoles ready effects out (eq.symm ▸ found)
  clear eq
  induction assigned with
  | nil => exact ⟨[],rfl,rfl,by intro _ no; cases no⟩
  | cons out rest ih =>
    obtain ⟨first,printed,target,typed⟩ := checked out List.mem_cons_self
    obtain ⟨rows,tail,targets,valid⟩ := ih (fun o h => checked o (List.mem_cons_of_mem _ h))
    refine ⟨first::rows,by simp [GeneralDeclarativeBatch320.collect,printed,tail],?_,?_⟩
    · simp only [List.map_cons,target,targets]
    · intro row chosen
      rcases List.mem_cons.mp chosen with same|later
      · exact same ▸ typed
      · exact valid row later

end Yulang.GeneralDeclarativeRootReplay344
