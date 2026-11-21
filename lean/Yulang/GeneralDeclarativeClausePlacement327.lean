import Yulang.GeneralDeclarativeClauseBatch327
import Yulang.GeneralDeclarativeFrameReadback325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeClausePlacement327
open GeneralDeclarations (Clause Declaration DeclarationChecked Registry)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeClauseBatch327 (Port Input prepare read_order)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeFrameReadback325 (ClauseFrame)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open CommonRoleOutermostResolver (All₂)
variable {r : Registry} {names : Names}

def portAt (cs : List Clause) (ports : List Port) (cl : Clause) : Option Port :=
  ((cs.zip ports).find? (fun x => x.1.id == cl.id)).map Prod.snd

def placement (cs : List Clause) (ports : List Port) (targets : Clause → Nat → Nat) : Placement :=
  ⟨fun cl j => ((portAt cs ports cl).map (fun p => p.input j)).getD ⟨0,0,0⟩,targets⟩

theorem located {relation : Clause → Port → Prop} (aligned : All₂ relation cs ports)
    (unique : (cs.map Clause.id).Nodup) (there : cl ∈ cs) :
    ∃ port, portAt cs ports cl = some port ∧ relation cl port := by
  induction aligned with
  | nil => cases there
  | @cons first port cs ports start tail ih =>
    rcases List.mem_cons.mp there with rfl|more
    · exact ⟨port,by simp [portAt],start⟩
    · obtain ⟨different,rest⟩ := List.nodup_cons.mp unique
      have separated : first.id ≠ cl.id := fun same => different (same.symm ▸ List.mem_map.mpr ⟨cl,more,rfl⟩)
      obtain ⟨found,elected,read⟩ := ih rest more
      exact ⟨found,by simpa [portAt,separated] using elected,read⟩

/-- In a successful ordered batch, a genuine clause id fixes its
fresh input port exactly. Unused fallback is unreachable at every
required clause; no certificate is demanded of a bare binder. -/
theorem checked_inputs {s t : State}
    (which : DeclarationChecked r.constructors r.roles impl)
    (actual : prepare r.constructors i protect names.input s impl.requirements = some (t,ports))
    (needed : cl ∈ impl.requirements) :
    ∃ port, portAt impl.requirements ports cl = some port ∧
      Input t r.constructors i names.input cl port ∧
      ∀ j, (placement impl.requirements ports targets).compound cl j = port.input j := by
  obtain ⟨port,located,known⟩ := located (read_order actual).2 which.identified.1 needed
  exact ⟨port,located,known,fun j => by simp [placement,located]⟩

theorem frame_from_inputs {s t : State}
    (which : DeclarationChecked r.constructors r.roles impl)
    (actual : prepare r.constructors i protect names.input s impl.requirements = some (t,ports))
    (needed : cl ∈ impl.requirements)
    (outputs : ∀ eq ∈ cl.outputs, ∃ e, translate r.constructors i (normalize eq.rhs) = some e ∧
      (¬Direct impl eq → Origin t (useOutput impl names (targets cl) eq).target
        (logical names.input .actual e))) :
    ClauseFrame t r i impl cl names (placement impl.requirements ports targets) := by
  obtain ⟨port,_,known,exactPlacement⟩ := checked_inputs (targets := targets) which actual needed
  refine ⟨⟨port.code,known.1,?_⟩,outputs⟩
  intro pos p e seen decoded compound
  rw [exactPlacement]
  exact (known.2 pos p e seen decoded compound).2

end Yulang.GeneralDeclarativeClausePlacement327
