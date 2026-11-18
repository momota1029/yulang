import Yulang.GeneralRebaseOutputDecoder260
namespace Yulang.GeneralOutputRebaseSource260
open GeneralRebaseStep258
open GeneralDictionaryOutputDepth252

/-- The first two binding-obligation indices are captures; index2 is the
actual associated-output equation. None of these indices allocates a name. -/
def facts : List Fact := [.installed 0,.lower 0 0,.upper 0 0,.binder 0,.binder 1,.binder 2]
def atom (slot : Fin snapshot.base.slots) : Option Nat := if slot = 2 then some 0 else none
abbrev schema := GeneralNominalVersionedPlans231.emittedSchema plan

theorem schema_exact : schema = ⟨[⟨3,.actual,rhs⟩],false⟩ := emitted_exact

theorem capture_exact : GeneralRebaseFiniteReport259.compile 0 atom (GeneralNominalPacketSupport.report packet) =
 some [.installed 0,.lower 0 0,.upper 0 0,.binder 0,.binder 1] := by
 change GeneralRebaseFiniteReport259.compile 0 atom
  (GeneralNominalRecursiveCandidates.report context declaration [(2,2)]) = _
 rw [report_exact]
 rfl

theorem output_keys : GeneralRebaseOutputKeys260.keys 2 schema = [.binder 2] := by
 rw [schema_exact]
 rfl

def proposal := GeneralRebaseOutputDecoder260.compile plan 0 atom

theorem proposal_exact : proposal = .ok facts := by
 apply (GeneralRebaseOutputDecoder260.successful ..).mpr
 refine ⟨?_,_,capture_exact,?_⟩
 · rw [emitted_exact]
 · change facts = [.installed 0,.lower 0 0,.upper 0 0,.binder 0,.binder 1] ++ GeneralRebaseOutputKeys260.keys 2 schema
   rw [output_keys]; rfl

abbrev initialState := GeneralRebaseStep258.initial facts
abbrev finalState := done facts

def observe : Observer facts := fun _ => match proposal with
 | .error _ => []
 | .ok value => [value]

theorem observe_exact : observe = fun _ => [facts] := by
 funext state
 simp only [observe,proposal_exact]

theorem closed : GeneralRebaseClosedObserver259.Closed observe := by
 intro state value member
 have same : value = facts := by simpa only [observe_exact,List.mem_singleton] using member
 subst value
 exact List.Subset.refl _

theorem write_initial : write initialState facts = finalState := by apply state_ext; decide

theorem first : Step observe initialState finalState :=
 ⟨facts,by simp [observe_exact],write_initial.symm,by decide⟩

theorem stop (after : State facts) : ¬ Step observe finalState after := by
 rintro ⟨value,_,equal,changed⟩
 apply changed
 rw [equal]
 rfl

theorem terminating (state : State facts) : Acc (fun after before => Step observe before after) state :=
 accessible _ _
end Yulang.GeneralOutputRebaseSource260
