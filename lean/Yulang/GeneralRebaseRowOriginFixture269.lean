import Yulang.GeneralRebaseTypedNominalWindow269
import Yulang.GeneralNominalProgressObstruction
import Yulang.GeneralRebaseOriginExecutable269

namespace Yulang.GeneralRebaseRowOriginFixture269
open GeneralNominalProgressObstruction (base view root)
open GeneralRebaseNominalOrigin269 (Raw)
open GeneralNominalVersionedJournal232 (initial Models)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseOriginCycles268 (Window)
open GeneralRebasePartialBool268 (Reflect)
open CommonNominalFullCarrier

abbrev d : GeneralNominalState.Descriptor 1 := ⟨0,⟨[.row],0⟩,[.row (0,0)],rfl⟩

abbrev raw : GeneralNominalState.State where
 base := base
 view := view
 constructors := fun i => if i = 0 then some d.declaration else none
 nominals := fun _ => some d
 catalogue := by intro _ other located; cases Option.some.inj located; rfl
 bodies_opaque := by intros; rfl

def assignment : GeneralNominalCommonBridge.Assignment :=
 fun _ => (nominal 0 [.inr Common.rowEmpty],Common.rowEmpty)

theorem raw_model : GeneralNominalState.Models raw assignment := by
 refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro _ member; cases member
 · intro _ _ located; cases located
 · intro pair member
   cases List.mem_singleton.mp member
   exact subtype_refl _
 · intro _ descriptor seen
   cases Option.some.inj seen
   exact ⟨[.inr Common.rowEmpty],.cons ⟨Common.rowLe_refl _,Common.rowLe_refl _⟩ .nil,
     subtype_refl _,subtype_refl _⟩

abbrev context : GeneralNominalCandidates.Context := ⟨raw,GeneralNominalExamples.interpretation⟩
abbrev journal := initial context (root 0)

theorem whole_model : Models journal assignment :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨raw_model,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

def points (_ : Fin 1) : Fin (Raw journal).base.slots := ⟨0,by decide +kernel⟩

theorem coverage : GeneralRebaseNominalWindow269.check journal points = true := by decide +kernel

def window : Window 1 := GeneralRebaseTypedNominalWindow269.window journal points (fun _ _ => none)

def matchOrigin (_ : Origin) (_ : Fin 1) : Option Bool := some true

theorem graph_empty : window.probe 0 0 = some false := by decide +kernel

theorem query : GeneralRebaseOriginExecutable269.cyclic window matchOrigin
 (fun _ => true) (fun _ => false) (.source 0) = some false := by decide +kernel

/-- A present descriptor with only row positions cannot produce a type
Origin edge. Negative recurrence is computed with no semantic Equals. -/
theorem no_cycle : ¬ Cyclic journal (.source 0) := by
 have ok := GeneralRebaseTypedNominalWindow269.window_sound journal points (fun _ _ => none)
   (fun _ _ => True.intro) ⟨assignment,whole_model⟩
 have forward := GeneralRebaseTypedNominalWindow269.typed_forward journal points
   (fun _ _ => none) coverage ⟨assignment,whole_model⟩
 have matched : ∀ i, Reflect (GeneralNominalVersionedCycles232.Equal journal (.source 0) (window.point i))
   (matchOrigin (.source 0) i) := fun _ m _ => GeneralNominalOriginTerms.source_self m 0
 have h := GeneralRebaseOriginExecutable269.with_semantic_closure window ok matchOrigin matched forward
 rw [query] at h
 exact h

end Yulang.GeneralRebaseRowOriginFixture269
