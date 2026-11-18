import Yulang.GeneralNominalPostInstall250
/-! A new packet-style equality reads the NEW private value. Moving that
metadata before refresh changes the result. This is a finite-frame regression,
not a claim about parser-to-source reachability or full language acceptance. -/
namespace Yulang.GeneralNominalPostInstallRegression250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalJournalAppend250 (Delta attach)
open GeneralNominalPersistentOwner250 (update)
open CommonNominalFullCarrier

def emptyView : GeneralNominalRebaseRawView243.View := ⟨0,Fin.elim0,[],Fin.elim0,[],Fin.elim0⟩
def emptyJournal : GeneralNominalRebaseJournalView243.Journal := ⟨emptyView,emptyView,[],[],[],[]⟩
def frame : Frame := ⟨emptyJournal,[],[(2,.exactEmpty)]⟩
def raw : List (Entry Nat) := [(2,.var 0)]
def extra : Delta := ⟨[],[],[],[],equations 2 (.var 0)⟩
def boundary : Assignment := fun _ => (.emptyRecord,Common.rowEmpty)

theorem empty_view_models (assignment : Assignment) : emptyView.Models assignment := by
 refine ⟨?_,?_,?_,?_⟩
 · intro atom member; cases member
 · intro index; exact Fin.elim0 index
 · intro pair member; cases member
 · intro index; exact Fin.elim0 index

theorem empty_journal_models (assignment : Assignment) : emptyJournal.Models assignment :=
 ⟨empty_view_models assignment,empty_view_models assignment,
   (by intro _ member; cases member),(by intro _ member; cases member),
   (by intro _ member; cases member),(by intro _ member; cases member)⟩

theorem old_safe : SafeOrder frame.definitions := by
 simp [frame,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem ordinary_satisfied : extra.Holds boundary := by
 refine ⟨(by intro _ member; cases member),(by intro _ member; cases member),
   (by intro _ member; cases member),(by intro _ member; cases member),?_⟩
 intro atom member
 simp only [extra,equations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl <;> exact subtype_refl _

theorem post_has_model : Models (attach (update frame raw) extra) boundary := by
 apply (GeneralNominalJournalAppend250.attach_models _ _ _).mpr
 refine ⟨⟨?_,?_⟩,ordinary_satisfied⟩
 · apply (GeneralNominalJournalSubst249.ordered_exact frame.definitions boundary emptyJournal).mpr
   exact empty_journal_models _
 · intro atom member
   change atom ∈ equations 2 (.var 0) at member
   simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl <;> exact subtype_refl _

theorem pre_has_no_public_model :
 ¬ ∃ assignment, Models (attach frame extra) assignment ∧ assignment 0 = boundary 0 := by
 rintro ⟨assignment,valid,agreement⟩
 obtain ⟨old,extraValid⟩ := (GeneralNominalJournalAppend250.attach_models _ _ _).mp valid
 have newToOld : Subtype (assignment 0).1 (assignment 2).1 :=
   extraValid.2.2.2.2 (.tyLe (.var 0) (.var 2)) (by simp [extra,equations])
 have oldToEmpty : Subtype (assignment 2).1 model.exactEmpty :=
   old.2 (.tyLe (.var 2) .exactEmpty) (by simp [frame,block,equations])
 have impossible := subtype_trans newToOld oldToEmpty
 rw [agreement] at impossible
 exact width_not_below_exactEmpty impossible
end Yulang.GeneralNominalPostInstallRegression250
