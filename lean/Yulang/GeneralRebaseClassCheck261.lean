import Yulang.GeneralRebaseClassTable261
namespace Yulang.GeneralRebaseClassCheck261
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralDictionaryAssociatedProvenance

inductive Failure where
 | missing (requests : List Output)
 | untranslated (requests : List Output)

def missing (plan : Plan roles) (outputs : List Output) :=
 outputs.filter fun output => (lookup roles plan.packet.declaration output.name).isNone

def untranslated (plan : Plan roles) (outputs : List Output) :=
 outputs.filter fun output => (GeneralRebaseBodyTable261.schema plan output).unknown

def Ready (plan : Plan roles) (outputs : List Output) : Prop :=
 ∀ output ∈ outputs, (GeneralRebaseBodyTable261.schema plan output).unknown = false

def check (plan : Plan roles) (outputs : List Output) : Except Failure Unit :=
 if (missing plan outputs).isEmpty then
   if (untranslated plan outputs).isEmpty then .ok () else .error (.untranslated (untranslated plan outputs))
 else .error (.missing (missing plan outputs))

theorem untranslated_empty (plan : Plan roles) (outputs : List Output) :
 (untranslated plan outputs).isEmpty = true ↔ Ready plan outputs := by
 simp [untranslated,Ready,List.isEmpty_iff,List.filter_eq_nil_iff]

theorem missing_empty (plan : Plan roles) (outputs : List Output) (ready : Ready plan outputs) :
 (missing plan outputs).isEmpty = true := by
 apply List.isEmpty_iff.mpr
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output member
 obtain ⟨included,absent⟩ := List.mem_filter.mp member
 obtain ⟨body,found,_⟩ := (GeneralRebaseBodyTable261.translated plan output).mp (ready output included)
 simp [found] at absent

theorem check_exact (plan : Plan roles) (outputs : List Output) : check plan outputs = .ok () ↔ Ready plan outputs := by
 constructor
 · intro valid
   unfold check at valid
   split at valid
   · split at valid
     · rename_i known; exact (untranslated_empty ..).mp known
     · cases valid
   · cases valid
 · intro ready
   simp only [check,missing_empty plan outputs ready,(untranslated_empty ..).mpr ready,↓reduceIte]

theorem ready_meaning (plan : Plan roles) (outputs : List Output) :
 Ready plan outputs ↔ ∀ output ∈ outputs, ∃ body,
 lookup roles plan.packet.declaration output.name = some body ∧
 (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body).unknown = false := by
 unfold Ready
 simp only [GeneralRebaseBodyTable261.translated]

theorem actual_ready (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) :
 check plan (GeneralNominalCenteredHeadOutputs.requests state root) = .ok () ↔
 GeneralNominalCenteredHeadMatEffects.Ready state root plan :=
 (check_exact ..).trans (ready_meaning ..)

theorem missing_error (plan : Plan roles) (outputs : List Output) (absent : (missing plan outputs).isEmpty = false) :
 check plan outputs = .error (.missing (missing plan outputs)) := by simp [check,absent]

theorem untranslated_error (plan : Plan roles) (outputs : List Output)
 (present : (missing plan outputs).isEmpty = true) (unknown : (untranslated plan outputs).isEmpty = false) :
 check plan outputs = .error (.untranslated (untranslated plan outputs)) := by simp [check,present,unknown]
end Yulang.GeneralRebaseClassCheck261
