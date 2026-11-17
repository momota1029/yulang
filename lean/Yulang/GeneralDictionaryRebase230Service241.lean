import Yulang.GeneralDictionaryRebase230Private241
import Yulang.GeneralNominalRebaseMachine241
set_option backward.isDefEq.respectTransparency false
/-! A concrete one-service run in the finite rebase machine. The original 230
raw source, actual center and public constraints survive. This is not a path
in an already completed Yulang source boundary. -/
namespace Yulang.GeneralDictionaryRebase230Service241
open GeneralDictionaryRebase230Private241
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryOptionalInstall229 (model actual)
open GeneralNominalRebaseStore241 (Owner)
open GeneralNominalRebaseMachine241
abbrev owner : Owner := (root.identity,declaration.id)
def ownerAt (_ : Fin 1) : Owner := owner
abbrev oldBlock := GeneralNominalAllocation.merges snapshot registry root.identity declaration oldBindings
abbrev newBlock := GeneralNominalAllocation.merges snapshot registry root.identity declaration newBindings

def initial : State 0 1 where
 work := ⟨fun index => Fin.elim0 index,fun _ => true⟩
 table := ⟨publicAtoms,[owner],fun _ => oldBlock⟩
def final : State 0 1 := service ownerAt initial 0 newBlock

theorem step : Step ownerAt initial final := .service initial 0 newBlock rfl

theorem initial_models : GeneralNominalRebaseStore241.Models
 initial.table.baseAtoms initial.table.owners initial.table.blocks model := by
 refine ⟨old_public,?_⟩
 intro key member
 exact old_merges

theorem final_models : GeneralNominalRebaseStore241.Models
 final.table.baseAtoms final.table.owners final.table.blocks rebased := by
 refine ⟨retained_public,?_⟩
 intro key member
 cases List.mem_singleton.mp member
 simpa only [final,service,GeneralNominalRebaseStore241.rebase,
   ownerAt,GeneralNominalRebaseStore241.replace_at] using new_merges

theorem final_raw : GeneralNominalState.Models snapshot rebased := raw_models

theorem final_actual : (rebased actual) = model actual := agrees _ (by simp [pool])

theorem final_capture : GeneralNominalRebaseProjection241.CapturedFits snapshot registry root.identity
 declaration newBindings (fun _ => actual) rebased := actual_fits

theorem stopped : ¬ ∃ next, Step ownerAt final next := by
 rintro ⟨next,action⟩
 cases action with
 | learn work retained newFact =>
   obtain ⟨index,_⟩ := newFact
   exact Fin.elim0 index
 | service index block pending =>
   have zero : index = 0 := by apply Fin.ext; omega
   subst index
   change (if (0 : Fin 1) = 0 then false else true) = true at pending
   simp at pending

theorem rank_initial : GeneralNominalRebaseProgress241.rank initial.work = 1 := rfl
theorem rank_final : GeneralNominalRebaseProgress241.rank final.work = 0 := rfl

theorem rejects_old_block : ¬ PresenceNormalForm.All CommonNominalFullCarrier.model rebased oldBlock := rejects_stale
end Yulang.GeneralDictionaryRebase230Service241
