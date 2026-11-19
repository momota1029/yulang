import Yulang.GeneralRebaseProspectiveFixture264
import Yulang.GeneralRebaseSourceInstallProjection264
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Yulang.GeneralRebaseSourceStrictFixture265
noncomputable section
open GeneralRebaseStep258
open GeneralDictionaryCompoundFrame238 (before effect installed)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryCompoundSource238 (sourceRegistry checked)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralRebaseMultiSelection263 (ofPlan proposal)
open GeneralRebaseLiveProjection264 (project)

def owner := (ofPlan plan).owner
def owners := [owner]
def output : GeneralSourceState.Output := ⟨0,4⟩
def pool := [output]
def proposed := proposal before.core (ofPlan plan)
def witness := GeneralRebaseUniversalBasis263.bodyKey owner output
abbrev first := project owners pool before
abbrev last := project owners pool installed

theorem witness_in_basis : witness ∈ GeneralRebaseUniversalBasis263.basis owners pool := by decide +kernel

theorem witness_proposed : witness ∈ proposed := by decide +kernel

theorem initial_projection : first = initial (GeneralRebaseUniversalBasis263.basis owners pool) := by
 change write (initial _) [] = initial _
 exact GeneralRebaseWriteAlgebra259.empty _

theorem square : last = write first proposed := by
 have enabled := GeneralNominalVersionedMixedCurrentCandidate235.source_installable
   GeneralRebaseProspectiveFixture264.current GeneralDictionaryCompoundStep238.initial_reachable
   GeneralRebaseProspectiveFixture264.selected
 exact GeneralRebaseSourceInstallProjection264.project_install_current sourceRegistry ⟨rfl,checked⟩ root before
   GeneralDictionaryCompoundStep238.initial_reachable effect enabled owners pool

theorem strict : last ≠ first := by
 intro equal
 have retained : witness ∈ first.remaining := by rw [initial_projection]; exact witness_in_basis
 have missing : witness ∉ last.remaining := by
  rw [square]
  intro member
  have excluded := (List.mem_filter.mp member).2
  simp [witness_proposed] at excluded
 have member : witness ∈ last.remaining := equal.symm ▸ retained
 exact missing member

/-- A genuine source-initial installation and a strict finite write agree.
The one-proposal observer is a concrete fixture, not a general discovery engine. -/
theorem source_and_finite :
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root before installed ∧
 GeneralRebaseStep258.Step (fun _ => [proposed]) first last ∧
 (∃ model, GeneralNominalVersionedJournal232.Models installed model) := by
 refine ⟨GeneralRebaseProspectiveFixture264.nonempty_install.2.1,?_,GeneralRebaseProspectiveFixture264.nonempty_install.2.2.1⟩
 refine ⟨proposed,List.mem_singleton_self _,square,?_⟩
 exact fun equal => strict (state_ext _ _ equal)
end
end Yulang.GeneralRebaseSourceStrictFixture265
