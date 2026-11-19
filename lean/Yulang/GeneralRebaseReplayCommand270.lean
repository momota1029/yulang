import Yulang.GeneralRebaseCertifiedObserver266

namespace Yulang.GeneralRebaseReplayCommand270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step Administrative Installable Equal)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalCandidates (Context)
open GeneralNominalState (Linked Known sources)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalReobservationSteps (Revision Improves)
open GeneralNominalVersionedMixedObservations233 (Refresh Reobserve)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedAdministrative232 (enqueue equate merge)
open GeneralNominalVersionedRefresh232 (refresh reobserve)
open GeneralNominalFeedbackSteps (RawEqual)
open GeneralRebaseCertifiedObserver266 (Edge)

/-- An executable payload with Lean-checked guards. No untrusted bit is a
semantic proof, and a caller cannot furnish an unrelated after journal. -/
inductive Command (registry : Registry) (root : Occurrence roles) (before : State roles) where
 | enqueue (focus : Occurrence roles) :
   Generated before.core.erased.current root focus →
   Linked before.core.erased.current.context.state focus.demand →
   (∀ s ∈ before.core.erased.current.sites, s.occurrence ≠ focus) → Command registry root before
 | refresh (focus : Occurrence roles) (context : Context) (source : Nat) :
   Generated before.core.erased.current root focus → Refresh before context →
   source ∈ sources before.core.erased.current.context.state →
   ¬ Known before.core.erased.current.context.state source → Known context.state source → Command registry root before
 | equate (focus : Occurrence roles) (a b : Nat) :
   Generated before.core.erased.current root focus →
   a ∈ sources before.core.erased.current.context.state →
   b ∈ sources before.core.erased.current.context.state →
   Equal before a b → ¬ RawEqual before.core.erased.current a b → Command registry root before
 | reobserve (focus : Occurrence roles) (revision : Revision before.core.erased.current) :
   Generated before.core.erased.current root focus → Reobserve before revision → Improves revision →
   Command registry root before
 | install (effect : Effect roles) :
   Generated before.core.erased.current root effect.plan.packet.site.occurrence →
   Installable registry before effect → ¬ Committed before effect.plan → Command registry root before
 | merge (first last : Site roles) :
   Generated before.core.erased.current root first.occurrence →
   first ∈ before.core.sites → last ∈ before.core.sites →
   SameInputs (Models before) first last →
   ¬ Alias before.core.erased.current first.occurrence.identity last.occurrence.identity → Command registry root before

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
 {before after : State roles}

def run (cmd : Command registry root before) : State roles :=
 match cmd with
 | .enqueue focus .. => enqueue before focus
 | .refresh _ ctx .. => refresh before ctx
 | .equate _ a b .. => equate before a b
 | .reobserve _ revision .. => reobserve before revision
 | .install effect .. => install before effect
 | .merge first last .. => merge before first last

theorem run_sound (cmd : Command registry root before) : Step registry root before (run cmd) := by
 cases cmd with
 | enqueue focus seen linked fresh =>
   exact ⟨focus,seen,.administrative (.enqueue focus linked fresh)⟩
 | refresh focus context source seen refreshOK listed absent known =>
   exact ⟨focus,seen,.refresh focus context refreshOK source listed absent known⟩
 | equate focus a b seen one two eq missing =>
   exact ⟨focus,seen,.administrative (.equate focus a b one two eq missing)⟩
 | reobserve focus rev seen observes improve =>
   exact ⟨focus,seen,.administrative (.reobserve focus rev observes improve)⟩
 | install effect seen enabled novelty =>
   exact ⟨effect.plan.packet.site.occurrence,seen,.install effect enabled novelty⟩
 | merge first last seen one two same nontrivial =>
   exact ⟨first.occurrence,seen,.merge first last one two same nontrivial⟩

theorem supported (step : Step registry root before after) :
 ∃ cmd : Command registry root before, run cmd = after := by
 obtain ⟨focus,seen,action⟩ := step
 cases action with
 | administrative admin =>
   cases admin with
   | enqueue linked fresh => exact ⟨.enqueue focus seen linked fresh,rfl⟩
   | refresh context good source listed unknown known =>
     exact ⟨.refresh focus context source seen good listed unknown known,rfl⟩
   | equate a b one two equal novel =>
     exact ⟨.equate focus a b seen one two equal novel,rfl⟩
   | reobserve revision valid improves =>
     exact ⟨.reobserve focus revision seen valid improves,rfl⟩
 | refresh focus context good source listed unknown known =>
   exact ⟨.refresh focus context source seen good listed unknown known,rfl⟩
 | install effect enabled novel =>
   exact ⟨.install effect seen enabled novel,rfl⟩
 | merge first last one two equal novel =>
   exact ⟨.merge first last seen one two equal novel,rfl⟩

def edge (cmd : Command registry root before) : Edge registry root :=
 ⟨before,run cmd,run_sound cmd⟩

end Yulang.GeneralRebaseReplayCommand270
