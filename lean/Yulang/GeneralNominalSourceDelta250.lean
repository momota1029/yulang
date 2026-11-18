import Yulang.GeneralNominalPersistentOwner250
import Yulang.GeneralNominalSourceOwnerFrame249
/-! Actual source observations, plans and effects compile into added finite
metadata. The theorem keeps their obligations on the same source assignment;
it neither assumes satisfiability nor synthesizes eligible source steps. -/
namespace Yulang.GeneralNominalSourceDelta250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalJournalAppend250 (Delta attach subst)
open GeneralNominalMaterializedOwnerFrame249 (Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalSourceOwnerFrame249 (sourceFrame)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedPrepared247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralNominalRebaseRawView243 (read)
open CommonNominalFullCarrier

structure SourceDelta (roles : Roles.RoleDecls) where
 observed : List (GeneralNominalDemandMerging.Site roles)
 sites : List (GeneralNominalCenters.Site roles)
 plans : List (GeneralNominalCenters.Plan roles)
 effects : List (GeneralNominalVersionedJournal232.Effect roles)
 ordinary : List (Atom Nat)

def SourceDelta.Holds (state : State roles) (delta : SourceDelta roles) (assignment : Assignment) : Prop :=
 (∀ site ∈ delta.observed, GeneralNominalSaturationState.SiteHolds site assignment) ∧
 (∀ site ∈ delta.sites, site.Holds assignment) ∧
 (∀ plan ∈ delta.plans, GeneralNominalVersionedPlans231.Holds plan assignment) ∧
 (∀ effect ∈ delta.effects, effect.Holds assignment ∧ effect.Live state.core assignment) ∧
 All model assignment delta.ordinary

noncomputable def compile (state : State roles) (delta : SourceDelta roles) (mapping : Nat → CompTerm Nat) : Delta :=
 ⟨delta.observed.map (GeneralNominalRebaseObservedSite243.compile · mapping),
 delta.sites.map (GeneralNominalRebaseLiveView243.compile · mapping),
 delta.plans.map (GeneralNominalRebasePacketView243.compile · mapping),
 delta.effects.map (GeneralNominalRebaseJournalView243.effect state · mapping),
 delta.ordinary.map (atomSubst mapping)⟩

theorem compile_exact (state : State roles) (delta : SourceDelta roles)
 (mapping : Nat → CompTerm Nat) (assignment : Assignment) :
 (compile state delta mapping).Holds assignment ↔ delta.Holds state (read mapping assignment) := by
 simp only [compile,Delta.Holds,SourceDelta.Holds,List.forall_mem_map,
   GeneralNominalRebaseObservedSite243.compile_exact,GeneralNominalRebaseLiveView243.compile_holds,
   GeneralNominalRebasePacketView243.compile_exact,GeneralNominalRebaseJournalView243.effect_exact,
   All,atom_exact]
 rfl

theorem attached_source_exact (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat))
 (success : prepare (GeneralNominalVersionedMixedSeedLedger237.entries state) = some sorted)
 (consumers : List (Atom Nat)) (delta : SourceDelta roles) (assignment : Assignment) :
 Models (attach (sourceFrame state sorted consumers) (compile state delta CompTerm.var)) assignment ↔
 GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers ∧ delta.Holds state assignment := by
 rw [GeneralNominalJournalAppend250.attach_models,
   GeneralNominalSourceOwnerFrame249.source_models_iff state reachable sorted success consumers assignment,
   compile_exact]
 exact and_assoc

theorem source_update_public_iff (state : State roles)
 (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (sorted : List (Entry Nat))
 (success : prepare (GeneralNominalVersionedMixedSeedLedger237.entries state) = some sorted)
 (consumers : List (Atom Nat)) (delta : SourceDelta roles) (raw : List (Entry Nat))
 (shared : Nat → Prop) (privateNames : ∀ name, shared name → ∀ entry ∈ sorted, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalVersionedJournal232.Models state assignment ∧ All model assignment consumers ∧
   delta.Holds state assignment ∧ Agrees model shared assignment boundary) ↔
 PublicModels (GeneralNominalPersistentOwner250.update
   (attach (sourceFrame state sorted consumers) (compile state delta CompTerm.var)) raw) shared boundary := by
 have result := GeneralNominalPersistentOwner250.public_models_iff
   (attach (sourceFrame state sorted consumers) (compile state delta CompTerm.var))
   (prepared_safe _ _ success) raw shared privateNames boundary
 simpa only [PublicModels,attached_source_exact state reachable sorted success,and_assoc] using result
end Yulang.GeneralNominalSourceDelta250
