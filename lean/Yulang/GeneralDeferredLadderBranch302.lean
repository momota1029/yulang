import Yulang.GeneralDeferredLadderExact302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderBranch302
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderRefresh302 (promotedContext certificate strict tracked_terminal)
open GeneralDeferredLadderExact302 (Promotion RawStep promotion_legal)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalRefinements (Refines)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom All)
open CommonNominalFullCarrier (subtype_refl)

abbrev self (n : Nat) : Atom Nat := .tyLe (.var (n+1)) (.var (n+1))
abbrev padding (n extras : Nat) := List.replicate extras (self n)

abbrev variant (p : Phase n k) (extras : Nat) :=
  GeneralDictionaryOrdinaryTransport.extend (promotedContext p) [] (padding n extras) []

abbrev successor (p : Phase n k) (extras : Nat) :=
  refresh p.state (variant p extras)

theorem padding_models (n extras : Nat) (m : Assignment) :
    All CommonNominalFullCarrier.model m (padding n extras) := by
  intro atom present
  have eq := List.eq_of_mem_replicate present
  subst atom
  exact subtype_refl _

theorem variant_support (p : Phase n k) (extras : Nat) :
    GeneralNominalState.sources (variant p extras).state ⊆
     GeneralNominalState.sources p.state.core.erased.current.context.state := by
  apply GeneralNominalAllocationSupport.extend_sources _ [] _
    (certificate p).support (by intro _ absent; cases absent)
  intro atom inRep a seen
  have eq := List.eq_of_mem_replicate inRep
  subst atom
  have atEnd : a = n+1 := by
    simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using seen
  simpa only [atEnd] using tracked_terminal p

def variant_refines (p : Phase n k) (extras : Nat) :
    Refines p.state.core.erased.current.context.state (variant p extras).state := by
  let base := (certificate p).refines
  refine ⟨base.base,base.heads,base.nominals,?_,base.known,?_,?_,base.seed,base.constructors⟩
  · intro atom seen
    exact List.mem_append_left _ (base.ordinary atom seen)
  · intro id seen
    exact List.mem_append_left _ (base.reserved id seen)
  · intro key seen
    exact List.mem_append_left _ (base.allocated key seen)

theorem variant_models (p : Phase n k) (extras : Nat) (m : Assignment) :
    GeneralNominalState.Models (variant p extras).state m ↔
      GeneralNominalState.Models (promotedContext p).state m := by
  rw [GeneralDictionaryOrdinaryTransport.models_extended]
  exact ⟨And.left,fun held => ⟨held,padding_models n extras m⟩⟩

theorem variant_cache (p : Phase n k) (extras : Nat) :
    GeneralNominalVersionedMixedObservations233.CacheSound p.state (variant p extras).state := by
  intro observation seen
  refine ⟨[],[],.source,.source,?_⟩
  intro m _ sourceFacts
  have source := sourceFacts.1
  rw [p.source_eq] at source
  have promoted : GeneralNominalState.Models (promotedContext p).state m :=
    (GeneralDictionaryOrdinaryTransport.models_extended ..).mpr
      ⟨(GeneralObservedLadderRefresh301.target_models n m).mpr source,p.extra_models m⟩
  exact GeneralCanonicalObservations.recorded_sound _ m ((variant_models p extras m).mpr promoted) seen

def variantCertificate (p : Phase n k) (extras : Nat) : Refresh p.state (variant p extras) := by
  refine ⟨variant_refines p extras,(certificate p).interpretation,variant_support p extras,?_,variant_cache p extras⟩
  intro m held
  have base := (certificate p).constraints m held
  exact ⟨base.1,(PresenceNormalForm.all_append ..).mpr ⟨base.2,padding_models n extras m⟩⟩

theorem promotion (p : Phase n k) (extras : Nat) : Promotion n p.state (successor p extras) :=
  ⟨variant p extras,variantCertificate p extras,strict p,rfl⟩

theorem actual (p : Phase n k) (extras : Nat) : RawStep p.state (successor p extras) :=
  promotion_legal p _ (promotion p extras)

theorem length (p : Phase n k) (extras : Nat) :
    (successor p extras).core.erased.current.context.state.ordinary.length =
      (promotedContext p).state.ordinary.length + extras := by
  change ((promotedContext p).state.ordinary ++ padding n extras).length = _
  simp [Nat.add_assoc]

theorem injective (p : Phase n k) : Function.Injective (successor p) := by
  intro i j eq
  have old := congrArg (fun s : State roles => s.core.erased.current.context.state.ordinary.length) eq
  change (successor p i).core.erased.current.context.state.ordinary.length =
    (successor p j).core.erased.current.context.state.ordinary.length at old
  rw [length,length] at old
  omega

theorem models_preserved (p : Phase n k) (extras : Nat) (m : Assignment) :
    Models (successor p extras) m ↔ Models p.state m :=
  GeneralNominalVersionedMixedObservations233.refresh_models (variantCertificate p extras)

/-- Infinitely many literal one-step successors, with fixed observed identity,
identical semantic models, and no new edges. This is not nontermination. -/
theorem infinite_successors (p : Phase n k) :
    ∃ f : Nat → State roles, Function.Injective f ∧ ∀ i, RawStep p.state (f i) :=
  ⟨successor p,injective p,actual p⟩

end Yulang.GeneralDeferredLadderBranch302
