import Yulang.GeneralRebaseMergedGate268
import Yulang.GeneralRebaseMergeCenters267

namespace Yulang.GeneralRebaseAdministrativeProbe268
open GeneralNominalVersionedJournal232 (State Models)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalSaturationState (Alias)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralRebaseOccurrenceEq267 (same same_exact)
open GeneralRebaseExecutableAlias267 (aliased aliased_exact)
open GeneralRebasePartialBool268 (Answer Reflect neg both either)
open GeneralRebasePartialFinite268 (all all_sound transfer)
open GeneralRebaseRawK2Probe268 (bool_reflect)

def inputs (_source : State roles) (proofs : Site roles → Site roles → Answer) (first last : Site roles) : Answer :=
 if first.occurrence.demand.role ≠ last.occurrence.demand.role then some false else
 if GeneralRebaseMergeCenters267.same first last then some true else proofs first last

theorem inputs_sound (source : State roles) (proofs : Site roles → Site roles → Answer)
 (first last : Site roles) (cert : Reflect (SameInputs (Models source) first last) (proofs first last)) :
 Reflect (SameInputs (Models source) first last) (inputs source proofs first last) := by
 unfold inputs
 split
 · rename_i diff
   exact fun equivalent => diff equivalent.1
 · split
   · rename_i literal
     exact GeneralRebaseMergeCenters267.source_sound (Models source) first last literal
   · exact cert

def pairReady (source : State roles) (proofs : Site roles → Site roles → Answer) (first last : Site roles) : Answer :=
 either (some (aliased source.core.erased.current first.occurrence.identity last.occurrence.identity))
  (neg (inputs source proofs first last))

theorem implication {p q : Prop} : (q ∨ ¬ p) ↔ (p → q) :=
 ⟨fun h p => h.elim id (fun no => False.elim (no p)),
  fun h => Classical.em p |>.elim (fun v => Or.inl (h v)) Or.inr⟩

theorem pair_sound (source : State roles) (proofs : Site roles → Site roles → Answer)
 (first last : Site roles) (cert : Reflect (SameInputs (Models source) first last) (proofs first last)) :
 Reflect (SameInputs (Models source) first last →
  Alias source.core.erased.current first.occurrence.identity last.occurrence.identity) (pairReady source proofs first last) :=
 transfer implication (GeneralRebasePartialBool268.either_sound
   (bool_reflect _ _ (aliased_exact ..)) (GeneralRebasePartialBool268.neg_sound (inputs_sound source proofs first last cert)))

def registered (source : State roles) (focus : Occurrence roles) : Bool :=
 source.core.sites.any fun site => same site.occurrence focus

theorem registered_exact (source : State roles) (focus : Occurrence roles) :
 registered source focus = true ↔ ∃ site ∈ source.core.sites, site.occurrence = focus := by
 simp only [registered,List.any_eq_true,same_exact]

def ready (source : State roles) (focus : Occurrence roles) (proofs : Site roles → Site roles → Answer) : Answer :=
 both (some (registered source focus))
  (all (fun first => either (neg (some (same first.occurrence focus)))
   (all (pairReady source proofs first) source.core.sites)) source.core.sites)

theorem ready_sound (source : State roles) (focus : Occurrence roles) (proofs : Site roles → Site roles → Answer)
 (cert : ∀ first ∈ source.core.sites, ∀ last ∈ source.core.sites,
   Reflect (SameInputs (Models source) first last) (proofs first last)) :
 Reflect (AdministrativeReady source focus) (ready source focus proofs) := by
 apply GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (registered_exact source focus))
 apply all_sound
 intro first listed
 apply transfer (p := (¬ first.occurrence = focus) ∨ ∀ last ∈ source.core.sites,
   SameInputs (Models source) first last → Alias source.core.erased.current first.occurrence.identity last.occurrence.identity)
 · exact or_comm.trans implication
 · exact GeneralRebasePartialBool268.either_sound
     (GeneralRebasePartialBool268.neg_sound (bool_reflect _ _ (same_exact ..)))
     (all_sound _ _ _ (fun last member => pair_sound source proofs first last (cert first listed last member)))

end Yulang.GeneralRebaseAdministrativeProbe268
