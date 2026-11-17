import Yulang.GeneralNominalViewSupport249
import Yulang.GeneralPresenceOrderedExpansion249

/-! Actual raw state transport with new unobserved targets. Complete raw View
support is explicit; no source-field is hidden by an abstract stability law.
Packet/history/cache occurrences and operational coverage are separate. -/
namespace Yulang.GeneralNominalOrderedRawExpansion249
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralPresenceCommonLaws245
open GeneralNominalRebaseRawView243 (View)

def Protected (state : GeneralNominalState.State) (old fresh : List (Entry Nat)) : Prop :=
 ∀ name ∈ GeneralNominalViewSupport249.support
   (GeneralNominalRebaseRawView243.compile state (mapping old)),
   ∀ entry ∈ fresh, entry.1 ≠ name

theorem view_preserved (view : View) (fresh : List (Entry Nat)) (assignment : Assignment)
 (protectedReads : ∀ name ∈ GeneralNominalViewSupport249.support view,
   ∀ entry ∈ fresh, entry.1 ≠ name) :
 view.Models (solve model fresh assignment) ↔ view.Models assignment := by
 apply GeneralNominalViewSupport249.models_iff view _ assignment (solve_rows model fresh assignment)
 intro name member
 exact congrArg Prod.fst (solve_outside model fresh assignment name (protectedReads name member))

theorem raw_forward (state : GeneralNominalState.State) (old fresh : List (Entry Nat))
 (protectedReads : Protected state old fresh) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 (GeneralNominalRebaseRawView243.compile state (mapping old)).Models (solve model fresh assignment) ↔
 GeneralNominalState.Models state assignment := by
 rw [view_preserved _ fresh assignment protectedReads,GeneralNominalOrderedRaw248.raw_exact]
 exact GeneralNominalRawCongruence238.models_iff state
   (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws old assignment valid)

theorem raw_public_models_iff (state : GeneralNominalState.State) (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (protectedRaw : Protected state old fresh) (consumers : List (Atom Nat))
 (protectedConsumers : GeneralPresenceOrderedExpansion249.Protected old fresh consumers)
 (sharedNames : Nat → Prop)
 (oldPrivate : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (freshPrivate : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalState.Models state assignment ∧
   All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseRawView243.compile state (mapping old)).Models assignment ∧
   All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,raw,valid,agree⟩
   refine ⟨solve model fresh assignment,?_,
     GeneralPresenceOrderedExpansion249.models_forward model common_laws old fresh freshSafe
       consumers protectedConsumers assignment valid,?_⟩
   · exact (raw_forward state old fresh protectedRaw assignment
       ((all_append model assignment _ _).mp valid).2).mpr raw
   · intro name shared
     rw [solve_outside model fresh assignment name (freshPrivate name shared)]
     exact agree name shared
 · rintro ⟨assignment,raw,valid,agree⟩
   refine ⟨solve model old assignment,(GeneralNominalOrderedRaw248.raw_exact state old assignment).mp raw,
     GeneralPresenceOrderedRebase247.models_backward model common_laws old fresh oldSafe consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (oldPrivate name shared)]
   exact agree name shared
end Yulang.GeneralNominalOrderedRawExpansion249
