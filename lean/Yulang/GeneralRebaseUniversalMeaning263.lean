import Yulang.GeneralRebaseUniversalObserver263
import Yulang.GeneralRebaseNormalizedFacts263

namespace Yulang.GeneralRebaseUniversalMeaning263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseUniversalObserver263 (Current)

def Models (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 {pool : List Output} (state : Current owners pool) (assignment : Assignment) : Prop :=
 GeneralRebaseFactSemantics259.Models base (GeneralRebaseOwnerTable263.Holds owners representative) state assignment

/-- Interpret only the actual emitted keys. Unused reserved addresses impose
no obligations, and no equality between the universal and compiled bases is needed. -/
theorem actual_proposal (owners : List Nat) (representative : Nat → Plan roles)
 (owner : Nat) (listed : owner ∈ owners) (plan : Plan roles) (outputs : List Output) (assignment : Assignment)
 (compatible : GeneralRebaseNormalizedBody263.Compatible (representative owner) plan assignment) :
 (∀ fact ∈ GeneralRebaseStableClass261.facts plan owner outputs,
   GeneralRebaseOwnerTable263.Holds owners representative assignment fact) ↔
 GeneralRebaseClassTable261.Effects plan outputs assignment := by
 rw [← GeneralRebaseStableClass261.all_exact plan owner outputs assignment]
 constructor
 · intro valid fact member
   exact (GeneralRebaseNormalizedFacts263.stable_class_holds _ _ assignment compatible owner fact).mp
     ((GeneralRebaseOwnerTable263.holds_owned owners representative owner listed assignment fact
       (GeneralRebaseOwnerTags263.tagged plan owner outputs fact member)).mp (valid fact member))
 · intro valid fact member
   exact (GeneralRebaseOwnerTable263.holds_owned owners representative owner listed assignment fact
     (GeneralRebaseOwnerTags263.tagged plan owner outputs fact member)).mpr
     ((GeneralRebaseNormalizedFacts263.stable_class_holds _ _ assignment compatible owner fact).mpr (valid fact member))

theorem write_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (owner : Nat) (listed : owner ∈ owners) (plan : Plan roles) (outputs : List Output)
 (covered : ∀ output ∈ outputs, output ∈ pool)
 (compatible : ∀ assignment, base assignment → GeneralRebaseNormalizedBody263.Compatible (representative owner) plan assignment)
 (before : Current owners pool) (assignment : Assignment) :
 Models base owners representative (write before (GeneralRebaseStableClass261.facts plan owner outputs)) assignment ↔
 Models base owners representative before assignment ∧ GeneralRebaseClassTable261.Effects plan outputs assignment := by
 rw [Models,GeneralRebaseFactSemantics259.write_exact]
 constructor
 · rintro ⟨prior,new⟩
   refine ⟨prior,(actual_proposal owners representative owner listed plan outputs assignment (compatible assignment prior.1)).mp ?_⟩
   intro fact member
   exact new fact (GeneralRebaseUniversalBasis263.proposal_covered owners pool plan owner listed outputs covered member) member
 · rintro ⟨prior,effects⟩
   refine ⟨prior,?_⟩
   intro fact _ member
   exact (actual_proposal owners representative owner listed plan outputs assignment (compatible assignment prior.1)).mpr effects fact member

theorem actual_write (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (owner : Nat) (listed : owner ∈ owners)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
 (coverage : GeneralRebaseChildRequestPool262.Covered source pool)
 (compatible : ∀ assignment, base assignment → GeneralRebaseNormalizedBody263.Compatible (representative owner) plan assignment)
 (before : Current owners pool) (assignment : Assignment) :
 Models base owners representative
   (write before (GeneralRebaseMultiSelection263.proposal source ⟨owner,root,plan⟩)) assignment ↔
 Models base owners representative before assignment ∧ GeneralNominalVersionedEffects231.ClassEffects source root plan assignment := by
 unfold GeneralRebaseMultiSelection263.proposal GeneralRebaseMultiSelection263.requests
 rw [GeneralRebaseExecutableRequests262.requests_eq]
 exact write_exact base owners representative pool owner listed plan _
   (GeneralRebaseChildRequestPool262.requests_covered source pool coverage root) compatible before assignment

theorem initial_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (assignment : Assignment) :
 Models base owners representative (initial (GeneralRebaseUniversalBasis263.basis owners pool)) assignment ↔ base assignment :=
 GeneralRebaseFactSemantics259.initial_exact ..
end Yulang.GeneralRebaseUniversalMeaning263
