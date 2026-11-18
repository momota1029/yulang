import Yulang.GeneralRebaseSourceCenters263
import Yulang.GeneralRebaseRegisteredOwners263
namespace Yulang.GeneralRebaseSourceRepresentatives263
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)

abbrev Path (registry : Registry) (root : Occurrence roles) (start state : State roles) :=
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root) start state

def RegisteredAt (registry : Registry) (root : Occurrence roles) (start : State roles)
 (owner : Nat) (plan : Plan roles) : Prop :=
 ∃ state, Path registry root start state ∧ plan ∈ state.plans ∧ GeneralRebaseRegisteredOwners263.code plan = owner

/-- Mathematical choice only, not a computable discovery procedure for future
plans. A single actual registered plan is a fallback for unused owner codes. -/
noncomputable def representatives (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan) : Nat → Plan roles := by
 classical
 exact fun owner => if existsPlan : ∃ plan, RegisteredAt registry root start owner plan
   then Classical.choose existsPlan else Classical.choose (Classical.choose_spec inhabited)

theorem representatives_registered (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owner : Nat) (occurs : ∃ plan, RegisteredAt registry root start owner plan) :
 RegisteredAt registry root start owner (representatives registry root start inhabited owner) := by
 classical
 simp only [representatives,dite_eq_left occurs]
 exact Classical.choose_spec occurs

theorem exists_representatives (registry : Registry) (root : Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan) :
 ∃ representative : Nat → Plan roles, ∀ owner,
 (∃ plan, RegisteredAt registry root start owner plan) → RegisteredAt registry root start owner (representative owner) :=
 ⟨representatives registry root start inhabited,representatives_registered registry root start inhabited⟩

/-- Actual head support across source futures. This strong, explicit semantic
context contains no body, child or output ClassEffects assumption. It is not
asserted to follow from source formation or arbitrary assignments. -/
def SourceHeads (registry : Registry) (root : Occurrence roles) (start : State roles) (assignment : Assignment) : Prop :=
 ∀ state, Path registry root start state → GeneralRebaseSourceCenters263.Heads state assignment

theorem layout (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (owner : Nat) (first last : Plan roles)
 (one : RegisteredAt registry root start owner first) (two : RegisteredAt registry root start owner last) :
 GeneralRebasePlanSemantic262.Layout first last := by
 obtain ⟨before,pathOne,memberOne,codeOne⟩ := one
 obtain ⟨after,pathTwo,memberTwo,codeTwo⟩ := two
 exact GeneralRebaseRegisteredPlan263.source_layout registry checked root start before after source
   pathOne pathTwo first last memberOne memberTwo
   ((GeneralRebaseRegisteredOwners263.code_eq_iff first last).mp (codeOne.trans codeTwo.symm))

theorem compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (owner : Nat) (first last : Plan roles)
 (one : RegisteredAt registry root start owner first) (two : RegisteredAt registry root start owner last)
 (assignment : Assignment) (heads : SourceHeads registry root start assignment) :
 GeneralRebaseNormalizedBody263.Compatible first last assignment := by
 obtain ⟨before,pathOne,memberOne,codeOne⟩ := one
 obtain ⟨after,pathTwo,memberTwo,codeTwo⟩ := two
 exact GeneralRebaseSourceCenters263.source_compatible_from_heads registry checked root start before after source
   pathOne pathTwo first last memberOne memberTwo
   ((GeneralRebaseRegisteredOwners263.code_eq_iff first last).mp (codeOne.trans codeTwo.symm))
   assignment (heads before pathOne) (heads after pathTwo)

theorem representative_layout (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (state : State roles) (path : Path registry root start state) (plan : Plan roles) (member : plan ∈ state.plans) :
 GeneralRebasePlanSemantic262.Layout
   (representatives registry root start inhabited (GeneralRebaseRegisteredOwners263.code plan)) plan := by
 have actual : RegisteredAt registry root start (GeneralRebaseRegisteredOwners263.code plan) plan := ⟨state,path,member,rfl⟩
 exact layout registry checked root start source _ _ plan
   (representatives_registered registry root start inhabited _ ⟨plan,actual⟩) actual

theorem representative_compatible (registry : Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (state : State roles) (path : Path registry root start state) (plan : Plan roles) (member : plan ∈ state.plans)
 (assignment : Assignment) (heads : SourceHeads registry root start assignment) :
 GeneralRebaseNormalizedBody263.Compatible
   (representatives registry root start inhabited (GeneralRebaseRegisteredOwners263.code plan)) plan assignment := by
 have actual : RegisteredAt registry root start (GeneralRebaseRegisteredOwners263.code plan) plan := ⟨state,path,member,rfl⟩
 exact compatible registry checked root start source _ _ plan
   (representatives_registered registry root start inhabited _ ⟨plan,actual⟩) actual assignment heads
end Yulang.GeneralRebaseSourceRepresentatives263
