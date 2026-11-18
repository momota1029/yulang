import Yulang.GeneralRebaseRegisteredOwners263
#print axioms Yulang.GeneralRebaseRegisteredOwners263.key
#print axioms Yulang.GeneralRebaseRegisteredOwners263.code
#print axioms Yulang.GeneralRebaseRegisteredOwners263.code_eq_iff
#print axioms Yulang.GeneralRebaseRegisteredOwners263.registered_origin
#print axioms Yulang.GeneralRebaseRegisteredOwners263.source_initial_empty
#print axioms Yulang.GeneralRebaseRegisteredOwners263.source_finite_keys
#print axioms Yulang.GeneralRebaseRegisteredOwners263.selected
#print axioms Yulang.GeneralRebaseRegisteredOwners263.source_finite_codes
#print axioms Yulang.GeneralRebaseRegisteredOwners263.source_selection_covered
#check @Yulang.GeneralRebaseRegisteredOwners263.registered_origin
#check @Yulang.GeneralRebaseRegisteredOwners263.source_finite_codes
open Yulang GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
example (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ owners : List Nat, ∀ first last,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start first →
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start last →
 ∀ one ∈ first.plans, ∀ two ∈ last.plans,
 GeneralRebaseRegisteredOwners263.code one ∈ owners ∧ GeneralRebaseRegisteredOwners263.code two ∈ owners := by
 obtain ⟨owners,finite⟩ := GeneralRebaseRegisteredOwners263.source_finite_codes sourceRegistry root start source
 exact ⟨owners,fun first last left right one firstMember two lastMember =>
   ⟨finite first left one firstMember,finite last right two lastMember⟩⟩
example (first last : Plan roles)
 (different : first.packet.site.occurrence.identity ≠ last.packet.site.occurrence.identity) :
 GeneralRebaseRegisteredOwners263.code first ≠ GeneralRebaseRegisteredOwners263.code last := by
 intro same
 exact different (congrArg Prod.fst ((GeneralRebaseRegisteredOwners263.code_eq_iff first last).mp same))
