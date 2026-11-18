import Yulang.GeneralRebaseChildRequestPool262
import Yulang.GeneralRebaseSourceRequestPool262
#print axioms Yulang.GeneralRebaseChildRequestPool262.equation_target
#print axioms Yulang.GeneralRebaseChildRequestPool262.clause_target
#print axioms Yulang.GeneralRebaseChildRequestPool262.emitted_target
#print axioms Yulang.GeneralRebaseChildRequestPool262.raw_target
#print axioms Yulang.GeneralRebaseChildRequestPool262.raw_name
#print axioms Yulang.GeneralRebaseChildRequestPool262.product
#print axioms Yulang.GeneralRebaseChildRequestPool262.mem_product
#print axioms Yulang.GeneralRebaseChildRequestPool262.Covered
#print axioms Yulang.GeneralRebaseChildRequestPool262.requests_covered
#print axioms Yulang.GeneralRebaseChildRequestPool262.snapshot_product
#print axioms Yulang.GeneralRebaseSourceRequestPool262.pool
#print axioms Yulang.GeneralRebaseSourceRequestPool262.trace_covered
#print axioms Yulang.GeneralRebaseSourceRequestPool262.mixed_finite_requests
#print axioms Yulang.GeneralRebaseSourceRequestPool262.all_requests
#check @Yulang.GeneralRebaseSourceRequestPool262.mixed_finite_requests
#check @Yulang.GeneralRebaseSourceRequestPool262.all_requests

open Yulang
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalVersionedJournal232
open GeneralSourceState (Output)

/-- The same finite pool covers two independently selected reachable snapshots
and arbitrary query roots, not only the source's generated root demand. -/
example (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Output, ∀ first last,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start first →
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start last →
 ∀ firstRoot lastRoot one two,
 one ∈ GeneralNominalCenteredHeadOutputs.requests first.core firstRoot →
 two ∈ GeneralNominalCenteredHeadOutputs.requests last.core lastRoot → one ∈ pool ∧ two ∈ pool := by
 obtain ⟨pool,covered⟩ := GeneralRebaseSourceRequestPool262.all_requests sourceRegistry root start source
 refine ⟨pool,?_⟩
 intro first last firstPath lastPath firstRoot lastRoot one two firstRequest lastRequest
 exact ⟨covered first firstPath firstRoot one firstRequest,covered last lastPath lastRoot two lastRequest⟩

example : GeneralRebaseChildRequestPool262.product [2] [3,5] = [⟨2,3⟩,⟨2,5⟩] := rfl
example : (⟨2,5⟩ : Output) ∈ GeneralRebaseChildRequestPool262.product [2] [3,5] := by decide
example : (⟨7,5⟩ : Output) ∉ GeneralRebaseChildRequestPool262.product [2] [3,5] := by decide
