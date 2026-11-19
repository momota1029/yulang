import Yulang.GeneralRebaseRawIntoFull271
import Yulang.GeneralRebaseRecordRecursiveFixture271

namespace Yulang.GeneralRebaseK2ModelBoundary271
open GeneralRebaseRecordRecursiveFixture271 (context root)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalVersionedJournal232 (State Models initial)
open GeneralNominalVersionedCycles232 (RootCycle)
open CommonNominalFullCarrier

def contradict : PresenceNormalForm.Atom Nat := .tyLe (.base .int) (.base .str)

def inconsistentContext : GeneralNominalCandidates.Context :=
 {context with state := {context.state with ordinary := [contradict]}}

def original : State roles := initial inconsistentContext root

def emptyRegistry : GeneralDeclarations.Registry := ⟨constructors,roles,[]⟩

theorem no_models : ¬ ∃ m, Models original m := by
 rintro ⟨m,ok⟩
 have raw := ok.1.1.2.2
 have contradiction := raw contradict (List.mem_singleton_self _)
 change Subtype (.base .int) (.base .str) at contradiction
 have impossible := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) (GeneralDictionaryInspectionHeads215.tagged_scalar .str)
   contradiction
 cases impossible

theorem no_semantic : ¬ RootCycle original root := by
 intro cycle
 apply no_models
 rcases cycle with ⟨_,⟨_,full⟩⟩ | ⟨_,_,_,_,⟨_,full⟩⟩
 · exact full
 · exact full

theorem structural_self : GeneralNominalCycleK2.DirectEdge inconsistentContext.state (0 : Fin 2) (0 : Fin 2) :=
 Or.inl ⟨(0 : Fin 2),GeneralRebaseRecordRecursiveFixture271.children 0,rfl,(0 : Fin 2),rfl⟩

theorem raw_root :
 GeneralNominalCycleK2.RootK2 inconsistentContext.state (GeneralNominalVersionedCandidates231.inputs root).demand := by
 let ask := (GeneralNominalVersionedCandidates231.inputs root).demand
 have linked := (GeneralRebaseCandidateChecks267.linked_exact inconsistentContext.state ask).mp (by decide +kernel)
 have known := (GeneralRebaseCandidateChecks267.allKnown_exact inconsistentContext.state ask).mp (by decide +kernel)
 let i : Fin (roles ask.role).arity := ⟨0,by change 0 < 1; decide +kernel⟩
 exact GeneralNominalCycleK2.direct_cycle_rejects inconsistentContext.state ask linked known i (0 : Fin 2) rfl
   ⟨(0 : Fin 2),structural_self,.nil _⟩

/-- A direct raw loop is independent of consistency, unlike semantic
recurrence. Do not collapse the diagnostic branches without a model. -/
theorem necessary_scope : (Boundary roles).RootK2 emptyRegistry original root ∧ ¬ RootCycle original root :=
 ⟨Or.inl raw_root,no_semantic⟩

end Yulang.GeneralRebaseK2ModelBoundary271
