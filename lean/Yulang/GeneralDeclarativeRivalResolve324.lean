import Yulang.GeneralDeclarativeRivalReads324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRivalResolve324
open GeneralDeclarativeRivalDecl324
open GeneralDeclarativeRivalReads324 (parent_read child_read parent_matches_here child_matches_here parent_meaning child_meaning)
open GeneralDeclarativeAggregateFixture324 (newState actualNames emitted support exact_child inhabited child_ready)
open GeneralDeclarativeAggregateReads324 (childNames dict)
open GeneralDeclarativeAggregateProbe324 (parent_ready no_cycle)
open GeneralDeclarativeRepeatedSource323 (goal parent child)
open GeneralDeclarativeRepeatedReads323 (place)
open GeneralDeclarativeNFComplete324 (ReadBack)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeOrigins321 (restriction restrict_models)
open GeneralDeclarativeNominalClash324 (tests genuine_selected)
open GeneralDeclarativePriority321 (Recurs Local Visible Blocked)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Classify)

def generates (d : Demand) (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ names placement, children impl names placement = kids ∧
    ReadBack newState wider richer d impl names placement ∧ BodyCoverage wider richer d impl

noncomputable abbrev assay (complete : Nat → Prop) := tests (restriction (support complete)) wider.constructors richer
abbrev localRule (complete : Nat → Prop) := Local newState wider richer (support complete) (assay complete) generates

theorem not_recurs (complete : Nat → Prop) (d : Demand) : ¬Recurs newState wider richer (assay complete) d := by
  rintro (⟨arg,_,cycle⟩|⟨impl,_,i,arg,pat,code,_,_,_,place,_,cycle⟩)
  · exact no_cycle arg.lower cycle
  · exact no_cycle place cycle

theorem root_wins (complete : Nat → Prop) : localRule complete goal (.selected parent.id [emitted]) := by
  obtain ⟨m,valid⟩ := inhabited
  apply genuine_selected (support complete) (restrict_models (support complete) m valid)
    (parent_ready complete) (not_recurs complete _) ⟨List.mem_cons_self,rfl⟩ (parent_matches_here complete)
  · rintro impl ⟨listed,role⟩ notParent
    rcases List.mem_cons.mp listed with h|tail
    · exact False.elim (notParent h)
    · rcases List.mem_cons.mp tail with h|tail
      · cases h
        exact real_conflict complete
      · cases List.mem_singleton.mp tail
        cases role
  · exact ⟨actualNames,place,exact_child,parent_read,fun _ bad => False.elim (List.not_mem_nil bad)⟩

theorem child_wins (complete : Nat → Prop) : localRule complete emitted (.selected child.id []) := by
  obtain ⟨m,valid⟩ := inhabited
  apply genuine_selected (support complete) (restrict_models (support complete) m valid)
    (child_ready complete) (not_recurs complete _)
    ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
    (child_matches_here complete)
  · rintro impl ⟨listed,role⟩ notChild
    rcases List.mem_cons.mp listed with h|tail
    · cases h
      cases role
    · rcases List.mem_cons.mp tail with h|tail
      · cases h
        cases role
      · exact False.elim (notChild (List.mem_singleton.mp tail))
  · exact ⟨childNames,place,rfl,child_read,fun _ bad => False.elim (List.not_mem_nil bad)⟩

theorem rival_eliminated (complete : Nat → Prop) :
    Visible wider goal rival ∧ ¬(assay complete).viable goal rival ∧ ¬(assay complete).unresolved goal rival :=
  ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,not_viable complete,fun h => h.2 (real_conflict complete)⟩

theorem family_wins (complete : Nat → Prop) : Classify (localRule complete) goal (.selected dict) :=
  ⟨.selected parent.id [.selected child.id []],
    .selected (root_wins complete) (.cons (.selected (child_wins complete) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem every_model (m : Assignment) (valid : Models newState m) :
    Evidence wider richer m goal dict :=
  .node ⟨parent,actualNames.input,rfl,parent_meaning m valid⟩
    (.cons (.node ⟨child,childNames.input,rfl,child_meaning m valid⟩ .nil) .nil)

theorem successful_with_rival :
    Classify (localRule (fun _ => False)) goal (.selected dict) ∧
    (∃ m, Models newState m) ∧ ∀ m, Models newState m → Evidence wider richer m goal dict :=
  ⟨family_wins _,inhabited,every_model⟩

end Yulang.GeneralDeclarativeRivalResolve324
