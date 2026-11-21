import Yulang.GeneralDeclarativeFollower324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFollowerResolve324
open GeneralDeclarativeFollower324
open GeneralDeclarativeHiddenDecl324 (registry interpretation checked)
open GeneralDeclarativeHiddenState324 (final support)
open GeneralDeclarativeHiddenProbe324 (root_bounds safe tests)
open GeneralDeclarativeHiddenResolve324 (branch)
open GeneralDeclarativeNFNode324 (Reads meaning)
open GeneralDeclarativeNFResolve324 (Generates)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeLowerKnown321 (Delayed ready_iff_not_delayed)
open GeneralDeclarativeExampleSource320 (leaf point)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonRoleOutermostResolver (Classify Dictionary All₂)

abbrev names : Names := ⟨fun _ => point 6,fun _ => 6⟩
abbrev place : Placement := ⟨fun _ _ => point 400,fun _ _ => 401⟩

theorem blocked_without (done : Nat → Prop) (missing : ¬(done 1 ∧ done 2)) :
    branch done later .pending := by
  have cannot := fun h => missing ((ready_iff done).mp h)
  have delayed : Delayed (support done) later := by
    apply Classical.byContradiction
    intro noDelay
    exact cannot ((ready_iff_not_delayed ..).mpr noDelay)
  exact .unsupported delayed (safe done _)

theorem leaf_match (done : Nat → Prop) :
    HeadMatches (restriction (support done)) registry.constructors interpretation later leaf :=
  .cons ⟨root_bounds _ 6,.variable 0,[⟨0,.lower,6⟩],[⟨0,.upper,6⟩],rfl,.capture,.capture⟩ .nil

theorem read_leaf : Reads final registry interpretation later leaf names place := by
  refine ⟨.cons ⟨root_bounds _ 6,⟨[⟨6,.variable 6⟩],rfl,?_⟩⟩ .nil,
    fun _ _ => root_bounds _ 6,fun _ bad => False.elim (List.not_mem_nil bad),
    fun _ bad => False.elim (List.not_mem_nil bad)⟩
  intro row there m _
  cases List.mem_singleton.mp there
  exact eqv_refl _

theorem chosen_with (done : Nat → Prop) (p : done 1) (c : done 2) :
    branch done later (.selected leaf.id []) := by
  refine .selected (ready_both done p c) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,leaf_match done⟩ ?_
    ⟨names,place,rfl,read_leaf,fun _ no => False.elim (List.not_mem_nil no)⟩
  · rintro ⟨decl,⟨listed,role⟩,fail⟩
    rcases List.mem_cons.mp listed with a|b
    · cases a
      cases role
    · cases List.mem_singleton.mp b
      exact fail (leaf_match done)
  · rintro decl ⟨⟨listed,role⟩,_⟩
    rcases List.mem_cons.mp listed with a|b
    · cases a
      cases role
    · cases List.mem_singleton.mp b
      rfl

theorem chosen_evidence (done : Nat → Prop) (p : done 1) (c : done 2) :
    Classify (branch done) later (.selected (.node leaf.id [])) ∧
      ∀ m, Models final m → Evidence registry interpretation m later (.node leaf.id []) := by
  constructor
  · exact ⟨.selected leaf.id [],.selected (chosen_with done p c) .nil,.selected .nil (.selected rfl)⟩
  · intro m valid
    refine .node ⟨leaf,names.input,rfl,meaning checked (List.mem_cons_of_mem _ List.mem_cons_self) rfl
      (fun _ no => False.elim (List.not_mem_nil no)) (fun _ no => False.elim (List.not_mem_nil no))
      read_leaf ?_ m valid⟩ .nil
    rintro _ ⟨_,no,_⟩
    cases no

end Yulang.GeneralDeclarativeFollowerResolve324
