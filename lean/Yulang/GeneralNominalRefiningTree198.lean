import Yulang.GeneralNominalRefiningCompletion198
import Yulang.GeneralNominalMixedTree198

/-! State-bounded finite synthesis mixes real recorded nodes and current reuse.
No caller enumeration of plans or accessibility witness is required. -/
namespace Yulang.GeneralNominalRefiningTree198
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRefiningCompletion198
open GeneralNominalMixedCompletion198 (Rule TotalCompletion)
open GeneralNominalMixedTree198 (rank child_rank)
open GeneralNominalRefiningJournal198 (MixedStep)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

private theorem assemble (rule : LocalInstance roles) (sites : List (Occurrence roles))
    (given : ∀ site ∈ sites, ∃ tree : Dictionary roles, tree.root = site ∧ GeneralSourceDictionaries.Evidence rule tree) :
    ∃ trees : List (Dictionary roles), trees.map Dictionary.root = sites ∧
      ∀ tree ∈ trees, GeneralSourceDictionaries.Evidence rule tree := by
  induction sites with
  | nil => exact ⟨[],rfl,by intro _ member; cases member⟩
  | cons site sites ih =>
    obtain ⟨first,root,evidence⟩ := given site (List.mem_cons_self)
    obtain ⟨rest,roots,valid⟩ := ih (fun site member => given site (List.mem_cons_of_mem _ member))
    refine ⟨first :: rest,by simp only [List.map_cons,root,roots],?_⟩
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact evidence
    · exact valid tree member

/-- Source identifiers in the actual finite state supply a decreasing rank.
Completion is nonrecursive and may choose different kinds of nodes locally. -/
theorem tree_exists {context : GeneralNominalCandidates.Context}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (complete : TotalCompletion registry state root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
  have all : ∀ n, ∀ focus, rank state focus = n → Generated state.core.erased.current root focus →
      ∃ tree : Dictionary roles, tree.root = focus ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro focus equal generated
      obtain ⟨key,children,rule⟩ := complete focus generated
      have kids : ∀ child ∈ children,
          ∃ tree : Dictionary roles, tree.root = child ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
        intro child member
        have smaller := child_rank rule child member
        rw [equal] at smaller
        exact ih _ smaller child rfl (children_generated path rule generated child member)
      obtain ⟨trees,roots,valid⟩ := assemble (Rule registry state) children kids
      exact ⟨.node focus key trees,rfl,.node (roots.symm ▸ rule) valid⟩
  exact all _ root rfl .root

/-- Uniform finite semantic Evidence in the original final models, without
supplied catalogue, rank, accessibility, recursive tree, or semantic premise. -/
theorem uniform_dictionary {context : GeneralNominalCandidates.Context}
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (complete : TotalCompletion registry state root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree ∧
      ∀ model, Models state model → (boundary roles).Evidence registry state model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := tree_exists path complete
  refine ⟨tree,same,syntactic,?_⟩
  intro model valid
  exact ⟨tree,⟨same,rfl⟩,
    evidence_mono _ _ (fun _ _ _ rule => node_instance path rule model valid) syntactic⟩
end Yulang.GeneralNominalRefiningTree198
