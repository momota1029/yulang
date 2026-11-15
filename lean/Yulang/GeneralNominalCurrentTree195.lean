import Yulang.GeneralNominalCurrentCompletion195

/-! Finite original-state registration constructs a uniform semantic dictionary
from current reusable plans. There is no supplied catalogue, well-foundedness
certificate, ordinary trace, recursive Evidence or preconstructed payload. -/
namespace Yulang.GeneralNominalCurrentTree195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalSaturationState (Generated)
open GeneralNominalReuseCatalogue195 (Reusable reusable_instance)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

/-- Stronger than selected-only completion: every generated obligation has a
current reusable plan, so no generated pending/rejected node is being hidden. -/
def TotalCompletion (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus →
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ Reusable registry state plan

def Rule (registry : Registry) (state : State roles) : LocalInstance roles :=
  fun focus key children => ∃ plan : Plan roles, Reusable registry state plan ∧
    plan.packet.site.occurrence = focus ∧ plan.packet.declaration.id = key ∧ plan.packet.children = children

def ceiling (state : State roles) : Nat :=
  (state.core.erased.current.sites.map fun site => site.occurrence.identity).foldr max 0

def rank (state : State roles) (focus : Occurrence roles) : Nat := ceiling state + 1 - focus.identity

theorem child_rank {plan : Plan roles} (reuse : Reusable registry state plan)
    {child : Occurrence roles} (member : child ∈ plan.packet.children) :
    rank state child < rank state plan.packet.site.occurrence := by
  have bounded : plan.packet.site.occurrence.identity ≤ ceiling state :=
    GeneralNominalCenteredWhere.member_max _ _ (List.mem_map.mpr ⟨plan.packet.site,reuse.1.raw_recorded,rfl⟩)
  have above := GeneralNominalCenteredWhere.packet_child_above plan.packet child member
  unfold rank
  omega

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

/-- Finite registration supplies the decreasing rank; the resulting dictionary
is chosen independently of every assignment. -/
theorem tree_exists (complete : TotalCompletion registry state root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
  have all : ∀ n, ∀ focus, rank state focus = n → Generated state.core.erased.current root focus →
      ∃ tree : Dictionary roles, tree.root = focus ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro focus equal generated
      obtain ⟨plan,same,reuse⟩ := complete focus generated
      have children : ∀ child ∈ plan.packet.children,
          ∃ tree : Dictionary roles, tree.root = child ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree := by
        intro child member
        have smaller := child_rank reuse member
        rw [same,equal] at smaller
        exact ih _ smaller child rfl (.child generated (same ▸ reuse.2.2.2 child member))
      obtain ⟨trees,roots,valid⟩ := assemble (Rule registry state) plan.packet.children children
      exact ⟨.node focus plan.packet.declaration.id trees,rfl,
        .node ⟨plan,reuse,same,rfl,roots.symm⟩ valid⟩
  exact all _ root rfl .root

theorem uniform_dictionary (complete : TotalCompletion registry state root) :
    ∃ tree : Dictionary roles, tree.root = root ∧ GeneralSourceDictionaries.Evidence (Rule registry state) tree ∧
      ∀ model, Models state model → (boundary roles).Evidence registry state model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := tree_exists complete
  refine ⟨tree,same,syntactic,?_⟩
  intro model valid
  refine ⟨tree,⟨same,rfl⟩,?_⟩
  apply evidence_mono (Rule registry state)
    (GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model)
    (fun focus key children rule => ?_) syntactic
  obtain ⟨plan,reuse,rfl,rfl,rfl⟩ := rule
  exact reusable_instance reuse model valid

/-- Total current completion also supplies the selected-only bridge. -/
theorem selected_completion (complete : TotalCompletion registry state root) :
    GeneralNominalCurrentCompletion195.SelectedCompletion registry state root :=
  fun focus generated _ _ _ => complete focus generated
end Yulang.GeneralNominalCurrentTree195
