import Yulang.GeneralNominalOrdinaryJournal194
import Yulang.GeneralNominalCenteredWhere

/-! Finite actual packet syntax makes journal child traversal well-founded.
This does not manufacture packet coverage for committed-but-unrecorded nodes. -/
namespace Yulang.GeneralNominalJournalAccessibility194
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryJournalTree (Child Covered Recorded)
variable {roles : Roles.RoleDecls}

def ceiling (state : GeneralNominalSaturationState.State roles) : Nat :=
  (state.packets.map fun packet => packet.site.occurrence.identity).foldr max 0

def rank (state : GeneralNominalSaturationState.State roles) (site : Occurrence roles) : Nat :=
  ceiling state + 1 - site.identity

theorem child_rank {state : GeneralNominalSaturationState.State roles}
    {child parent : Occurrence roles} (edge : Child state child parent) :
    rank state child < rank state parent := by
  obtain ⟨packet,present,same,member⟩ := edge
  have bounded : parent.identity ≤ ceiling state :=
    GeneralNominalCenteredWhere.member_max _ _
      (List.mem_map.mpr ⟨packet,present,congrArg Occurrence.identity same⟩)
  have above : parent.identity < child.identity := by
    rw [← same]
    exact GeneralNominalCenteredWhere.packet_child_above packet child member
  unfold rank
  omega

/-- Every root is accessible, with no reachability, stability, coverage or model premise. -/
theorem accessible (state : GeneralNominalSaturationState.State roles) (root : Occurrence roles) :
    Acc (Child state) root := by
  have all : ∀ n, ∀ root, rank state root = n → Acc (Child state) root := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro root equal
      exact Acc.intro root (fun child edge => ih _ (equal ▸ child_rank edge) child rfl)
  exact all _ root rfl

/-- Coverage alone constructs a finite recorded tree for any actual packet journal. -/
theorem recorded_tree (state : GeneralNominalSaturationState.State roles)
    (root : Occurrence roles) (covered : Covered state root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      GeneralSourceDictionaries.Evidence (Recorded state) tree :=
  GeneralDictionaryJournalTree.recorded_tree state root covered (accessible state root)

/-- Ordinary WF execution plus coverage yields a uniform semantic dictionary;
no independent accessibility certificate is necessary. -/
theorem uniform_dictionary {registry : Registry} {root : Occurrence roles}
    {context : GeneralNominalCandidates.Context} {after : GeneralNominalCenteredHeadStepEffects.State roles}
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (GeneralNominalCenteredHeadStepEffects.initial context root) after)
    (covered : Covered after.core.erased.current root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      GeneralSourceDictionaries.Evidence (Recorded after.core.erased.current) tree ∧
      ∀ model, GeneralNominalCenteredHeadStepEffects.Models after model →
        (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry after model root (erase tree) :=
  GeneralNominalOrdinaryJournal194.uniform_dictionary path covered (accessible _ root)
end Yulang.GeneralNominalJournalAccessibility194
