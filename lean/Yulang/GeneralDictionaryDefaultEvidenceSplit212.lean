import Yulang.GeneralDictionaryDefaultProvenance212
import Yulang.GeneralDictionaryDefaultComposition211

/-! An exhaustive split of the one remaining evidence field. Nonterminal
child evidence already forces historical parent provenance; no new selection
predicate and no fresh completion helper are introduced. -/
namespace Yulang.GeneralDictionaryDefaultEvidenceSplit212
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls} {state : State roles}

 def HistoricalInvocation (state : State roles) (focus : Occurrence roles) (key : Nat) : Prop :=
  ∃ plan ∈ state.core.plans, plan.packet.site.occurrence.identity = focus.identity ∧
    plan.packet.declaration.id = key

 theorem nonempty_child_evidence_historical
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (nonempty : children ≠ [])
    (given : All₂ ((boundary roles).Evidence value state model) children dictionaries) :
    HistoricalInvocation state focus key := by
  obtain ⟨current,frame,kids⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable selected
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil children nonempty
  obtain ⟨dictionary,evidence⟩ := GeneralDictionaryDefaultSoundness211.children_classified given member
  obtain ⟨historical,present,identity,declaration⟩ :=
    GeneralDictionaryDefaultProvenance212.child_registered_parent checked reachable frame (kids.symm ▸ member)
      (GeneralDictionaryDefaultSelectedGeneration211.evidence_registered evidence)
  exact ⟨historical,present,identity,(congrArg Declaration.id declaration).trans frame.key_eq⟩

 theorem fresh_child_evidence_empty
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (fresh : ¬ HistoricalInvocation state focus key)
    (given : All₂ ((boundary roles).Evidence value state model) children dictionaries) :
    children = [] := by
  apply Classical.byContradiction
  intro nonempty
  exact fresh (nonempty_child_evidence_historical checked reachable selected nonempty given)

/-- Terminal parents without a historical invocation. The quantified model,
reachability, stability and selected domain are unchanged from EvidenceNode. -/
 def FreshTerminal (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → ∀ model,
    (boundary roles).Models state model → ∀ focus key,
    (focus = root ∨ (boundary roles).Generated value state root focus) →
    (boundary roles).Stable value state focus →
    Local value state focus (.selected key []) →
    ¬ HistoricalInvocation state focus key →
    (boundary roles).Evidence value state model focus (.node key [])

/-- Historical invocations, including changed endpoint reports. Equality of
historical/current parent occurrences or child lists is not assumed. -/
 def HistoricalReplay (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → ∀ model,
    (boundary roles).Models state model → ∀ focus key children dictionaries,
    (focus = root ∨ (boundary roles).Generated value state root focus) →
    (boundary roles).Stable value state focus →
    (∀ child ∈ children, (boundary roles).Stable value state child) →
    Local value state focus (.selected key children) →
    HistoricalInvocation state focus key →
    All₂ ((boundary roles).Evidence value state model) children dictionaries →
    (boundary roles).Evidence value state model focus (.node key dictionaries)

 theorem evidenceNode (terminal : FreshTerminal roles) (replay : HistoricalReplay roles) :
    B4SkeletonV7.EvidenceNode (boundary roles) := by
  intro value checked state root reachable model valid focus key children dictionaries reached stable childStable selected given
  by_cases history : HistoricalInvocation state focus key
  · exact replay value checked state root reachable model valid focus key children dictionaries
      reached stable childStable selected history given
  · have empty := fresh_child_evidence_empty checked reachable selected history given
    subst children
    cases given
    exact terminal value checked state root reachable model valid focus key reached stable selected history

 theorem evidenceNode_iff : B4SkeletonV7.EvidenceNode (boundary roles) ↔
    FreshTerminal roles ∧ HistoricalReplay roles := by
  constructor
  · intro node
    constructor
    · intro value checked state root reachable model valid focus key reached stable selected _
      exact node value checked state root reachable model valid focus key [] [] reached stable
        (by intro child member; cases member) selected .nil
    · intro value checked state root reachable model valid focus key children dictionaries reached stable childStable selected _ given
      exact node value checked state root reachable model valid focus key children dictionaries reached stable childStable selected given
  · exact fun ⟨terminal,replay⟩ => evidenceNode terminal replay

 theorem composition (terminal : FreshTerminal roles) (replay : HistoricalReplay roles) :
    B4TargetV7.Statement (boundary roles) (GeneralDictionaryDefaultExecutor208.executor roles) :=
  GeneralDictionaryDefaultComposition211.composition (evidenceNode terminal replay)

end Yulang.GeneralDictionaryDefaultEvidenceSplit212
