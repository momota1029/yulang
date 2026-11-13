import Yulang.GeneralNominalOccurrenceEnumeration

/-! A finite cover and accessibility for the actual-inspection relation,
conditional only on bounded installation ancestry. The finite code construction
retains semantic deltas and literal child identities. -/
namespace Yulang.GeneralNominalActualBudget
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalSharedBudget (Signature Represents remaining remaining_monotone remaining_decreases
  novel_signature installed_signature)

structure SignatureCover (registry : Registry) (root : Occurrence roles) (start : Tracked roles) where
  basis : List (Signature roles)
  covers : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ packet : Packet roles, ∀ support,
      Generated state.current root packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.current packet → PacketGuard state packet support →
      ∃ signature ∈ basis, Represents signature packet

theorem formed_step_cases {roles : Roles.RoleDecls} {root : Occurrence roles} {before after : Tracked roles} (formed : SourceFormed registry root before) (step : Step registry root before after) :
    GeneralNominalSharedSteps.Passive registry before after ∨ ∃ packet : Packet roles, ∃ support,
      Generated before.current root packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
      PacketGuard before packet support ∧ after = GeneralNominalSharedSteps.install before packet support := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install packet support enabled novel guard => exact Or.inr ⟨packet,support,generated,enabled,novel,guard,rfl⟩
  | merge first last support one two same novel guard => exact Or.inl (.ordinary (.merge first last one two same novel))
  | administrative focus after action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
      exact False.elim (absent site member same)
    | refresh context certificate source member unknown known =>
      exact Or.inl (.ordinary (.refresh focus context certificate source member unknown known))
    | equate first last one two equal novel => exact Or.inl (.ordinary (.equate focus first last one two equal novel))
    | reobserve revision certificate improved => exact Or.inl (.reobserve revision certificate improved)

theorem accessible_of_signature_cover {roles : Roles.RoleDecls} {root : Occurrence roles} {start : Tracked roles} (cover : SignatureCover registry root start)
    (formed : SourceFormed registry root start) :
    Acc (fun next current => Step registry root current next) start := by
  have all : ∀ n, ∀ state : Tracked roles, remaining cover.basis state = n →
      SourceFormed registry root state → B4Target.Steps (Step registry root) start state →
      Acc (fun next current => Step registry root current next) state := by
    intro n
    induction Nat.lt_wfRel.wf.apply n with
    | intro n below ih =>
      intro state
      induction GeneralNominalSharedSteps.passive_accessible registry state with
      | intro state predecessors admin =>
        intro equal current path
        refine Acc.intro state ?_
        intro next step
        have nextFormed := SourceFormed.update current step
        have nextPath := B4Target.Steps.tail path step
        rcases formed_step_cases current step with passive | ⟨packet,support,generated,enabled,novel,guard,rfl⟩
        · have weak := remaining_monotone cover.basis (step_shared step)
          rcases Nat.lt_or_eq_of_le weak with strict | same
          · exact ih _ (equal ▸ strict) next rfl nextFormed nextPath
          · exact admin next passive (same.trans equal) nextFormed nextPath
        · obtain ⟨signature,member,represents⟩ := cover.covers state path packet support generated enabled novel guard
          have strict := remaining_decreases cover.basis (step_shared step) member
            (novel_signature enabled novel represents) (installed_signature represents support)
          exact ih _ (equal ▸ strict) _ rfl nextFormed nextPath
  exact all _ start rfl formed .refl

def signatureCover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit) : SignatureCover registry root (initial context root) where
  basis := (GeneralNominalPacketCodes.codes context registry (GeneralNominalOccurrenceEnumeration.checkedFor checked source)
    (GeneralNominalOccurrenceEnumeration.basis checked source limit) (pool registry context root limit)).map
      (GeneralNominalPacketCodes.signature context)
  covers := by
    intro state path packet support generated enabled novel guard
    have registrySame := enabled.1.1
    have parent := GeneralNominalOccurrenceEnumeration.sites_enumerated checked source bound path packet.site enabled.1.2.2.1
    have config := configuration_trace path
    rw [← enabled.1.2.1] at config
    have listed : ∀ slot, packet.context.state.base.source slot ∈ pool registry context root limit := by
      rw [enabled.1.2.1]
      exact slot_pool source bound path
    have visible : packet.declaration ∈ packet.registry.declarations := by
      simpa only [registrySame] using enabled.1.2.2.2.1
    have packetChecked : ∀ declaration ∈ packet.registry.declarations,
        DeclarationChecked packet.registry.constructors roles declaration := by
      rw [registrySame]; exact GeneralNominalOccurrenceEnumeration.checkedFor checked source
    have codeMember := GeneralNominalPacketCodes.encoded_member context packet packetChecked parent visible
      enabled.1.2.2.2.2.2.1 listed config.2.1.symm config.2.2.symm
    have represented := GeneralNominalPacketCodes.encode_represents context packet config.1.symm config.2.1.symm config.2.2.symm
    refine ⟨_,?_,represented⟩
    have mapped := (List.mem_map (f := GeneralNominalPacketCodes.signature context)).mpr ⟨_,codeMember,rfl⟩
    subst registry
    exact mapped

theorem accessible_of_installed_depth_bound (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  accessible_of_signature_cover (signatureCover checked source bound) (.initial context source)

/-- Initial pointness concerns literal endpoint identities, including nominal
row parameters. Subsequent certified observations need not remain point pairs. -/
structure PointSource (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Prop where
  intervals : ∀ bounds ∈ context.state.base.intervals, bounds.1 = bounds.2
  nominalTypes : ∀ slot descriptor, context.state.nominals slot = some descriptor →
    ∀ bounds, GeneralNominalState.Parameter.type bounds ∈ descriptor.arguments → bounds.1 = bounds.2
  nominalRows : ∀ slot descriptor, context.state.nominals slot = some descriptor →
    ∀ bounds, GeneralNominalState.Parameter.row bounds ∈ descriptor.arguments → bounds.1 = bounds.2
  rootInputs : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2

/-- The sole open quantitative premise of the Class P theorem. It is a bound
on allocator ancestry of future installing parents, with no report, semantic
cover, refinement-history, or accessibility premise. -/
def ClassPInvocationBound (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root → PointSource context root →
      ∃ limit, InstalledDepthBound registry context root limit

def SourceBudget (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root → PointSource context root →
      Nonempty (SignatureCover registry root (initial context root))

theorem sourceBudget_of_invocation_bound (bounded : ClassPInvocationBound roles) : SourceBudget roles := by
  intro registry checked context root source point
  obtain ⟨limit,bound⟩ := bounded registry checked context root source point
  exact ⟨signatureCover checked source bound⟩

theorem class_p_accessible (bounded : ClassPInvocationBound roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : PointSource context root) :
    Acc (fun next current => Step registry root current next) (initial context root) := by
  obtain ⟨limit,bound⟩ := bounded registry checked context root source point
  exact accessible_of_installed_depth_bound checked source bound

end Yulang.GeneralNominalActualBudget
