import Yulang.GeneralVersionedFirstComputed313

set_option backward.isDefEq.respectTransparency false
/-! Actual source compilation pairs the clause address with its local
equation ID. Raw per-clause uniqueness therefore suffices for the entire
first-install certificate: no extra where/output restriction is needed. -/
namespace Yulang.GeneralVersionedCompiledFirstInstall313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedComputedRows313 (KeyCoherent)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalCenteredHeadAllocEncoding (declaration clause equation equation_key)

theorem compiled_outputs_unique (d : Declaration) (unique : d.Identified) :
    ∀ first ∈ (declaration d).requirements, ∀ a ∈ first.outputs,
      ∀ last ∈ (declaration d).requirements, ∀ b ∈ last.outputs, a.id = b.id → a = b := by
  intro first hf a ha last hl b hb keys
  obtain ⟨c,required,rfl⟩ := List.mem_map.mp hf
  obtain ⟨dcl,other,rfl⟩ := List.mem_map.mp hl
  obtain ⟨one,oneIn,rfl⟩ := List.mem_map.mp ha
  obtain ⟨two,twoIn,rfl⟩ := List.mem_map.mp hb
  have decoded : c.id = dcl.id ∧ one.id = two.id := equation_key.mp keys
  have equal := GeneralVersionedCompoundRows313.key_unique Clause.id _ unique.1 c dcl required other decoded.1
  subst dcl
  have same := GeneralVersionedCompoundRows313.key_unique GeneralDeclarations.Equation.id _
    (unique.2.2.2.2 c required) one two oneIn twoIn decoded.2
  rw [same]

theorem key_coherence (checked : Checked registry) (listed : d ∈ (Compiled registry).declarations) :
    KeyCoherent d := by
  obtain ⟨source,visible,rfl⟩ := List.mem_map.mp listed
  intro c hc a ha _ d hd b hb _ eq
  exact congrArg GeneralDeclarations.Equation.rhs
    (compiled_outputs_unique source (checked.2 source visible).identified c hc a ha d hd b hb eq)

theorem joint {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) : ∃ m, Residual s e m := by
  have visible : e.plan.packet.declaration ∈ (Compiled registry).declarations := registryEq ▸ e.frame.visible
  exact GeneralVersionedFirstComputed313.joint checked actual empty pick registryEq snapshot inhabited
    (key_coherence checked.2 visible)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e := by
  have visible : e.plan.packet.declaration ∈ (Compiled registry).declarations := registryEq ▸ e.frame.visible
  exact GeneralVersionedFirstComputed313.installable checked actual empty pick registryEq snapshot inhabited
    (key_coherence checked.2 visible)


/-- Closes the no-prior-installation branch of the same-model recursive
evidence argument. The induction hypothesis is the actual ordered children,
not separate assignment witnesses. -/
theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (empty : s.plans = [])
    (picked : Local registry s focus (.selected key kids))
    (stable : (boundary roles).Stable registry s focus)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated s.core.erased.current root focus)
    (valid : Models s m)
    (ordered : CommonRoleOutermostResolver.All₂
      (GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core m) kids dictionaries) :
    GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core m focus (.node key dictionaries) ∧
    ∀ child ∈ kids, GeneralNominalSaturationState.Generated s.core.erased.current root child := by
  obtain ⟨e,registryEq,snapshot,focusEq,keyEq,childrenEq⟩ :=
    GeneralNominalVersionedMixedSelectedEffect235.source_effect checked actual picked
  have exactPick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [focusEq,keyEq]
    exact picked
  have enabled := installable checked actual empty exactPick registryEq snapshot ⟨m,valid⟩
  have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked
  exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled focusEq mixed valid ordered,
    fun _ h => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled focusEq mixed reached h⟩

end Yulang.GeneralVersionedCompiledFirstInstall313
