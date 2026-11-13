import Yulang.GeneralNominalGroundReachable
import Yulang.GeneralPatternConservativeSubstitution

/-! The actual emitter consumes normalized templates. This reduction uses
that same boundary and the conservative checker, including erased raw joins. -/
namespace Yulang.GeneralNominalNormalizedGround
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalReadbackFunctionality GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalGroundAccessibility
open GeneralNominalPatersonLineage (mass)

/-- The remaining local source bridge. It supplies a finite capture and
actual child meanings, but no trace, depth, cover or numerical budget. The
head comparison allows a syntactic presentation smaller than its input. -/
def NormalizedProduction (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Prop :=
  ∀ (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)),
    B4Target.Steps (Step registry root) (initial context root) state →
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    GeneralNominalActualInspectionSteps.PacketGuard state packet support →
    packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels →
      ∃ capture : Nat → Pattern,
        mass (substArgs capture (normalizeArgs packet.declaration.head)) ≤ mass labels ∧
        ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
          Inputs context model
            (GeneralNominalSharedEmission.childSite packet (GeneralNominalFeedbackSites.clauseChild packet clause signature))
            (substArgs capture (normalizeArgs clause.arguments))

theorem sites_bounded (production : NormalizedProduction roles registry context root)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels)
    (steps : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ model, Models state.current model → ∀ site ∈ state.current.sites,
      ∃ depth labels, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        Inputs context model site labels ∧ depth + mass labels ≤ mass rootLabels := by
  induction steps with
  | refl =>
    intro model valid site member
    cases List.mem_singleton.mp member
    exact ⟨0,rootLabels,.root,root_inputs ground point model valid.1,by omega⟩
  | @tail before after steps step ih =>
    have formed := formed_trace (.initial context source) steps
    have restrict := GeneralNominalSharedSteps.step_models (step_shared step)
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve =>
        intro model valid site member
        exact ih model (restrict model valid) site member
    | merge =>
      intro model valid site member
      exact ih model (restrict model valid) site member
    | install packet support enabled novel guard =>
      intro model valid site member
      have oldValid := restrict model valid
      have config := configuration_trace steps
      have branch := valid.2.1 packet (List.mem_cons_self ..)
      obtain ⟨depth,labels,parent,parentInputs,bounded⟩ := ih model oldValid packet.site enabled.1.2.2.1
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih model oldValid site old
      · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp added
        have visible : packet.declaration ∈ packet.registry.declarations := by
          simpa only [enabled.1.1] using enabled.1.2.2.2.1
        have seed : packet.context.state.seed = context.state.seed := by rw [enabled.1.2.1]; exact config.1
        have successor := child_identity packet child childMember visible
        rw [enabled.1.1,seed] at successor
        obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child childMember
        have nonempty : packet.declaration.requirements ≠ [] := by
          intro empty; rw [empty] at present; cases present
        obtain ⟨capture,headBound,children⟩ := production before packet support steps config.2.1 config.2.2
          enabled guard nonempty model oldValid branch labels parentInputs
        refine ⟨depth+1,substArgs capture (normalizeArgs clause.arguments),.child parent successor,
          children clause present signature,?_⟩
        have strict := GeneralPatternConservativeSubstitution.checked_normalized_descent packet.checked clause present capture
        change mass (substArgs capture (normalizeArgs clause.arguments)) < mass (substArgs capture (normalizeArgs packet.declaration.head)) at strict
        omega

theorem installed_depth_bound (production : NormalizedProduction roles registry context root)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels) :
    InstalledDepthBound registry context root (mass rootLabels) := by
  intro state steps packet support generated enabled novel guard
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded production source point ground steps
    model valid packet.site enabled.1.2.2.1
  exact ⟨depth,by omega,ancestry⟩

theorem ground_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels)
    (production : NormalizedProduction roles registry context root) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound production source point.rootInputs ground)

def NormalizedCaptureFactorization (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Prop :=
  ∀ (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles) (support : List (GeneralSourceDictionaries.Occurrence roles)),
    B4Target.Steps (Step registry root) (initial context root) state →
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    GeneralNominalActualInspectionSteps.PacketGuard state packet support →
    packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels →
      ∃ capture : Nat → Pattern,
        GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs packet.declaration.head)) ≤
          GeneralNominalPatersonLineage.mass labels ∧
        ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
          ∃ length : (substArgs capture (normalizeArgs clause.arguments)).length = (roles clause.role).arity,
            ∀ index : Fin (roles clause.role).arity, ∃ term,
              ClosedTerm context ((substArgs capture (normalizeArgs clause.arguments))[index.val]'(by rw [length]; exact index.isLt)) term ∧
              GeneralNominalGroundProduction.ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term)

theorem packet_production (factorization : NormalizedCaptureFactorization roles registry context root) :
    NormalizedProduction roles registry context root := by
  intro state packet support trace constructors interpretation enabled guard nonempty model valid branch labels inputs
  obtain ⟨capture,bounded,children⟩ := factorization state packet support trace constructors interpretation
    enabled guard nonempty model valid branch labels inputs
  refine ⟨capture,bounded,?_⟩
  intro clause present signature
  obtain ⟨length,meanings⟩ := children clause present signature
  exact GeneralNominalGroundProduction.child_inputs packet guard.1.2.2.2 model branch clause present signature length meanings

theorem accessible_of_reachable_factorization (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels)
    (factorization : NormalizedCaptureFactorization roles registry context root) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  ground_accessible checked source point ground (packet_production factorization)

end Yulang.GeneralNominalNormalizedGround
