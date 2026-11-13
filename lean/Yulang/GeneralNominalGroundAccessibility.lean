import Yulang.GeneralNominalStructuralContainment
import Yulang.GeneralNominalPatersonLineage

/-! A local ground-input production obligation suffices for every actual
trace. Labels are retrospective and need not be shared by different models.
No elimination history or bound on output trees is required by this reduction. -/
namespace Yulang.GeneralNominalGroundAccessibility
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalReadbackFunctionality GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open GeneralNominalPatersonLineage (mass)

def ClosedTerm (context : GeneralNominalCandidates.Context) (pattern : Pattern) (term : Expr Nat) : Prop :=
  GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern) = quote term ∧
    term.leaves = [] ∧ Canonical term

def Inputs (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (site : GeneralNominalDemandMerging.Site roles) (labels : List Pattern) : Prop :=
  ∃ length : labels.length = (roles site.occurrence.demand.role).arity,
    ∀ index : Fin (roles site.occurrence.demand.role).arity, ∃ term,
      ClosedTerm context (labels[index.val]'(by rw [length]; exact index.isLt)) term ∧
      GeneralNominalCaptureMerges.Fits model (site.occurrence.demand.arguments index) (denote (fun _ => .bottom) term) ∧
      ∀ origin, site.inputs[index.val]? = some (some origin) →
        GeneralNominalFiniteMeaning.At model .actual origin (denote (fun _ => .bottom) term)

def GroundRoots (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (labels : List Pattern) : Prop :=
  ∃ length : labels.length = (roles root.demand.role).arity,
    ∀ index : Fin (roles root.demand.role).arity, ∃ term,
      ClosedTerm context (labels[index.val]'(by rw [length]; exact index.isLt)) term ∧
      ∀ model, GeneralNominalState.Models context.state model →
        CommonNominalFullCarrier.Equivalent (model (root.demand.arguments index).1).1 (denote (fun _ => .bottom) term)

theorem root_inputs {roles : Roles.RoleDecls} {root : Occurrence roles} (ground : GroundRoots context root labels)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    Inputs context model (GeneralNominalDemandMerging.pointSite root) labels := by
  obtain ⟨length,terms⟩ := ground
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,meaning⟩ := terms index
  have equal := meaning model valid
  refine ⟨term,closed,⟨equal.1,?_⟩,?_⟩
  · change CommonNominalFullCarrier.Subtype _ (model (root.demand.arguments index).2).1
    rw [← point index]; exact equal.2
  · intro origin recorded
    have identity : Origin.source (root.demand.arguments index).1 = origin := by
      change Fin (roles root.demand.role).arity at index
      simp only [GeneralNominalDemandMerging.pointSite,List.getElem?_ofFn] at recorded
      split at recorded
      · rename_i bounded
        have same : (⟨index.val,bounded⟩ : Fin (roles root.demand.role).arity) = index := Fin.ext rfl
        rw [same] at recorded
        simpa only [ite_eq_left (point index),Option.some.injEq] using recorded
      · rename_i absent
        exact False.elim (absent index.isLt)
    subst origin
    refine ⟨⟨_,.source _⟩,?_⟩
    intro value seen
    cases seen
    exact equal

/-- The remaining local source bridge. It supplies a finite capture and
actual child meanings, but no trace, depth, cover or numerical budget. The
head comparison allows a syntactic presentation smaller than its input. -/
def GroundPacketProduction (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) : Prop :=
  ∀ (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)),
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    GeneralNominalActualInspectionSteps.PacketGuard state packet support →
    packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels →
      ∃ capture : Nat → Pattern,
        mass (substArgs capture packet.declaration.head) ≤ mass labels ∧
        ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
          Inputs context model
            (GeneralNominalSharedEmission.childSite packet (GeneralNominalFeedbackSites.clauseChild packet clause signature))
            (substArgs capture clause.arguments)

theorem sites_bounded (production : GroundPacketProduction roles registry context)
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
        obtain ⟨capture,headBound,children⟩ := production before packet support config.2.1 config.2.2
          enabled guard nonempty model oldValid branch labels parentInputs
        refine ⟨depth+1,substArgs capture clause.arguments,.child parent successor,
          children clause present signature,?_⟩
        have strict := (checked_child_descent packet.checked clause present capture).1
        change mass (substArgs capture clause.arguments) < mass (substArgs capture packet.declaration.head) at strict
        omega

theorem installed_depth_bound (production : GroundPacketProduction roles registry context)
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
    (production : GroundPacketProduction roles registry context) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound production source point.rootInputs ground)

end Yulang.GeneralNominalGroundAccessibility
