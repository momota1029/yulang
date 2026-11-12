import Yulang.GeneralDictionaryScalarLeaf
import Yulang.GeneralNominalAssociatedSourceTransport

/-! Depth-two nominal linear heads. Intermediate point bounds identify the
inner semantic source; final captured intervals remain arbitrary. -/
namespace Yulang.GeneralNominalNestedLinearFacts
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open CommonNominalFullCarrier

structure NestedShape (context : Context) (declaration : Declaration) where
  outer : Fin context.state.base.slots
  inner : Fin context.state.base.slots
  outerDescriptor : GeneralNominalState.Descriptor context.state.base.slots
  innerDescriptor : GeneralNominalState.Descriptor context.state.base.slots
  outerRecorded : context.state.nominals outer = some outerDescriptor
  innerRecorded : context.state.nominals inner = some innerDescriptor
  outerParameters : outerDescriptor.arguments = [.type (inner,inner)]
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds context.state
  innerParameters : innerDescriptor.arguments = List.ofFn fun i => .type (bounds i)
  query : GeneralNominalInspection.queries context.state context.interpretation declaration =
    [.nominal outerDescriptor.declaration.name
      [.nominal innerDescriptor.declaration.name (List.ofFn fun i => .variables [names i])]]

def parentOrigin (context : Context) (shape : NestedShape context declaration) : Origin :=
  .nominal (.source (context.state.base.source shape.outer)) shape.outerDescriptor.declaration.name 0

def nestedOrigin (context : Context) (shape : NestedShape context declaration) (i : Nat) : Origin :=
  .nominal (parentOrigin context shape) shape.innerDescriptor.declaration.name i

def nestedReport (context : Context) (shape : NestedShape context declaration) : Report context.state :=
  { variablesReport context.state shape.names shape.bounds (nestedOrigin context shape) 0 with
    inspected := [(shape.outer,shape.outer),(shape.inner,shape.inner)]
    checked := [(shape.outer,shape.outer),(shape.outer,shape.outer),(shape.inner,shape.inner)] ++ List.ofFn shape.bounds
    anchors := (parentOrigin context shape,(shape.inner,shape.inner)) ::
      (variablesReport context.state shape.names shape.bounds (nestedOrigin context shape) 0).anchors
    tests := [(parentOrigin context shape,.nominal shape.innerDescriptor.declaration.name shape.arity)] }

theorem report_exact (context : Context) (declaration : Declaration) (shape : NestedShape context declaration) :
    report context declaration [(shape.outer,shape.outer)] = nestedReport context shape := by
  have outerArguments : typeArguments shape.outerDescriptor.arguments = some [(shape.inner,shape.inner)] := by
    rw [shape.outerParameters]; rfl
  unfold report
  rw [shape.query]
  simp only [inspectMany,inspect,shape.outerRecorded,shape.innerRecorded,outerArguments,
    shape.innerParameters,typeArguments_exact,↓reduceIte,Option.getD_none,Option.getD_some]
  rw [inspectMany_exact]
  simp [nestedReport,variablesReport,parentOrigin,nestedOrigin,Report.visit,Report.append]

theorem parent_models (context : Context) (declaration : Declaration) (shape : NestedShape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    (∃ actual, Observes model (parentOrigin context shape) actual) ∧
    ∀ actual, Observes model (parentOrigin context shape) actual →
      Equivalent actual (model (context.state.base.source shape.inner)).1 := by
  have p := nominal_argument_bounds context.state model valid shape.outer shape.outerDescriptor shape.outerRecorded 0
    (shape.inner,shape.inner) (by rw [shape.outerParameters]; rfl)
  refine ⟨p.1,?_⟩
  intro a ha
  have bounds := p.2 a ha
  exact ⟨bounds.2,bounds.1⟩

theorem nested_observation_iff (context : Context) (declaration : Declaration) (shape : NestedShape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model)
    (i : Nat) (actual : Ty) :
    Observes model (nestedOrigin context shape i) actual ↔
      Observes model (.nominal (.source (context.state.base.source shape.inner)) shape.innerDescriptor.declaration.name i) actual := by
  have p := parent_models context declaration shape model valid
  constructor
  · intro seen
    cases seen with
    | nominal parent eq found =>
      have same := p.2 _ parent
      exact .nominal (.source _) ⟨subtype_trans same.2 eq.1,subtype_trans eq.2 same.1⟩ found
  · intro seen
    cases seen with
    | nominal parent eq found =>
      cases parent
      obtain ⟨a,ha⟩ := p.1
      have same := p.2 a ha
      exact .nominal ha ⟨subtype_trans same.1 eq.1,subtype_trans eq.2 same.2⟩ found

theorem nested_argument_bounds (context : Context) (declaration : Declaration) (shape : NestedShape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model)
    (i : Fin shape.arity) :
    (∃ a, Observes model (nestedOrigin context shape i.val) a) ∧
    ∀ a, Observes model (nestedOrigin context shape i.val) a → Fits context.state model (shape.bounds i) a := by
  have arg := nominal_argument_bounds context.state model valid shape.inner shape.innerDescriptor shape.innerRecorded i.val
    (shape.bounds i) (by rw [shape.innerParameters]; simp [i.isLt])
  constructor
  · obtain ⟨a,seen⟩ := arg.1
    exact ⟨a,(nested_observation_iff context declaration shape model valid i.val a).mpr seen⟩
  · intro a seen
    exact arg.2 a ((nested_observation_iff context declaration shape model valid i.val a).mp seen)

theorem projection_models (context : Context) (declaration : Declaration) (shape : NestedShape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    ProjectionModels context.state (nestedReport context shape) model := by
  have parent := parent_models context declaration shape model valid
  have arg := nested_argument_bounds context declaration shape model valid
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | tail
    · refine ⟨parent.1,?_⟩
      intro a ha
      exact ⟨(parent.2 a ha).2,(parent.2 a ha).1⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp tail
      simpa only [Nat.zero_add] using arg i
  · intro test member actual seen
    have eq := List.mem_singleton.mp member
    subst test
    obtain ⟨values,fit,equal⟩ := valid.2.1 shape.inner shape.innerDescriptor shape.innerRecorded
    refine ⟨values,?_,?_⟩
    · rw [fitsAll_length context.state.base model shape.innerDescriptor.arguments values fit,shape.innerParameters]
      exact List.length_ofFn
    · have same := parent.2 actual seen
      exact ⟨subtype_trans same.1 equal.1,subtype_trans equal.2 same.2⟩
  · intro a ha b hb same origin found actual seen
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := shape.distinct same
    subst j
    cases Option.some.inj found
    exact (arg i).2 actual (by simpa only [Nat.zero_add] using seen)
  · intro a ha b hb same x y hx hy u v hu hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := shape.distinct same
    subst j
    cases Option.some.inj hx
    cases Option.some.inj hy
    exact nominal_observation_unique model
      (.argument (.argument (.source (context.state.base.source shape.outer)) shape.outerDescriptor.declaration.name 0)
        shape.innerDescriptor.declaration.name i.val) u v
      (by simpa only [Nat.zero_add,embed,nestedOrigin,parentOrigin] using hu)
      (by simpa only [Nat.zero_add,embed,nestedOrigin,parentOrigin] using hv)

theorem private_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (shape : NestedShape context declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(shape.outer,shape.outer)]) model ∧
    ProjectionModels context.state (report context declaration [(shape.outer,shape.outer)]) model := by
  have fits := nested_argument_bounds context declaration shape model valid
  have bounds (i : Fin shape.arity) : Subtype (model (context.state.base.source (shape.bounds i).1)).1
      (model (context.state.base.source (shape.bounds i).2)).1 := by
    obtain ⟨a,ha⟩ := (fits i).1
    exact subtype_trans ((fits i).2 a ha).1 ((fits i).2 a ha).2
  constructor
  · unfold privateState
    rw [report_exact context declaration shape]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · simpa only [bindings,nestedReport,variablesReport,List.map_ofFn,Function.comp_def] using
        propagated_models context.state registry root.identity declaration shape.names shape.distinct shape.inputs
          shape.bounds model valid bounds
    · intro atom member
      obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
      simp only [nestedReport,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with (rfl | rfl | rfl) | tail
      · exact subtype_refl _
      · exact subtype_refl _
      · exact subtype_refl _
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp tail
        exact bounds i
  · rw [report_exact context declaration shape]
    exact projection_models context declaration shape model valid
end Yulang.GeneralNominalNestedLinearFacts
