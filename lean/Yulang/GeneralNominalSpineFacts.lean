import Yulang.GeneralNominalNestedLinearFacts

/-! A finite nominal source spine, not a fixed-depth collection of examples. -/
namespace Yulang.GeneralNominalSpineFacts
open GeneralDeclarations GeneralSourceDictionaries CommonNominalFullCarrier
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts

inductive Spine (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state) : Fin state.base.slots → Type where
  | leaf (slot) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i)) : Spine state names bounds slot
  | wrap (slot child) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = [.type (child,child)])
      (rest : Spine state names bounds child) : Spine state names bounds slot

def Spine.query {state : GeneralNominalState.State} {names : Fin n → Nat} {bounds}
    {slot} : Spine state names bounds slot → GeneralNominalInspection.Query
  | .leaf _ descriptor _ _ => .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])
  | .wrap _ _ descriptor _ _ rest => .nominal descriptor.declaration.name [rest.query]

def Matches (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (slot : Fin state.base.slots) (origin : Origin) : Prop :=
  (∃ a, Observes model origin a) ∧
    ∀ a, Observes model origin a → Equivalent a (model (state.base.source slot)).1

theorem source_matches (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (slot : Fin state.base.slots) : Matches state model slot (.source (state.base.source slot)) := by
  refine ⟨⟨_,.source _⟩,?_⟩
  intro a seen; cases seen
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem nominal_observation_iff (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (slot : Fin state.base.slots) (origin : Origin) (consistentOrigin : Matches state model slot origin)
    (name index : Nat) (actual : Ty) :
    Observes model (.nominal origin name index) actual ↔
      Observes model (.nominal (.source (state.base.source slot)) name index) actual := by
  constructor
  · intro seen
    cases seen with
    | nominal parent eq found =>
      have same := consistentOrigin.2 _ parent
      exact .nominal (.source _) ⟨subtype_trans same.2 eq.1,subtype_trans eq.2 same.1⟩ found
  · intro seen
    cases seen with
    | nominal parent eq found =>
      cases parent
      obtain ⟨a,ha⟩ := consistentOrigin.1
      have same := consistentOrigin.2 a ha
      exact .nominal ha ⟨subtype_trans same.1 eq.1,subtype_trans eq.2 same.2⟩ found

theorem point_child_matches (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot child : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (child,child)])
    (origin : Origin) (consistentOrigin : Matches state model slot origin) :
    Matches state model child (.nominal origin descriptor.declaration.name 0) := by
  have arg := nominal_argument_bounds state model valid slot descriptor recorded 0 (child,child)
    (by rw [parameters]; rfl)
  have transport := nominal_observation_iff state model slot origin consistentOrigin descriptor.declaration.name 0
  constructor
  · obtain ⟨a,ha⟩ := arg.1
    exact ⟨a,(transport a).mpr ha⟩
  · intro a ha
    have fit := arg.2 a ((transport a).mp ha)
    exact ⟨fit.2,fit.1⟩

theorem visit_models (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (arity : Nat) (length : descriptor.arguments.length = arity)
    (origin : Option Origin) (consistentOrigin : ∀ o, origin = some o → Matches state model slot o)
    (r : Report state) (good : ProjectionModels state r model) :
    ProjectionModels state (Report.visit (slot,slot) origin (.nominal descriptor.declaration.name arity) r) model := by
  refine ⟨?_,?_,good.2.2.1,good.2.2.2⟩
  · intro anchor member
    rcases List.mem_append.mp member with extra | old
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp extra
      have eq : origin = some o := by simpa using ho
      have m := consistentOrigin o eq
      exact ⟨m.1,fun a ha => ⟨(m.2 a ha).2,(m.2 a ha).1⟩⟩
    · exact good.1 anchor old
  · intro test member a ha
    rcases List.mem_append.mp member with extra | old
    · obtain ⟨o,ho,rfl⟩ := List.mem_map.mp extra
      have eq : origin = some o := by simpa using ho
      have same := (consistentOrigin o eq).2 a ha
      obtain ⟨values,fit,equal⟩ := valid.2.1 slot descriptor recorded
      exact ⟨values,(fitsAll_length state.base model descriptor.arguments values fit).trans length,
        subtype_trans same.1 equal.1,subtype_trans equal.2 same.2⟩
    · exact good.2.1 test old a ha

theorem variables_models (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (origin : Origin) (consistentOrigin : Matches state model slot origin) :
    ProjectionModels state (variablesReport state names bounds (fun i => .nominal origin descriptor.declaration.name i) 0) model := by
  have arg (i : Fin n) := nominal_argument_bounds state model valid slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  have transport := nominal_observation_iff state model slot origin consistentOrigin descriptor.declaration.name
  have fits (i : Fin n) : (∃ a, Observes model (.nominal origin descriptor.declaration.name i.val) a) ∧
      ∀ a, Observes model (.nominal origin descriptor.declaration.name i.val) a → Fits state model (bounds i) a := by
    constructor
    · obtain ⟨a,ha⟩ := (arg i).1; exact ⟨a,(transport i.val a).mpr ha⟩
    · intro a ha; exact (arg i).2 a ((transport i.val a).mp ha)
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    simpa only [Nat.zero_add] using fits i
  · intro test member; cases member
  · intro a ha b hb same ref found actual seen
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same; subst j
    cases Option.some.inj found
    exact (fits i).2 actual (by simpa only [Nat.zero_add] using seen)
  · intro a ha b hb same x y hx hy u v hu hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same; subst j
    cases Option.some.inj hx; cases Option.some.inj hy
    exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name i.val) u v
      ((transport i.val u).mp (by simpa only [Nat.zero_add] using hu))
      ((transport i.val v).mp (by simpa only [Nat.zero_add] using hv))

theorem append_empty (state : GeneralNominalState.State) (r : Report state) : r.append {} = r := by
  cases r; simp [Report.append]

theorem inspect_leaf (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat) (bounds)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i)) (origin : Option Origin) :
    inspect state (.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])) (slot,slot) origin =
    Report.visit (slot,slot) origin (.nominal descriptor.declaration.name n)
      (variablesReport state names bounds
        (fun i => .nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name i) 0) := by
  simp only [inspect,recorded,parameters,typeArguments_exact,↓reduceIte,List.length_ofFn]
  rw [inspectMany_exact]

theorem inspect_wrap (state : GeneralNominalState.State) (slot child : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    (parameters : descriptor.arguments = [.type (child,child)])
    (query : GeneralNominalInspection.Query) (origin : Option Origin) :
    inspect state (.nominal descriptor.declaration.name [query]) (slot,slot) origin =
    Report.visit (slot,slot) origin (.nominal descriptor.declaration.name 1)
      (inspect state query (child,child)
        (some (.nominal (origin.getD (.source (state.base.source slot))) descriptor.declaration.name 0))) := by
  have args : typeArguments descriptor.arguments = some [(child,child)] := by rw [parameters]; rfl
  simp only [inspect,recorded,args,↓reduceIte,inspectMany,append_empty,List.length_cons,List.length_nil]

theorem origin_default (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (slot : Fin state.base.slots) (origin : Option Origin)
    (consistentOrigin : ∀ o, origin = some o → Matches state model slot o) :
    Matches state model slot (origin.getD (.source (state.base.source slot))) := by
  cases origin with
  | none => exact source_matches state model slot
  | some o => exact consistentOrigin o rfl

/-- Structural induction over an arbitrary finite descriptor spine. All nested
anchor/test and shared-origin projection conditions are derived from the source
model and linear names; no ProjectionModels premise is supplied. -/
theorem spine_projection (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (distinct : Function.Injective names) (bounds) {slot} (spine : Spine state names bounds slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin)
    (consistentOrigin : ∀ o, origin = some o → Matches state model slot o) :
    ProjectionModels state (inspect state spine.query (slot,slot) origin) model := by
  induction spine generalizing origin with
  | leaf slot descriptor recorded parameters =>
    rw [Spine.query,inspect_leaf state names bounds slot descriptor recorded parameters origin]
    exact visit_models state model valid slot descriptor recorded n (by rw [parameters]; exact List.length_ofFn)
      origin consistentOrigin _ (variables_models state model valid slot descriptor recorded names distinct bounds parameters _
        (origin_default state model slot origin consistentOrigin))
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Spine.query,inspect_wrap state slot child descriptor recorded parameters]
    apply visit_models state model valid slot descriptor recorded 1 (by rw [parameters]; rfl) origin consistentOrigin
    apply ih
    intro o eq
    cases Option.some.inj eq
    exact point_child_matches state model valid slot child descriptor recorded parameters _
      (origin_default state model slot origin consistentOrigin)

/-- Exact capture allocation is independent of spine depth and observation
origins. Each linear leaf name still has its one actual interval. -/
theorem spine_bindings (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine state names bounds slot) (origin : Option Origin) :
    bindings state (inspect state spine.query (slot,slot) origin) =
      List.ofFn fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2) := by
  induction spine generalizing origin with
  | leaf slot descriptor recorded parameters =>
    rw [Spine.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    simp [bindings,Report.visit,variablesReport,List.map_ofFn,Function.comp_def]
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Spine.query,inspect_wrap state slot child descriptor recorded parameters]
    exact ih _

theorem spine_finished (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine state names bounds slot) (origin : Option Origin) :
    Finished (inspect state spine.query (slot,slot) origin) := by
  induction spine generalizing origin with
  | leaf slot descriptor recorded parameters =>
    rw [Spine.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    exact ⟨rfl,rfl,rfl⟩
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Spine.query,inspect_wrap state slot child descriptor recorded parameters]
    exact ih _

theorem spine_bounds (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine state names bounds slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) :
    ∀ i, Subtype (model (state.base.source (bounds i).1)).1 (model (state.base.source (bounds i).2)).1 := by
  induction spine with
  | leaf slot descriptor recorded parameters =>
    intro i
    have arg := nominal_argument_bounds state model valid slot descriptor recorded i.val (bounds i)
      (by rw [parameters]; simp [i.isLt])
    obtain ⟨a,ha⟩ := arg.1
    exact subtype_trans (arg.2 a ha).1 (arg.2 a ha).2
  | wrap _ _ _ _ _ _ ih => exact ih

theorem spine_checked (state : GeneralNominalState.State) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine state names bounds slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (origin : Option Origin) :
    ∀ pair ∈ (inspect state spine.query (slot,slot) origin).checked,
      Subtype (model (state.base.source pair.1)).1 (model (state.base.source pair.2)).1 := by
  induction spine generalizing origin with
  | leaf slot descriptor recorded parameters =>
    rw [Spine.query,inspect_leaf state names bounds slot descriptor recorded parameters]
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact subtype_refl _
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp tail
      exact spine_bounds state names bounds (.leaf slot descriptor recorded parameters) model valid i
  | wrap slot child descriptor recorded parameters rest ih =>
    rw [Spine.query,inspect_wrap state slot child descriptor recorded parameters]
    intro pair member
    rcases List.mem_cons.mp member with rfl | tail
    · exact subtype_refl _
    · exact ih _ pair tail

theorem report_exact (context : Context) (declaration : Declaration) {n : Nat} (names : Fin n → Nat)
    (bounds) {slot} (spine : Spine context.state names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [spine.query]) :
    report context declaration [(slot,slot)] =
      { inspect context.state spine.query (slot,slot) none with
        checked := (slot,slot) :: (inspect context.state spine.query (slot,slot) none).checked } := by
  simp [report,query,inspectMany,append_empty]

/-- The complete candidate-private/projection obligations for any finite spine
hold in every unchanged source assignment. -/
theorem private_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names) (bounds) {slot}
    (spine : Spine context.state names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [spine.query])
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have computed := report_exact context declaration names bounds spine query
  have captured : bindings context.state (report context declaration [(slot,slot)]) =
      List.ofFn fun i => (names i,context.state.base.source (bounds i).1,context.state.base.source (bounds i).2) := by
    rw [computed]
    exact spine_bindings context.state names bounds spine none
  constructor
  · unfold privateState
    rw [captured]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · exact propagated_models context.state registry root.identity declaration names distinct inputs bounds model valid
        (spine_bounds context.state names bounds spine model valid)
    · intro atom member
      obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
      rw [computed] at present
      rcases List.mem_cons.mp present with rfl | tail
      · exact subtype_refl _
      · exact spine_checked context.state names bounds spine model valid none pair tail
  · rw [computed]
    exact spine_projection context.state names distinct bounds spine model valid none (by intro o eq; cases eq)
end Yulang.GeneralNominalSpineFacts
