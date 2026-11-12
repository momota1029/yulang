import Yulang.GeneralNominalProjectionPropagation

/-! An additive provenance sidecar for the existing child-emission interface.
Entries are keyed by allocated occurrence and argument position, never by an
endpoint pair. All associated outputs remain in the original emission. This
retention bridge is not a complete compound-input materializer. -/
namespace Yulang.GeneralNominalEmissionOrigins

open GeneralNominalProjections
open GeneralDeclarationDemands
open GeneralDeclarationPatterns
open GeneralDeclarations

structure InputOrigin where
  occurrence : Nat
  position : Nat
  endpoints : GeneralSourceState.Interval
  origin : Ref
  deriving DecidableEq

def occurrence (state : GeneralNominalState.State) (registry : Registry)
    (emission : Emission roles) : Nat :=
  GeneralNominalAllocation.source state registry emission.invocation
    (GeneralNominalAllocation.origin emission.invocation emission.declaration 6 emission.clause 0)

def requestOrigins (identity : Nat) (request : InputRequest) (bindings : List (Binding state)) :
    List InputOrigin :=
  match normalize request.pattern with
  | .var name => (bindings.filter fun binding => binding.name == name).map fun binding =>
      ⟨identity,request.position,request.endpoints,binding.origin⟩
  | _ => []

def origins (state : GeneralNominalState.State) (registry : Registry)
    (emission : Emission roles) (bindings : List (Binding state)) : List InputOrigin :=
  emission.inputs.flatMap fun request => requestOrigins (occurrence state registry emission) request bindings

structure Annotated (roles : Roles.RoleDecls) where
  emission : Emission roles
  inputOrigins : List InputOrigin

def annotate (state : GeneralNominalState.State) (registry : Registry)
    (emission : Emission roles) (bindings : List (Binding state)) : Annotated roles :=
  ⟨emission,origins state registry emission bindings⟩

theorem annotation_erases (state : GeneralNominalState.State) (registry : Registry)
    (emission : Emission roles) (bindings : List (Binding state)) :
    (annotate state registry emission bindings).emission = emission := rfl

theorem request_origin_exact (identity : Nat) (request : InputRequest)
    (bindings : List (Binding state)) (entry : InputOrigin) :
    entry ∈ requestOrigins identity request bindings ↔
      ∃ name, normalize request.pattern = .var name ∧
        ∃ binding ∈ bindings, binding.name = name ∧
          entry = ⟨identity,request.position,request.endpoints,binding.origin⟩ := by
  cases h : normalize request.pattern with
  | var name =>
      simp only [requestOrigins,h,List.mem_map,List.mem_filter,beq_iff_eq,Pattern.var.injEq]
      constructor
      · rintro ⟨binding,⟨present,same⟩,equal⟩
        exact ⟨name,rfl,binding,present,same,equal.symm⟩
      · rintro ⟨_,rfl,binding,present,same,equal⟩
        exact ⟨binding,⟨present,same⟩,equal.symm⟩
  | app | record | variant | join => simp [requestOrigins,h]

theorem emitted_input_origin (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (bindings : List (Binding state)) (index : Fin (roles clause.role).arity)
    (name : Nat) (pattern : normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name)
    (binding : Binding state) (member : binding ∈ bindings) (same : binding.name = name) :
    let emission := emit invocation declaration clause valid capture allocation
    (emission.demand.arguments index = capture.inputs name) ∧
      (⟨occurrence state registry emission,index.val,capture.inputs name,binding.origin⟩ : InputOrigin) ∈
        origins state registry emission bindings := by
  dsimp only
  have endpoints : (childDemand declaration clause valid capture allocation).arguments index = capture.inputs name := by
    simp only [childDemand,inputInterval,pattern]
  refine ⟨endpoints,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨index.val,clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt),capture.inputs name⟩,?_,?_⟩
  · apply List.mem_ofFn.mpr
    exact ⟨index,by simp only [endpoints]⟩
  · apply (request_origin_exact ..).mpr
    exact ⟨name,pattern,binding,member,same,rfl⟩

theorem origin_has_observation (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (registry : Registry) (emission : Emission roles)
    (bindings : List (Binding state)) (compatible : Compatible state model bindings)
    (entry : InputOrigin) (member : entry ∈ origins state registry emission bindings) :
    entry.occurrence = occurrence state registry emission ∧
      ∃ value, Observes model entry.origin value := by
  obtain ⟨request,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨_,_,binding,present,_,rfl⟩ := (request_origin_exact ..).mp member
  obtain ⟨value,observed,_⟩ := compatible.1 binding present
  exact ⟨rfl,value,observed⟩

theorem occurrence_registry_independent (state : GeneralNominalState.State)
    (first last : Registry) (emission : Emission roles) :
    occurrence state first emission = occurrence state last emission := rfl

/-- For a single captured type occurrence the actual computed frame retains
the interval, so its where input inherits the projection bounds. Repeated
capture merging requires a further correspondence proof. -/
theorem single_capture_child_bounds (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (clause : Clause) (valid : clause.Signature roles)
    (binding : Binding state) (bounds : Fin state.base.slots × Fin state.base.slots)
    (typed : binding.bounds = .type bounds) (fits : binding.Valid state model)
    (index : Fin (roles clause.role).arity)
    (pattern : normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var binding.name) :
    let capture := GeneralNominalAllocation.capture state registry invocation declaration.id
      [(binding.name,(state.base.source bounds.1,state.base.source bounds.2))]
    let allocation := GeneralNominalAllocation.allocation state registry invocation declaration.id clause
    let demand := childDemand declaration clause valid capture allocation
    ∃ actual, Observes model binding.origin (.inl actual) ∧
      CommonNominalFullCarrier.Subtype (model (demand.arguments index).1).1 actual ∧
      CommonNominalFullCarrier.Subtype actual (model (demand.arguments index).2).1 := by
  dsimp only
  obtain ⟨value,seen,fits⟩ := fits
  rw [typed] at fits
  cases value with
  | inr => cases fits
  | inl actual =>
      refine ⟨actual,seen,?_⟩
      simpa [childDemand,inputInterval,pattern,GeneralNominalAllocation.capture,
        GeneralNominalAllocation.occurrences,GeneralNominalState.Fits] using fits

end Yulang.GeneralNominalEmissionOrigins
