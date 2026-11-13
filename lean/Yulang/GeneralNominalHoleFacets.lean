import Yulang.GeneralNominalHoleReadback

/-! Interval endpoints are lattice expressions, not actual captured values.
The computed merge producer introduces no leaf beyond its input endpoints. -/
namespace Yulang.GeneralNominalHoleFacets
open GeneralNominalAllocation GeneralNominalCaptureMerges
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

inductive Facet (α : Type) where
  | leaf (name : α)
  | bottom | top
  | join (first last : Facet α)
  | meet (first last : Facet α)

def Facet.eval (assignment : α → Ty) : Facet α → Ty
  | .leaf name => assignment name
  | .bottom => .bottom
  | .top => .top
  | .join first last => .union (first.eval assignment) (last.eval assignment)
  | .meet first last => .inter (first.eval assignment) (last.eval assignment)

def Facet.leaves : Facet α → List α
  | .leaf name => [name]
  | .bottom | .top => []
  | .join first last | .meet first last => first.leaves ++ last.leaves

def Facet.bind (substitution : α → Facet β) : Facet α → Facet β
  | .leaf name => substitution name
  | .bottom => .bottom
  | .top => .top
  | .join first last => .join (first.bind substitution) (last.bind substitution)
  | .meet first last => .meet (first.bind substitution) (last.bind substitution)

theorem leaves_bind (term : Facet α) (substitution : α → Facet β) (leaf : β) :
    leaf ∈ (term.bind substitution).leaves ↔
      ∃ name ∈ term.leaves, leaf ∈ (substitution name).leaves := by
  induction term with
  | leaf => simp [Facet.bind,Facet.leaves]
  | bottom => simp [Facet.bind,Facet.leaves]
  | top => simp [Facet.bind,Facet.leaves]
  | join first last one two | meet first last one two =>
      simp only [Facet.bind,Facet.leaves,List.mem_append,one,two]
      constructor
      · rintro (⟨name,present,leaf⟩ | ⟨name,present,leaf⟩)
        · exact ⟨name,Or.inl present,leaf⟩
        · exact ⟨name,Or.inr present,leaf⟩
      · rintro ⟨name,one | two,leaf⟩
        · exact Or.inl ⟨name,one,leaf⟩
        · exact Or.inr ⟨name,two,leaf⟩

theorem eval_bind (term : Facet α) (substitution : α → Facet β)
    (before : α → Ty) (after : β → Ty)
    (same : ∀ name ∈ term.leaves, Equivalent (before name) ((substitution name).eval after)) :
    Equivalent (term.eval before) ((term.bind substitution).eval after) := by
  induction term with
  | leaf name => exact same name (by simp [Facet.leaves])
  | bottom | top => exact ⟨subtype_refl _,subtype_refl _⟩
  | join first last one two =>
      have a := one (fun name present => same name (List.mem_append_left _ present))
      have b := two (fun name present => same name (List.mem_append_right _ present))
      exact ⟨common_union_mono a.1 b.1,common_union_mono a.2 b.2⟩
  | meet first last one two =>
      have a := one (fun name present => same name (List.mem_append_left _ present))
      have b := two (fun name present => same name (List.mem_append_right _ present))
      exact ⟨common_inter_mono a.1 b.1,common_inter_mono a.2 b.2⟩

def lowerFacet : List GeneralSourceState.Interval → Facet Nat
  | [] => .bottom
  | [pair] => .leaf pair.1
  | pair :: rest => .join (.leaf pair.1) (lowerFacet rest)

def upperFacet : List GeneralSourceState.Interval → Facet Nat
  | [] => .top
  | [pair] => .leaf pair.2
  | pair :: rest => .meet (.leaf pair.2) (upperFacet rest)

theorem lower_eval (bounds : List GeneralSourceState.Interval) (model : Assignment) :
    (lowerFacet bounds).eval (fun identity => (model identity).1) =
      (lower bounds).eval CommonNominalFullCarrier.model model := by
  induction bounds with
  | nil => rfl
  | cons first rest ih => cases rest <;> simp_all [lowerFacet,lower,Facet.eval,TyTerm.eval] <;> rfl

theorem upper_eval (bounds : List GeneralSourceState.Interval) (model : Assignment) :
    (upperFacet bounds).eval (fun identity => (model identity).1) =
      (upper bounds).eval CommonNominalFullCarrier.model model := by
  induction bounds with
  | nil => rfl
  | cons first rest ih => cases rest <;> simp_all [upperFacet,upper,Facet.eval,TyTerm.eval] <;> rfl

theorem endpoint_leaves (bounds : List GeneralSourceState.Interval) :
    (lowerFacet bounds).leaves = bounds.map Prod.fst ∧
      (upperFacet bounds).leaves = bounds.map Prod.snd := by
  induction bounds with
  | nil => exact ⟨rfl,rfl⟩
  | cons first rest ih =>
      cases rest <;> simp_all [lowerFacet,upperFacet,Facet.leaves]

/-- This covers every multiplicity, including reused singleton endpoints.
For repeated captures it reads the actual generated join/meet equations. -/
theorem capture_endpoints (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
    (invocation : Nat) (declaration : GeneralDeclarations.Declaration) (bindings : Bindings)
    (name : Nat) (declared : name ∈ declaration.inputNames) (model : Assignment)
    (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration bindings)) :
    Equivalent (model ((capture state registry invocation declaration.id bindings).inputs name).1).1
      ((lowerFacet (occurrences bindings name)).eval (fun identity => (model identity).1)) ∧
    Equivalent (model ((capture state registry invocation declaration.id bindings).inputs name).2).1
      ((upperFacet (occurrences bindings name)).eval (fun identity => (model identity).1)) := by
  rw [lower_eval,upper_eval]
  by_cases singleton : ∃ pair, occurrences bindings name = [pair]
  · obtain ⟨pair,equal⟩ := singleton
    simp only [capture,equal,lower,upper,TyTerm.eval]
    exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩
  · have equations : PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.equations ((capture state registry invocation declaration.id bindings).inputs name).1
          (lower (occurrences bindings name)) ++
         GeneralNominalAllocation.equations ((capture state registry invocation declaration.id bindings).inputs name).2
          (upper (occurrences bindings name))) := by
      intro atom member
      apply valid atom
      apply List.mem_flatMap.mpr
      refine ⟨name,declared,?_⟩
      cases found : occurrences bindings name with
      | nil => simpa only [found] using member
      | cons first rest =>
          cases rest with
          | nil => exact False.elim (singleton ⟨first,found⟩)
          | cons second tail => simpa only [found] using member
    have pair := (PresenceNormalForm.all_append ..).mp equations
    exact ⟨(equations_exact ..).mp pair.1,(equations_exact ..).mp pair.2⟩

def Over (models : Assignment → Prop) (basis : List Nat) (identity : Nat) (term : Facet Nat) : Prop :=
  (∀ model, models model → Equivalent (model identity).1 (term.eval (fun name => (model name).1))) ∧
    ∀ name ∈ term.leaves, name ∈ basis

theorem compose (readback : Over models middle identity term) (substitution : Nat → Facet Nat)
    (represented : ∀ name ∈ middle, Over models basis name (substitution name)) :
    Over models basis identity (term.bind substitution) := by
  constructor
  · intro model valid
    have one := readback.1 model valid
    have two := eval_bind term substitution (fun name => (model name).1) (fun name => (model name).1)
      (fun name member => (represented name (readback.2 name member)).1 model valid)
    exact ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩
  · intro name member
    obtain ⟨prior,present,member⟩ := (leaves_bind term substitution name).mp member
    exact (represented prior (readback.2 prior present)).2 name member

theorem packet_endpoints (packet : GeneralNominalSaturationState.Packet roles)
    (name : Nat) (declared : name ∈ packet.declaration.inputNames) :
    Over (GeneralNominalPacketSupport.Inputs packet)
      ((occurrences packet.bindings name).map Prod.fst)
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 (lowerFacet (occurrences packet.bindings name)) ∧
    Over (GeneralNominalPacketSupport.Inputs packet)
      ((occurrences packet.bindings name).map Prod.snd)
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 (upperFacet (occurrences packet.bindings name)) := by
  have exactness (model : Assignment) (valid : GeneralNominalPacketSupport.Inputs packet model) :=
    capture_endpoints packet.context.state packet.registry packet.site.occurrence.identity packet.declaration
      packet.bindings name declared model valid.1.2.1
  exact ⟨⟨fun model valid => (exactness model valid).1,by rw [(endpoint_leaves _).1]; exact fun _ member => member⟩,
    ⟨fun model valid => (exactness model valid).2,by rw [(endpoint_leaves _).2]; exact fun _ member => member⟩⟩

end Yulang.GeneralNominalHoleFacets
