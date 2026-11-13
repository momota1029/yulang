import Yulang.GeneralDictionaryCapturedChildIntervals

/-! Allocation is semantically extensional in the nonempty set of occurrence
bounds, even when singleton-vs-merge selection changes source identities.
Merge atoms on BOTH sides are explicit premises; their current installation is
not inferred merely from historical packet membership. -/
namespace Yulang.GeneralDictionaryCaptureMultiplicity
open GeneralNominalAllocation GeneralNominalCaptureMerges
open GeneralDeclarations
open PresenceNormalForm (All)

/-- Auxiliary semantic equality, not literal capture-source equality. -/
theorem capture_fits_of_membership
    (a b : GeneralNominalState.State) (ra rb : Registry) (ia ib : Nat)
    (da db : Declaration) (xs ys : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat)
    (declaredA : name ∈ da.inputNames) (declaredB : name ∈ db.inputNames)
    (nonempty : occurrences xs name ≠ [])
    (membership : ∀ pair, pair ∈ occurrences xs name ↔ pair ∈ occurrences ys name)
    (mergeA : All CommonNominalFullCarrier.model model (merges a ra ia da xs))
    (mergeB : All CommonNominalFullCarrier.model model (merges b rb ib db ys))
    (actual : CommonNominalFullCarrier.Ty) :
    Fits model ((capture a ra ia da.id xs).inputs name) actual ↔
      Fits model ((capture b rb ib db.id ys).inputs name) actual := by
  have nonemptyB : occurrences ys name ≠ [] := by
    intro empty
    apply nonempty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro pair member
    have := (membership pair).mp member
    simp [empty] at this
  rw [capture_interval_exact a ra ia da xs model mergeA name declaredA nonempty,
    capture_interval_exact b rb ib db ys model mergeB name declaredB nonemptyB]
  exact ⟨fun h p hp => h p ((membership p).mpr hp),
    fun h p hp => h p ((membership p).mp hp)⟩

/-- Removing a second identical occurrence preserves the actual-value interval,
not necessarily the identities of its two endpoints. -/
theorem duplicate_collapse (state : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (pair : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (declared : name ∈ declaration.inputNames)
    (merged : All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration [(name,pair),(name,pair)]))
    (actual : CommonNominalFullCarrier.Ty) :
    Fits model ((capture state registry invocation declaration.id [(name,pair),(name,pair)]).inputs name) actual ↔
      Fits model pair actual := by
  have h := capture_interval_exact state registry invocation declaration
    [(name,pair),(name,pair)] model merged name declared (by simp [occurrences]) actual
  simpa [occurrences] using h

/-- The singleton is not allocated at the merge origin. -/
theorem duplicate_sources_differ (state : GeneralNominalState.State) (registry : Registry)
    (invocation key name : Nat) (pair : GeneralSourceState.Interval)
    (below : pair.1 ≤ state.seed) :
    (capture state registry invocation key [(name,pair),(name,pair)]).inputs name ≠
      (capture state registry invocation key [(name,pair)]).inputs name := by
  intro equal
  have first := congrArg Prod.fst equal
  simp [capture,occurrences] at first
  exact source_initial_fresh state registry invocation _ pair.1 below first

/-- For formed intervals, equality of their Fits sets determines both endpoints
up to the existing semantic type equivalence, not equality of source identities. -/
theorem endpoints_of_fits (model : GeneralNominalCommonBridge.Assignment)
    (a b : GeneralSourceState.Interval)
    (orderedA : CommonNominalFullCarrier.Subtype (model a.1).1 (model a.2).1)
    (orderedB : CommonNominalFullCarrier.Subtype (model b.1).1 (model b.2).1)
    (same : ∀ actual, Fits model a actual ↔ Fits model b actual) :
    CommonNominalFullCarrier.Equivalent (model a.1).1 (model b.1).1 ∧
    CommonNominalFullCarrier.Equivalent (model a.2).1 (model b.2).1 := by
  have al := (same (model a.1).1).mp ⟨CommonNominalFullCarrier.subtype_refl _,orderedA⟩
  have bl := (same (model b.1).1).mpr ⟨CommonNominalFullCarrier.subtype_refl _,orderedB⟩
  have au := (same (model a.2).1).mp ⟨orderedA,CommonNominalFullCarrier.subtype_refl _⟩
  have bu := (same (model b.2).1).mpr ⟨orderedB,CommonNominalFullCarrier.subtype_refl _⟩
  exact ⟨⟨bl.1,al.1⟩,⟨au.2,bu.2⟩⟩

/-- Actual propagation supplies the endpoint-order premises. This handles any
finite multiplicity/permutation change with the same occurrence membership. -/
theorem propagated_endpoints
    (a b : GeneralNominalState.State) (ra rb : Registry) (ia ib : Nat)
    (da db : Declaration) (xs ys : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat)
    (declaredA : name ∈ da.inputNames) (declaredB : name ∈ db.inputNames)
    (nonempty : occurrences xs name ≠ [])
    (membership : ∀ pair, pair ∈ occurrences xs name ↔ pair ∈ occurrences ys name)
    (validA : GeneralNominalState.Models (propagate a ra ia da xs) model)
    (validB : GeneralNominalState.Models (propagate b rb ib db ys) model) :
    let ca := (capture a ra ia da.id xs).inputs name
    let cb := (capture b rb ib db.id ys).inputs name
    CommonNominalFullCarrier.Equivalent (model ca.1).1 (model cb.1).1 ∧
    CommonNominalFullCarrier.Equivalent (model ca.2).1 (model cb.2).1 := by
  dsimp only
  apply endpoints_of_fits
  · exact GeneralDictionaryCapturedChildIntervals.capture_order a ra ia da xs model validA name declaredA
  · exact GeneralDictionaryCapturedChildIntervals.capture_order b rb ib db ys model validB name declaredB
  · exact capture_fits_of_membership a b ra rb ia ib da db xs ys model name declaredA declaredB
      nonempty membership ((propagate_models ..).mp validA).2.2 ((propagate_models ..).mp validB).2.2

/-- In the duplicate-to-singleton direction the new merge constraints are empty.
Current base Models and the OLD propagation suffice; no current propagation
validity is assumed. The one-input declaration scope is explicit. -/
theorem collapse_propagation (a b : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (pair : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (names : declaration.inputNames = [name])
    (old : GeneralNominalState.Models
      (propagate a registry invocation declaration [(name,pair),(name,pair)]) model)
    (current : GeneralNominalState.Models b model) :
    GeneralNominalState.Models (propagate b registry invocation declaration [(name,pair)]) model := by
  have parts := (propagate_models ..).mp old
  apply (propagate_models ..).mpr
  refine ⟨current,?_,?_⟩
  · intro first one last two same
    have h1 := List.mem_singleton.mp one
    have h2 := List.mem_singleton.mp two
    subst first; subst last
    exact parts.2.1 (name,pair) (by simp) (name,pair) (by simp) rfl
  · simp [merges,names,occurrences,All]

/-- Semantic endpoints of actual duplicate allocation and its singleton
replacement agree, without a current merge/private-state assumption. -/
theorem collapse_endpoints (a b : GeneralNominalState.State) (registry : Registry)
    (invocation : Nat) (declaration : Declaration) (name : Nat)
    (pair : GeneralSourceState.Interval) (model : GeneralNominalCommonBridge.Assignment)
    (names : declaration.inputNames = [name])
    (old : GeneralNominalState.Models
      (propagate a registry invocation declaration [(name,pair),(name,pair)]) model)
    (current : GeneralNominalState.Models b model) :
    let ca := (capture a registry invocation declaration.id [(name,pair),(name,pair)]).inputs name
    CommonNominalFullCarrier.Equivalent (model ca.1).1 (model pair.1).1 ∧
    CommonNominalFullCarrier.Equivalent (model ca.2).1 (model pair.2).1 := by
  have result := propagated_endpoints a b registry registry invocation invocation declaration declaration
    [(name,pair),(name,pair)] [(name,pair)] model name (by simp [names]) (by simp [names])
    (by simp [occurrences]) (by intro p; simp [occurrences]) old
    (collapse_propagation a b registry invocation declaration name pair model names old current)
  simpa [capture,occurrences] using result
end Yulang.GeneralDictionaryCaptureMultiplicity
