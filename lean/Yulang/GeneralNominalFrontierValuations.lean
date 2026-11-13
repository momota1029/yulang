import Yulang.GeneralNominalOpenInspectionMatching
import Yulang.GeneralNominalFrontierReadback

/-! Every origin in the finite initial frontier is an alias of one initial
identity. Its valuation is shared across all terms and remains valid through
actual steps, including changes to inspection intervals. -/
namespace Yulang.GeneralNominalFrontierValuations
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalSourceFrontier
open GeneralNominalFrontierReadback GeneralNominalActualInspectionSteps
open GeneralNominalIndexedHoleReadback GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality
open GeneralNominalSaturationState GeneralNominalSupport CommonNominalFullCarrier

variable {roles : Roles.RoleDecls}
variable {model : GeneralNominalCommonBridge.Assignment}

theorem explored_alias (state : State roles) (fuel : Nat)
    (slot : Fin state.context.state.base.slots) (root : Origin)
    (represented : Represents state root (state.context.state.base.source slot))
    (member : result ∈ explore state.context.state fuel slot root) :
    ∃ identity ∈ GeneralNominalState.sources state.context.state, Represents state result identity := by
  induction fuel generalizing slot root with
  | zero => cases List.mem_singleton.mp member; exact ⟨_,by
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))),represented⟩
  | succ fuel ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_,List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))),represented⟩
    · obtain ⟨next,edge,present⟩ := List.mem_flatMap.mp member
      exact ih next.2 (next.1.apply root) (label_readback represented (child_readback state edge)) present

theorem frontier_alias (state : State roles) (member : result ∈ frontier state.context.state) :
    ∃ identity ∈ GeneralNominalState.sources state.context.state, Represents state result identity := by
  rcases List.mem_append.mp member with source | paths
  · obtain ⟨identity,present,rfl⟩ := List.mem_map.mp source
    exact ⟨identity,present,fun model _ => source_self model identity⟩
  · obtain ⟨slot,_,present⟩ := List.mem_flatMap.mp paths
    exact explored_alias state _ slot _ (fun model _ => source_self model _) present

/-- One source identity is chosen for each fixed frontier position, once for
all future states and all models. The initial source keys are not reconstructed. -/
theorem simultaneous_aliases (state : State roles) :
    ∃ identities : Nat → Nat, ∀ index ∈ holes (frontier state.context.state),
      identities index ∈ GeneralNominalState.sources state.context.state ∧
      Represents state (origin (frontier state.context.state) index) (identities index) := by
  classical
  have each (index : Nat) (present : index ∈ holes (frontier state.context.state)) :
      ∃ identity ∈ GeneralNominalState.sources state.context.state, Represents state (origin (frontier state.context.state) index) identity := by
    apply frontier_alias state
    have bound : index < (frontier state.context.state).length := List.mem_range.mp present
    simp only [origin,List.getElem?_eq_getElem bound,Option.getD_some]
    exact List.getElem_mem ..
  let identities := fun index => if present : index ∈ holes (frontier state.context.state)
    then Classical.choose (each index present) else 0
  refine ⟨identities,?_⟩
  intro index present
  simpa only [identities,dite_eq_left present] using Classical.choose_spec (each index present)

theorem simultaneous_survives (before : Tracked roles) :
    ∃ identities : Nat → Nat, (∀ index ∈ holes (frontier before.current.context.state),
      identities index ∈ GeneralNominalState.sources before.current.context.state) ∧ ∀ after,
      B4Target.Steps (Step registry focus) before after →
      ∀ index ∈ holes (frontier before.current.context.state),
        Represents after.current (origin (frontier before.current.context.state) index) (identities index) := by
  obtain ⟨identities,represented⟩ := simultaneous_aliases before.current
  exact ⟨identities,fun index member => (represented index member).1,
    fun _ path index member => trace_preserves path (represented index member).2⟩

theorem alias_value (same : Same model root (.source identity)) :
    At model .actual root (model identity).1 :=
  ⟨same.1,fun actual seen => same.2.2 actual _ seen (.source identity)⟩

/-- Interpreting a finite indexed expression uses one valuation of all holes.
No freeness or closedness of the valuation is required. -/
theorem readback_meaning (term : Expr Nat) (canonical : Canonical term)
    (unique : Unique model root)
    (readback : Holds model (interpret origins term) root)
    (values : Nat → Ty)
    (leaves : ∀ name ∈ term.leaves, At model .actual (origins name) (values name)) :
    At model .actual root (denote values term) := by
  induction term generalizing root with
  | leaf name =>
    exact GeneralNominalSimultaneousCaptures.at_same (leaves name (List.mem_singleton_self _)) (same_symm readback)
  | node test children ih =>
    apply assemble test .actual _ unique readback.1
    intro index
    have child : At model .actual (project root test index) (denote values (children index)) :=
      ih index (canonical.2 index) (projection_unique unique test canonical.1 index) (readback.2 index) (by
        intro name member
        exact leaves name (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩))
    cases test <;> exact child

theorem indexed_meaning (readback : Readback models origins remaining root term)
    (canonical : Canonical term) (valid : models model) (unique : Unique model root)
    (values : Nat → Ty)
    (leaves : ∀ name ∈ remaining, At model .actual (origins name) (values name)) :
    At model .actual root (denote values term) :=
  readback_meaning term canonical unique (readback.1 model valid) values
    (fun name member => leaves name (readback.2 name member))

/-- A shared source valuation is available for every represented dynamic ID.
This includes newly allocated IDs whenever their readback has been produced. -/
theorem source_valuation (before : Tracked roles) :
    ∃ identities : Nat → Nat, (∀ index ∈ holes (frontier before.current.context.state),
      identities index ∈ GeneralNominalState.sources before.current.context.state) ∧ ∀ after,
      B4Target.Steps (Step registry focus) before after →
      ∀ remaining, remaining ⊆ holes (frontier before.current.context.state) →
      ∀ root term, Readback (Models after.current) (origin (frontier before.current.context.state)) remaining root term →
        Canonical term → ∀ model, Models after.current model → Unique model root →
          At model .actual root (denote (fun name => (model (identities name)).1) term) := by
  obtain ⟨identities,initial,represented⟩ := simultaneous_survives (registry := registry) (focus := focus) before
  refine ⟨identities,initial,?_⟩
  intro after path remaining subset root term readback canonical model valid unique
  exact indexed_meaning readback canonical valid unique _
    (fun name member => alias_value (represented after path name (subset member) model valid))

end Yulang.GeneralNominalFrontierValuations
