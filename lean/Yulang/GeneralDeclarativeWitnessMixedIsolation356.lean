import Yulang.GeneralDeclarativeWitnessMixedFront356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedIsolation356
open GeneralDeclarativeWitnessMixedScope356 (Scope Ordinary filtered keep_exact)
open GeneralSourceMetadataBareBundle291 (InputBundle forget preserves_input)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation constructors)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeHead320 (State)

theorem compiled_scope_is_original {e source s path d out} (a : Ordinary e source s path d out) :
    forget a.actual.global.table = filtered source e.typedRoles :=
  (preserves_input _ _ a.actual.global.canonical).1

theorem ordinary_mode_and_roles_not_changed {e source s path d out} (a : Ordinary e source s path d out) :
    a.actual.global.table.declared = source.declared ∧
    a.actual.global.table.snapshot = source.snapshot ∧
    (forget a.actual.global.table).roles = source.roles := by
  have kept := compiled_scope_is_original a
  have mapped := congrArg InputBundle.declared kept
  have interp := congrArg InputBundle.snapshot kept
  have head := congrArg InputBundle.roles kept
  exact ⟨mapped,interp,head⟩

theorem exact_retained_role {e source s path d out} (a : Ordinary e source s path d out)
    {role : Nat} (success : role ∉ e.typedRoles) {impl : Declaration} (this : impl.role = role) :
    (impl ∈ (registry a.actual.global.table).declarations ↔ impl ∈ source.declarations) := by
  have kept := congrArg InputBundle.declarations (compiled_scope_is_original a)
  change a.actual.global.table.declarations = (filtered source e.typedRoles).declarations at kept
  change impl ∈ a.actual.global.table.declarations ↔ _
  rw [kept,keep_exact,this]
  simp [success]

/-- Whole-role filtration preserves every competing declaration at every
actual ordinary node. It cannot hide an alternative at a retained role. -/
theorem real_ordinary_nodes_keep_all_candidates {e source s path d out} (a : Ordinary e source s path d out)
    (f : Fixed) (used : f ∈ a.actual.diagnostic.fixed) (impl : Declaration) (this : impl.role = f.demand.role) :
    (impl ∈ (registry a.actual.global.table).declarations ↔ impl ∈ source.declarations) :=
  exact_retained_role a (a.doesNotReturnToTyped f used) this

end Yulang.GeneralDeclarativeWitnessMixedIsolation356
