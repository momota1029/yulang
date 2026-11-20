import Yulang.GeneralSourceRoleQualification292

/-! Keep an independently supplied scope per symbolic role. The scope carrier
has no prescribed source syntax; the helper does not assign scopes or IDs. -/
namespace Yulang.GeneralSourceRoleScopedExport292
open GeneralSourceRoleSpelling292 (Environment Role)
open GeneralSourceRoleExport292 (Aligned RowWitness collect collect_exact resolveRole role_exact)
open GeneralSourceMetadataBuildRoles291 (Input build build_exact forget)
open GeneralSourceMetadataRoles291 (RoleSource Valid)
open GeneralSourceMetadataBareRole291 (BareRow forgetRow)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure ScopedRole (Scope : Type) where
  scope : Scope
  role : Role

def lower {Scope : Type} (resolver : Scope → Environment) (fallback : Nat)
    (entries : List (ScopedRole Scope)) : Option RoleSource :=
  (collect (fun p => resolveRole (resolver p.scope) p.role) entries).bind fun rows =>
    build (⟨fallback,rows⟩ : Input)

def Witness {Scope : Type} (resolver : Scope → Environment) (p : ScopedRole Scope) (row : BareRow) : Prop :=
  RowWitness (resolver p.scope) p.role row

theorem lower_exact {Scope : Type} (resolver : Scope → Environment) (fallback : Nat)
    (entries : List (ScopedRole Scope)) (out : RoleSource) :
    lower resolver fallback entries = some out ↔ out.fallbackArity = fallback ∧
      Aligned (Witness resolver) entries (out.rows.map forgetRow) ∧ Valid out := by
  have row_law : ∀ a b, resolveRole (resolver a.scope) a.role = some b ↔ Witness resolver a b := by
    intro a b; exact role_exact ..
  constructor
  · intro pass
    obtain ⟨rows,built,generated⟩ := bind_success pass
    have facts := (build_exact ..).mp generated
    have data : out.fallbackArity = fallback ∧ out.rows.map forgetRow = rows := by
      have := facts.1
      simp only [forget,Input.mk.injEq] at this
      exact this
    exact ⟨data.1,data.2 ▸ (collect_exact _ _ row_law _ _).mp built,facts.2⟩
  · rintro ⟨arity,related,valid⟩
    unfold lower
    rw [(collect_exact _ _ row_law _ _).mpr related]
    exact (build_exact ..).mpr ⟨by cases out; cases arity; rfl,valid⟩

theorem constant_env {Scope : Type} (env : Environment) (fallback : Nat)
    (input : List (ScopedRole Scope)) :
    lower (fun _ => env) fallback input =
      GeneralSourceRoleExport292.lower env fallback (input.map ScopedRole.role) := by
  have h : collect (fun p => resolveRole env p.role) input =
      collect (resolveRole env) (input.map ScopedRole.role) := by
    induction input with
    | nil => rfl
    | cons h t ih => rw [List.map_cons,collect,collect,ih]
  unfold lower GeneralSourceRoleExport292.lower
  rw [h]

end Yulang.GeneralSourceRoleScopedExport292
