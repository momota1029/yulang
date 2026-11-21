import Yulang.GeneralDeclarativeFrontier327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCandidateScan327
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativePriority321 (Candidates Visible Survives Blocked)
open GeneralDeclarativeFrontier327 (Unique unique_declaration)

/-- Enumerate only the actual visible registry entries, with supplied
exact *ordinary* tests. Failure to match positively is not used as the
unresolved predicate. -/
def viable (r : Registry) (d : Demand) (test : Declaration → Bool) : List Declaration :=
  r.declarations.filter (fun decl => decl.role == d.role && test decl)

theorem exact_membership {r : Registry} {d : Demand}
    (correct : ∀ impl ∈ r.declarations, impl.role = d.role → (test impl = true ↔ tests.viable d impl)) :
    impl ∈ viable r d test ↔ Survives r tests d impl := by
  simp only [viable,List.mem_filter,Bool.and_eq_true,beq_iff_eq,Survives,Visible]
  constructor
  · rintro ⟨here,role,found⟩
    exact ⟨⟨here,role⟩,(correct _ here role).mp found⟩
  · rintro ⟨⟨here,role⟩,passes⟩
    exact ⟨here,role,(correct _ here role).mpr passes⟩

theorem scan_blocked {r : Registry} {d : Demand}
    (correct : ∀ decl ∈ r.declarations, decl.role = d.role → (wait decl = true ↔ tests.unresolved d decl)) :
    (viable r d wait).isEmpty = false ↔ Blocked r tests d := by
  have h : ∀ decl, decl ∈ viable r d wait ↔ Visible r d decl ∧ tests.unresolved d decl :=
    fun decl => exact_membership (tests := ⟨tests.unresolved,tests.viable⟩) (impl := decl) correct
  constructor
  · intro notEmpty
    cases s : viable r d wait with
    | nil => simp [s] at notEmpty
    | cons first more =>
      exact ⟨first,(h first).mp (s ▸ List.mem_cons_self)⟩
  · rintro ⟨one,blocked⟩
    have mem := (h one).mpr blocked
    cases s : viable r d wait with
    | nil => rw [s] at mem; exact False.elim (List.not_mem_nil mem)
    | cons first more => rfl

theorem single {r : Registry} {d : Demand} (checked : Checked r)
    (correct : ∀ impl ∈ r.declarations, impl.role = d.role → (test impl = true ↔ tests.viable d impl)) :
    viable r d test = [only] ↔ Unique r tests d only := by
  have iffHere (decl : Declaration) := exact_membership (impl := decl) correct
  constructor
  · intro found
    have appears : only ∈ viable r d test := found ▸ List.mem_cons_self
    refine ⟨(iffHere only).mp appears,fun decl v => congrArg Declaration.id ?_⟩
    exact List.mem_singleton.mp (found ▸ (iffHere decl).mpr v)
  · intro picked
    have appears := (iffHere only).mpr picked.1
    have unique (decl : Declaration) (h : decl ∈ viable r d test) : decl = only :=
      unique_declaration checked d picked ((iffHere decl).mp h)
    have nodup : ((viable r d test).map Declaration.id).Nodup := by
      exact List.Nodup.sublist ((List.filter_sublist).map _) checked.1
    cases h : viable r d test with
    | nil => rw [h] at appears; exact False.elim (List.not_mem_nil appears)
    | cons x xs =>
      have e := unique x (h ▸ List.mem_cons_self)
      subst x
      cases xs with
      | nil => rfl
      | cons y rest =>
        have f := unique y (h ▸ (List.mem_cons_of_mem _ List.mem_cons_self))
        subst y
        rw [h] at nodup
        exact False.elim ((List.nodup_cons.mp nodup).1 List.mem_cons_self)

end Yulang.GeneralDeclarativeCandidateScan327
