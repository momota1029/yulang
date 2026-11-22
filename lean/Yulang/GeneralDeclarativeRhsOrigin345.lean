import Yulang.GeneralDeclarativeCurrentUnstored345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRhsOrigin345
open GeneralDeclarations (Declaration)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open GeneralSourceState (Output)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalCenteredHeadMatEffects (compileBody)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeStoppedOutput339 (Receipt ordinary captureFor)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeHead320 (Equation)

def Indexed (roles : Roles.RoleDecls) (d : Declaration) (name : Nat) : Body → Prop
  | .explicit eq => (∃ i : Nat, d.associated[i]? = some eq) ∧ eq.name = name
  | .default role key t =>
    role = d.role ∧ key = name ∧ (roles d.role).assoc name = some (some t) ∧
      ∀ eq ∈ d.associated, eq.name ≠ name

theorem indexed_iff (d : Declaration) (name : Nat) (body : Body) :
    Supplies roles d name body ↔ Indexed roles d name body := by
  constructor
  · intro h
    cases h with
    | explicit eq found named => exact ⟨List.mem_iff_getElem?.mp found,named⟩
    | default rhs absent declared => exact ⟨rfl,rfl,declared,absent⟩
  · cases body with
    | explicit eq =>
      rintro ⟨place,named⟩
      exact .explicit eq (List.mem_iff_getElem?.mpr place) named
    | default role key rhs =>
      rintro ⟨rfl,rfl,declared,absent⟩
      exact .default rhs absent declared

theorem rhs_exact {final : State rs} {e : Effect rs} {out : Output} {row : Equation}
    (receipt : Receipt final e out row) :
    ∃ body code, Indexed rs e.plan.packet.declaration out.name body ∧
      compileBody e.plan body = some code ∧
      row = ⟨out.target,logical (captureFor e.plan body) .actual code⟩ := by
  obtain ⟨body,matched,made⟩ := receipt.authored
  have supply := (lookup_exact rs e.plan.packet.declaration
    e.plan.packet.checked.identified.2.2.1 _ body).mp matched
  unfold ordinary at made
  obtain ⟨code,ran,rfl⟩ := Option.map_eq_some_iff.mp made
  exact ⟨body,code,(indexed_iff _ _ _).mp supply,ran,rfl⟩

theorem default_center (p : Plan rs) (role name : Nat) (t : Roles.Term) (index : Fin (rs p.input.occurrence.demand.role).arity) :
    captureFor p (.default role name t) index.val = point (p.input.center index) := by
  change point ((List.ofFn p.input.center)[index.val]?.getD 0) = _
  rw [List.getElem?_ofFn]
  simp [index.isLt]

end Yulang.GeneralDeclarativeRhsOrigin345
