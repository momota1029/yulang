import Yulang.GeneralSourceRoleResolverFixture292
import Yulang.GeneralSourceRoleActualAttach292

/-! Observational locality of the old selected association read. This is
specific to an already selected impl and is not an assertion about any
language-visible rejection, result completeness or journal stabilization. -/
namespace Yulang.GeneralSourceRoleOperationalRead292
open Yulang.Roles

theorem assocValue_one_read (i : AssocImpl) (g : Goal) (name : Nat) (a b : RoleDecl)
    (h : (a.assoc name).join = (b.assoc name).join) :
    assocValue i a g name = assocValue i b g name := by
  unfold assocValue
  rw [h]

theorem selected_read_congr (env : AssocEnv) (wf : WellFormed env.cores)
    (g : Goal) (n : Nat) (a b : RoleDecls)
    (resolved : resolve env.cores wf g = .resolved)
    (h : ((a g.role).assoc n).join = ((b g.role).assoc n).join) :
    assocOf env a wf g n = assocOf env b wf g n := by
  obtain ⟨i,member,selected,_⟩ := assoc_selected_of_resolved env wf g resolved
  rw [assoc_independent_of_constraints env a wf g n resolved i member selected,
    assoc_independent_of_constraints env b wf g n resolved i member selected]
  exact assocValue_one_read i g n _ _ h

theorem one_read_weaker_than_declared_state :
    (some none : Option (Option Term)).join = (none : Option (Option Term)).join ∧
    (some none : Option (Option Term)) ≠ (none : Option (Option Term)) := by decide

/-- Absence and required are observationally equal only for the omitted value
reader. They are not equal as declared states. Already selected + well-formed
rules out the required branch when the implementation body is omitted. -/
theorem valid_selected_required_never_omitted (roles : RoleDecls) (impl : AssocImpl)
    (g : Goal) (n : Nat) (matched : Matches impl.impl g)
    (complete : AssocComplete roles impl)
    (required : (roles g.role).assoc n = some none) :
    ∃ body, impl.assoc.lookup n = some body := by
  have clause := complete.2 n none (matched.1.symm ▸ required)
  rcases clause with supplied | ⟨_,impossible⟩
  · exact supplied
  · cases impossible

theorem resolved_declared_has_compiled_value
    {frontend : GeneralSourceRoleSpelling292.Environment} {fallback : Nat}
    {shells : List GeneralSourceRoleSyntaxBoundary292.Shell}
    {table : GeneralSourceMetadataRoles291.RoleSource}
    (assembled : GeneralSourceRoleSyntaxPipeline292.applyShells frontend fallback shells = some table)
    (env : AssocEnv) (wf : WellFormed env.cores)
    (allOK : AssocWellFormed env (GeneralSourceMetadataRoles291.roleTable table))
    (g : Goal) (n : Nat) (rightRole : resolve env.cores wf g = .resolved)
    (rhs : Term)
    (source : GeneralSourceRoleResolverUse292.ShellDefault frontend shells g.role n rhs) :
    ∃ value, assocOf env (GeneralSourceMetadataRoles291.roleTable table) wf g n = some value ∧
      ∀ v, 0 < value.occurrences v → 0 < argsOccurrences v g.args := by
  have present :=
    (GeneralSourceRoleSyntaxPipeline292.default_from_shells frontend fallback shells table assembled g.role n rhs).mpr source
  exact assoc_total_closed _ _ wf allOK g n rightRole ⟨_,present⟩

end Yulang.GeneralSourceRoleOperationalRead292
