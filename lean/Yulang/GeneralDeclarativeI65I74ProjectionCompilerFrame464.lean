import Yulang.GeneralDeclarativeI65I74ProjectionBatchField464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open AuthoredInspectQuery456 (legacyApply compileApply compileQuery compileQueries compile_query_exact)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open PreparedDeclarations463

/-- An explicit frame for the existing source compiler. Identical authored
registry alone is not an assertion that every interpretation/mode agrees. -/
structure SameCompilerFrame (p : SnapshotPair) : Prop where
  environment : p.before.state.base.core.current.environment =
    p.after.state.base.core.current.environment
  modes : p.before.state.base.core.modes = p.after.state.base.core.modes

private theorem same_apply_only_reads_mode_frame (s t : GeneralDeclarativeI65.State)
    (env : s.current.environment = t.current.environment) (modes : s.modes = t.modes)
    (key : Nat) (args : List Expr) : compileApply s key args = compileApply t key args := by
  rcases s with ⟨⟨e₁,old,one⟩,p₁,n₁,r₁⟩
  rcases t with ⟨⟨e₂,new,two⟩,p₂,n₂,r₂⟩
  change e₁ = e₂ at env
  change p₁ = p₂ at modes
  subst e₂ p₂
  simp only [compileApply,legacyApply,authoredRegistry]
  split <;> try rfl
  cases args with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | cons b rest => rfl
    | nil =>
      cases read : GeneralDeclarativeWitnessConstructorModes357.readUse e₁ key 1 with
      | none => rfl
      | some u => cases u.mode <;> rfl

private theorem same_apply {p : SnapshotPair} (f : SameCompilerFrame p) (key : Nat) (args : List Expr) :
    compileApply p.before.state.base.core key args = compileApply p.after.state.base.core key args :=
  same_apply_only_reads_mode_frame _ _ f.environment f.modes key args

mutual
theorem same_compiled_written_tree_in_both_supplied_inputs
    {p : SnapshotPair} (f : SameCompilerFrame p) (term : Pattern) :
    compileQuery p.before.state.base.core term = compileQuery p.after.state.base.core term := by
  cases term with
  | var n => rfl
  | app k ts =>
    simp only [compileQuery,same_compiled_written_forest_in_both_supplied_inputs f ts, same_apply f]
  | record k x y => simp only [compileQuery,same_compiled_written_tree_in_both_supplied_inputs f x,
      same_compiled_written_tree_in_both_supplied_inputs f y]
  | variant k x => simp only [compileQuery,same_compiled_written_tree_in_both_supplied_inputs f x]
  | join x y => simp only [compileQuery,same_compiled_written_tree_in_both_supplied_inputs f x,
      same_compiled_written_tree_in_both_supplied_inputs f y]
termination_by sizeOf term

theorem same_compiled_written_forest_in_both_supplied_inputs
    {p : SnapshotPair} (f : SameCompilerFrame p) (ts : List Pattern) :
    compileQueries p.before.state.base.core ts = compileQueries p.after.state.base.core ts := by
  cases ts with
  | nil => rfl
  | cons first rest => simp only [compileQueries,same_compiled_written_tree_in_both_supplied_inputs f first,
      same_compiled_written_forest_in_both_supplied_inputs f rest]
termination_by sizeOf ts
end

/-- This transports the unchanged input source selection's literal head
*address*, not a resolver verdict or a raw head trail. In particular it
does not invoke GD or construct a new producer. -/
theorem an_after_prechecked_head_has_its_same_compiled_origin_before
    {p : SnapshotPair} (f : SameCompilerFrame p) (t : CheckedTable p.before.state.base.core.current)
    (now : PrecheckedHead (p := p.after.old) (p.afterTable t)) :
    ∃ before : PrecheckedHead (p := p.before.old) t,
      before.orig.location = now.orig.location ∧ before.orig.declaration = now.orig.declaration ∧
      before.orig.original = now.orig.original ∧ before.orig.capture = now.orig.capture ∧
      before.orig.code = now.orig.code ∧
      readPrecheckedHead (p := p.before.old) t now.orig.location = some before := by
  have exposed := same_authored_roster_and_original_head_arguments p
  have v : (visible p.before.old.state.core p.before.root)[now.orig.location.visibleOrdinal]? =
      some now.orig.declaration := by rw [exposed.1]; exact now.orig.actualVisible
  have arg : p.before.root.demand.arguments[now.orig.location.headArgument]? = some now.orig.capture := by
    rw [exposed.2]
    exact now.orig.actualArgument
  have compiled : AuthoredInspectQuery456.AuthoredQuery p.before.old.state.core
      (normalize now.orig.original) now.orig.code := by
    have current := (compile_query_exact ..).mpr now.orig.compiled
    apply (compile_query_exact ..).mp
    exact (same_compiled_written_tree_in_both_supplied_inputs f _).trans current
  let old : PrecheckedHead (p := p.before.old) t :=
    ⟨⟨now.orig.location,now.orig.declaration,now.orig.original,now.orig.capture,now.orig.code,
      v,now.orig.actualHead,arg,compiled⟩,now.stored,now.point⟩
  exact ⟨old,rfl,rfl,rfl,rfl,rfl,each_prechecked_head_position_replays (p := p.before.old) t old⟩

theorem actual_batch_field_uses_the_same_prechecked_compiled_origin
    {p : SnapshotPair} (f : SameCompilerFrame p) (t : CheckedTable p.before.state.base.core.current)
    {r : HeadFieldReceipt} (h : ExactProjectionBatchField p t r) :
    ∃ (before : PrecheckedHead (p := p.before.old) t)
      (after : PrecheckedHead (p := p.after.old) (p.afterTable t)),
      before.orig.location = r.authored ∧ after.orig.location = r.authored ∧
      before.orig.declaration = after.orig.declaration ∧
      before.orig.original = after.orig.original ∧ before.orig.capture = after.orig.capture ∧
      before.orig.code = after.orig.code ∧
      readPrecheckedHead (p := p.before.old) t r.authored = some before := by
  obtain ⟨after,_,found,_,_,_,_⟩ := h.2.1
  obtain ⟨before,loc,decl,original,cap,code,replay⟩ :=
    an_after_prechecked_head_has_its_same_compiled_origin_before f t after
  refine ⟨before,after,loc.trans found,found,decl,original,cap,code,?_⟩
  rw [←found]
  exact replay

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
