import Yulang.GeneralRebaseRowOuterBoundary287

/-! Independently of model dependence, the finite closed term representation
builds every nominal parameter as a type sum-left. Even a *fixed* row value
under the wrapper cannot be represented by such an expression. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28200
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowClosedTerm287
open GeneralRebaseRowChildSource287 (R F)
open GeneralNominalOriginTerms (Expr arity)
open GeneralNominalFiniteMeaning (denote build)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_scalar tagged_nominal tagged_shape)
open CommonNominalFullCarrier

theorem r_not_closed {α : Type} (env : α → Ty) (r : Common.Row)
    (term : Expr α) (closed : term.leaves = []) :
    ¬ Equivalent (R r) (denote env term) := by
  intro eq
  cases term with
  | leaf a => cases closed
  | node test kids =>
    cases test with
    | scalar base =>
      have bad := tag_subtype (tagged_nominal 6 _) (tagged_scalar base) eq.1
      cases bad
    | structural shape =>
      have len : (List.ofFn (fun i => denote env (kids i))).length = shape.arity :=
        List.length_ofFn
      have bad := tag_subtype (tagged_nominal 6 _) (tagged_shape shape _ len) eq.1
      cases shape <;> cases bad
    | nominal name count =>
      let args := List.ofFn (fun i : Fin count => (Sum.inl (denote env (kids i)) : Argument))
      have exact : Subtype (nominal 6 [.inr r]) (nominal name args) := eq.1
      have inv := (nominal_regular_invariant_exact 6 name _ _).mp exact
      have positive : 0 < count := by
        have same := inv.2.1
        change 1 = (List.ofFn (fun i : Fin count => (Sum.inl (denote env (kids i)) : Argument))).length at same
        rw [List.length_ofFn] at same
        omega
      let i : Fin count := ⟨0,positive⟩
      have found : args[0]? = some (.inl (denote env (kids i))) := by
        unfold args i
        simp [positive]
      exact inv.2.2 0 (.inr r) (.inl (denote env (kids i))) rfl found

theorem child_closed {α : Type} {test : GeneralNominalRecursiveInspection.Test}
    (kids : Fin (arity test) → Expr α) (closed : (Expr.node test kids).leaves = [])
    (i : Fin (arity test)) : (kids i).leaves = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a seen
  have member : (kids i).leaves ∈ List.ofFn (fun j => (kids j).leaves) :=
    List.mem_ofFn.mpr ⟨i,rfl⟩
  have all : a ∈ (Expr.node test kids).leaves := List.mem_flatten.mpr ⟨_,member,seen⟩
  rw [closed] at all
  cases all

theorem wrapped_not_closed {α : Type} (env : α → Ty) (r : Common.Row)
    (term : Expr α) (closed : term.leaves = []) :
    ¬ Equivalent (F (R r)) (denote env term) := by
  intro eq
  cases term with
  | leaf a => cases closed
  | node test kids =>
    cases test with
    | scalar base =>
      have bad := tag_subtype (tagged_nominal 0 _) (tagged_scalar base) eq.1
      cases bad
    | structural shape =>
      have len : (List.ofFn (fun i => denote env (kids i))).length = shape.arity :=
        List.length_ofFn
      have bad := tag_subtype (tagged_nominal 0 _) (tagged_shape shape _ len) eq.1
      cases shape <;> cases bad
    | nominal name count =>
      let args := List.ofFn (fun i : Fin count => (Sum.inl (denote env (kids i)) : Argument))
      have exact : Subtype (nominal 0 [.inl (R r)]) (nominal name args) := eq.1
      have inv := (nominal_regular_invariant_exact 0 name _ _).mp exact
      have positive : 0 < count := by
        have same := inv.2.1
        change 1 = (List.ofFn (fun i : Fin count => (Sum.inl (denote env (kids i)) : Argument))).length at same
        rw [List.length_ofFn] at same
        omega
      let i : Fin count := ⟨0,positive⟩
      have found : args[0]? = some (.inl (denote env (kids i))) := by
        unfold args i
        simp [positive]
      have eqChild : Equivalent (R r) (denote env (kids i)) :=
        inv.2.2 0 (.inl (R r)) (.inl (denote env (kids i))) rfl found
      exact r_not_closed env r (kids i) (child_closed kids closed i) eqChild

end Yulang.GeneralRebaseRowClosedTerm287
