import Yulang.GeneralNominalOriginTerms

/-! Semantic transport only: no syntactic equality of sites or origins is
asserted. Projection comparison retains its inhabited/coherent observation
premise; in particular nominal head validity alone does not specify type slots. -/
namespace Yulang.GeneralNominalHeadSemanticTransport185
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

private theorem equiv_trans (ab : Equivalent a b) (bc : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans ab.1 bc.1, subtype_trans bc.2 ab.2⟩

 theorem head_transport (same : Same model first last)
    (valid : Head model first test) : Head model last test := by
  obtain ⟨value, seen⟩ := same.1
  refine ⟨same.2.1, ?_⟩
  intro other observed
  have eqv := same.2.2 value other seen observed
  have held := valid.2 value seen
  cases test with
  | scalar base => exact equiv_trans ⟨eqv.2, eqv.1⟩ held
  | structural shape =>
    obtain ⟨values, length, equal⟩ := held
    exact ⟨values, length, equiv_trans ⟨eqv.2, eqv.1⟩ equal⟩
  | nominal name count =>
    obtain ⟨values, length, equal⟩ := held
    exact ⟨values, length, equiv_trans ⟨eqv.2, eqv.1⟩ equal⟩

 theorem project_observes (same : Same model first last) (test : Test)
    (index : Fin (arity test))
    (seen : Observes model (project first test index) value) :
    Observes model (project last test index) value := by
  obtain ⟨other, observed⟩ := same.2.1
  cases test with
  | scalar base => exact Fin.elim0 index
  | structural shape =>
    cases seen with
    | structural parent length equal found =>
      exact .structural observed length
        (equiv_trans ⟨(same.2.2 _ _ parent observed).2,
          (same.2.2 _ _ parent observed).1⟩ equal) found
  | nominal name count =>
    cases seen with
    | nominal parent equal found =>
      exact .nominal observed
        (equiv_trans ⟨(same.2.2 _ _ parent observed).2,
          (same.2.2 _ _ parent observed).1⟩ equal) found

 theorem project_observes_iff (same : Same model first last) (test : Test)
    (index : Fin (arity test)) (value) :
    Observes model (project first test index) value ↔
      Observes model (project last test index) value :=
  ⟨project_observes same test index, project_observes (same_symm same) test index⟩

 theorem project_same (same : Same model first last) (test : Test)
    (index : Fin (arity test))
    (valid : Same model (project first test index) (project first test index)) :
    Same model (project first test index) (project last test index) := by
  obtain ⟨value, seen⟩ := valid.1
  exact ⟨valid.1, ⟨value, project_observes same test index seen⟩,
    fun a b one two => valid.2.2 a b one
      (project_observes (same_symm same) test index two)⟩

/-- A common constructor tree, with corresponding observational leaves,
transports its meaning without identifying the leaf origins syntactically. -/
 theorem holds_leaves (term : Expr α) (first last : α → Origin)
    (leaves : ∀ name ∈ term.leaves, Same model (first name) (last name))
    (valid : Holds model (term.bind (fun name => .leaf (first name))) root) :
    Holds model (term.bind (fun name => .leaf (last name))) root := by
  induction term generalizing root with
  | leaf name =>
    exact same_trans valid (leaves name (by simp [Expr.leaves]))
  | node test children ih =>
    refine ⟨valid.1, ?_⟩
    intro index
    apply ih index _ (valid.2 index)
    intro name member
    apply leaves name
    simp only [Expr.leaves, List.mem_flatten, List.mem_ofFn]
    exact ⟨(children index).leaves, ⟨index, rfl⟩, member⟩

 theorem holds_leaves_and_root (term : Expr α) (first last : α → Origin)
    (leaves : ∀ name ∈ term.leaves, Same model (first name) (last name))
    (roots : Same model root target)
    (valid : Holds model (term.bind (fun name => .leaf (first name))) root) :
    Holds model (term.bind (fun name => .leaf (last name))) target :=
  holds_transport roots (holds_leaves term first last leaves valid)

end Yulang.GeneralNominalHeadSemanticTransport185
