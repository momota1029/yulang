import Yulang.GeneralNominalFiniteHeadInversion

/-! Actual paths through canonical structural and nominal arguments invert
to subterms of a closed finite input. Path construction is independent of
the chosen semantic tree and preserves the original source Pattern keys. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCanonicalPaths
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility
open GeneralNominalFiniteHeadInversion GeneralNominalSourceProjection
open GeneralNormalizedObservation CommonNominalFullCarrier

inductive Path (root : Origin) : Origin → Prop
  | root : Path root root
  | nominal : Path root parent → Path root (.nominal parent name index)
  | structural (canonical : shape.Canonical) : Path root parent → Path root (.structural parent shape index)

theorem trans (first : Path root middle) (last : Path middle endpoint) : Path root endpoint := by
  induction last with
  | root => exact first
  | nominal prior ih => exact .nominal ih
  | structural canonical prior ih => exact .structural canonical ih

private theorem list_values (values : List Ty) (length : values.length = count) :
    List.ofFn (fun index : Fin count => values[index.val]'(by rw [length]; exact index.isLt)) = values := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using length.symm
  · intro index first last
    simp only [List.getElem_ofFn]

variable {model : GeneralNominalCommonBridge.Assignment}

theorem structural_follows (term : Expr Nat) (closed : term.leaves = []) (canonical : Canonical term)
    (known : At model .actual root (denote (fun _ => .bottom) term)) (shapeCanonical : shape.Canonical)
    (observed : Observes model (.structural root shape index) actual) :
    ∃ part, Follows root term (.structural root shape index) part := by
  cases term with
  | leaf name => cases closed
  | node test children =>
    cases observed with
    | structural seen length equal found =>
      rename_i parentValue endpoints
      have rootEqual := known.2 _ seen
      let values : Fin (arity (.structural shape)) → Ty :=
        fun index => endpoints[index.val]'(by rw [length]; exact index.isLt)
      have built : build (.structural shape) values = shapeValue shape endpoints := by
        change shapeValue shape (List.ofFn values) = shapeValue shape endpoints
        exact congrArg (shapeValue shape) (list_values endpoints length)
      have same := test_equal test (.structural shape)
        (fun index => denote (fun _ => .bottom) (children index)) values canonical.1 shapeCanonical
        (show Equivalent _ (build (.structural shape) values) from by
          rw [built]; exact ⟨subtype_trans rootEqual.2 equal.1,subtype_trans equal.2 rootEqual.1⟩)
      subst test
      have bound : index < arity (.structural shape) := by
        have bound := (List.getElem?_eq_some_iff.mp found).1
        simpa only [length,arity] using bound
      exact ⟨children ⟨index,bound⟩,.child (.structural shape) children ⟨index,bound⟩ .root⟩

theorem nominal_follows (term : Expr Nat) (closed : term.leaves = [])
    (known : At model .actual root (denote (fun _ => .bottom) term))
    (observed : Observes model (.nominal root name index) actual) :
    ∃ part, Follows root term (.nominal root name index) part := by
  cases term with
  | leaf binder => cases closed
  | node test children =>
    cases observed with
    | nominal seen equal found =>
      rename_i parentValue arguments
      have rootEqual := known.2 _ seen
      let env : CommonNominalFullDemand.Environment Row :=
        ⟨fun _ => .bottom,fun _ => [.nominal name arguments.length]⟩
      have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp
        ((subtype_trans rootEqual.2 equal.1) 0) 0 env (.role 0)
        (show CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
          (observeTy 0 (nominal name arguments)) (.role 0) from by
          rw [observe_nominal]
          change CommonNominalFullDemand.Head.nominal name (arguments.map (argumentAt 0)).length ∈ env.roles 0
          simp only [List.length_map,env,List.mem_singleton])
      have same := List.mem_singleton.mp ((build_role test
        (fun index => denote (fun _ => .bottom) (children index)) env).mp accepted)
      cases test with
      | scalar => cases same
      | structural shape => cases shape <;> cases same
      | nominal label count =>
        obtain ⟨names,counts⟩ := CommonNominalFullDemand.Head.nominal.inj same
        subst label
        subst count
        have bound : index < arity (.nominal name arguments.length) :=
          (List.getElem?_eq_some_iff.mp found).1
        exact ⟨children ⟨index,bound⟩,.child (.nominal name arguments.length) children ⟨index,bound⟩ .root⟩

theorem follows_trans (first : Follows root term middle part) (last : Follows middle part endpoint value) :
    Follows root term endpoint value := by
  induction last with
  | root => exact first
  | child test children index prior ih => exact .child test children index ih

theorem observed_follows (path : Path root endpoint) (term : Expr Nat)
    (closed : term.leaves = []) (canonical : Canonical term)
    (known : At model .actual root (denote (fun _ => .bottom) term))
    (observed : Observes model endpoint actual) :
    ∃ part, Follows root term endpoint part := by
  induction path generalizing actual with
  | root => exact ⟨term,.root⟩
  | nominal prior ih =>
    cases observed with
    | nominal seen equal found =>
      obtain ⟨part,followed⟩ := ih seen
      have readback := followed_readback followed canonical (fun _ => .bottom) known
      obtain ⟨child,next⟩ := nominal_follows part (followed_closed followed closed) readback.2
        (.nominal seen equal found)
      exact ⟨child,follows_trans followed next⟩
  | structural shapeCanonical prior ih =>
    cases observed with
    | structural seen length equal found =>
      obtain ⟨part,followed⟩ := ih seen
      have readback := followed_readback followed canonical (fun _ => .bottom) known
      obtain ⟨child,next⟩ := structural_follows part (followed_closed followed closed) readback.1 readback.2
        shapeCanonical (.structural seen length equal found)
      exact ⟨child,follows_trans followed next⟩

theorem closed_pattern (path : Path root endpoint)
    (closed : ClosedTerm context pattern term)
    (known : At model .actual root (denote (fun _ => .bottom) term))
    (observed : Observes model endpoint actual) :
    ∃ source part, GeneralNominalSourcePatternParts.Part (GeneralDeclarationPatterns.normalize pattern) source ∧
      ClosedTerm context source part ∧ At model .actual endpoint (denote (fun _ => .bottom) part) ∧
      GeneralNominalPatersonLineage.mass [source] ≤ GeneralNominalPatersonLineage.mass [pattern] := by
  obtain ⟨part,followed⟩ := observed_follows path term closed.2.1 closed.2.2 known observed
  obtain ⟨source,member,reified,meaning,bound⟩ := followed_pattern followed closed known
  exact ⟨source,part,member,reified,meaning,bound⟩

end Yulang.GeneralNominalCanonicalPaths
