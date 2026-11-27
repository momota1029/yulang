import Yulang.GeneralDeclarativeI65I74ProjectionPath464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias alias_symm)

private theorem path_widen {before after : View} (subset : ∀ n h, before n h → after n h)
    {x y : Nat} (p : Path before x y) : Path after x y := by
  induction p with
  | refl => exact .refl _
  | next step _ ih =>
    obtain ⟨h,p,q⟩ := step
    exact .next ⟨h, subset _ _ p,q⟩ ih

/-- New observations are confined to a single complete original alias class.
The alias relation remains exactly the same, including bounds-based aliases. -/
structure AdditionAtAliasClass (s t : State) (root : Nat) : Prop where
  aliases : ∀ a b, Alias t a b ↔ Alias s a b
  keep : ∀ a h, structural s a h → structural t a h
  only : ∀ a h, structural t a h → Alias s a root ∨ structural s a h

theorem some_new_shape_path_through_alias_class_has_one_exact_new_edge
    {s t : State} {root x y : Nat} (added : AdditionAtAliasClass s t root) :
    Path (structural t) x y ↔
      Path (structural s) x y ∨
      ∃ atName child, Path (structural s) x atName ∧ Alias s atName root ∧
        Descends (structural t) atName child ∧
        ¬ Descends (structural s) atName child ∧ Path (structural s) child y := by
  constructor
  · intro actual
    induction actual with
    | refl n => exact .inl (.refl n)
    | @next a b c first _ ih =>
      by_cases old : Descends (structural s) a b
      · rcases ih with good|⟨z,w,firstPart,alias,extra,isNew,lastPart⟩
        · exact .inl (.next old good)
        · exact .inr ⟨z,w,.next old firstPart,alias,extra,isNew,lastPart⟩
      · obtain ⟨h,haveNew,child⟩ := first
        have inClass := (added.only a h haveNew).resolve_right (fun q => old ⟨h,q,child⟩)
        rcases ih with good|⟨z,w,_,alias,lastNew,isNew,suffix⟩
        · exact .inr ⟨a,b,.refl a,inClass,⟨h,haveNew,child⟩,old,good⟩
        · have eq : Alias s a z := .trans inClass (alias_symm alias)
          have agree : Alias t a z := (added.aliases a z).mpr eq
          have atA := edge_transport agree lastNew
          have stillNew : ¬ Descends (structural s) a w := fun prior =>
            isNew (edge_transport (alias_symm eq) prior)
          exact .inr ⟨a,w,.refl a,inClass,atA,stillNew,suffix⟩
  · rintro (old | ⟨a,b,leading,_,middle,_,follow⟩)
    · exact path_widen added.keep old
    · exact path_cat (path_widen added.keep leading)
        (.next middle (path_widen added.keep follow))

theorem no_old_return_to_the_alias_class_preserves_every_raw_k2
    {s t : State} {root : Nat} (added : AdditionAtAliasClass s t root)
    (noReturn : ∀ a b z, Alias s a root → Alias s z root → Descends (structural t) a b →
      ¬ Descends (structural s) a b → ¬ Path (structural s) b z) (v : Nat) :
    AliasCycle t (observed t) v ↔ AliasCycle s (observed s) v := by
  constructor
  · rintro ⟨c,last,first,back,returnAlias⟩
    have identified := (added.aliases last v).mp returnAlias
    by_cases oldFirst : Descends (structural s) v c
    · rcases (some_new_shape_path_through_alias_class_has_one_exact_new_edge added).mp back with
        oldBack | ⟨a,b,leading,classA,middle,isNew,tail⟩
      · exact ⟨c,last,oldFirst,oldBack,identified⟩
      · have atLast := edge_transport identified oldFirst
        exact (noReturn a b a classA classA middle isNew (path_cat tail (.next atLast leading))).elim
    · obtain ⟨h,opens,chosen⟩ := first
      have classV := (added.only v h opens).resolve_right (fun old => oldFirst ⟨h,old,chosen⟩)
      rcases (some_new_shape_path_through_alias_class_has_one_exact_new_edge added).mp back with
        oldBack | ⟨a,_,leading,classA,_,_,_⟩
      · have classLast : Alias s last root := .trans identified classV
        exact (noReturn v c last classV classLast ⟨h,opens,chosen⟩ oldFirst oldBack).elim
      · exact (noReturn v c a classV classA ⟨h,opens,chosen⟩ oldFirst leading).elim
  · rintro ⟨c,last,⟨h,first,chosen⟩,back,link⟩
    exact ⟨c,last,⟨h,added.keep _ _ first,chosen⟩,path_widen added.keep back,(added.aliases last v).mpr link⟩

theorem actually_appending_nonalias_row_changes_shapes_only_on_old_alias_class
    (s : State) (root : Nat) (term : Expr) (notAlias : ∀ n, term ≠ .variable n) :
    AdditionAtAliasClass s (extendedRows s ⟨root,term⟩) root := by
  let r : Equation := ⟨root,term⟩
  have same := adding_a_non_alias_row_preserves_actual_aliases s r notAlias
  refine ⟨same,?_,?_⟩
  · rintro src h ⟨a,auth,e,seen,shape⟩
    exact ⟨a,(same src a).mpr auth,e,List.mem_append_left _ seen,shape⟩
  · rintro src h ⟨a,auth,e,seen,shape⟩
    change _ ∈ s.equations ++ [r] at seen
    rcases List.mem_append.mp seen with before|new
    · exact .inr ⟨a,(same src a).mp auth,e,before,shape⟩
    · have eq := congrArg Equation.left (List.mem_singleton.mp new)
      change a = root at eq
      subst a
      exact .inl ((same src root).mp auth)

/-- Semantic justification for the added literal equation and issuer provenance
are deliberately separate hypotheses at a higher layer. This is the complete
existing raw K2 preservation statement for any alias class satisfying the
no-return test, even if the target already lies on an old cycle. -/
theorem one_nonalias_raw_row_does_not_change_k2_under_original_class_no_return
    (s : State) (root : Nat) (term : Expr) (notAlias : ∀ n, term ≠ .variable n)
    (noReturn : ∀ shape, shapeOf term = some shape → ∀ child ∈ shape.children,
      ∀ near, Alias s near root → ¬ Path (structural s) child near) (v : Nat) :
    AliasCycle (extendedRows s ⟨root,term⟩) (observed (extendedRows s ⟨root,term⟩)) v ↔
      AliasCycle s (observed s) v := by
  let r : Equation := ⟨root,term⟩
  have added := actually_appending_nonalias_row_changes_shapes_only_on_old_alias_class s root term notAlias
  apply no_old_return_to_the_alias_class_preserves_every_raw_k2 added
  rintro a b z _ alias ⟨h,⟨owner,auth,e,mem,shape⟩,take⟩ notOld
  change _ ∈ s.equations ++ [r] at mem
  rcases List.mem_append.mp mem with old|new
  · exact (notOld ⟨h,⟨owner,(added.aliases a owner).mp auth,e,old,shape⟩,take⟩).elim
  · have eq : e = term := congrArg Equation.right (List.mem_singleton.mp new)
    subst e
    exact noReturn h shape b take z alias

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
