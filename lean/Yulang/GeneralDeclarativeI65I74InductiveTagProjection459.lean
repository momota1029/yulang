import Yulang.GeneralDeclarativeI65I74IdenticalTagProjection459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InductiveTagProjection459
open GeneralDeclarationPatterns
open IdenticalTagProjection459

/-- Two exact original source branches; equality is source spelling, not
semantic equality at some capture, nor equality of tag alone. -/
def SameTagSpelling (p q : Pattern) : Prop :=
  ∃ tag term, p = .variant tag term ∧ q = .variant tag term

theorem exactly_written_duplicate_test459 (p q : Pattern) :
    isRepeatedTag p q = true ↔ SameTagSpelling p q := by
  constructor
  · exact only_identically_written_tag459
  · rintro ⟨k,t,rfl,rfl⟩
    simp [isRepeatedTag]

/- Syntax-directed projection of actual authored source. The join rule
erases only an exactly repeated literal-variant branch. It does not
model opening a join during inspection or create a new source declaration. -/
mutual
  inductive Projects : Pattern → Pattern → Prop where
    | var : Projects (.var n) (.var n)
    | app : ProjectsArgs args out → Projects (.app k args) (.app k out)
    | record : Projects first f → Projects last l →
        Projects (.record k first last) (.record k f l)
    | variant : Projects term out → Projects (.variant k term) (.variant k out)
    | repeated : Projects (.variant k term) out →
        Projects (.join (.variant k term) (.variant k term)) out
    | keepJoin : ¬SameTagSpelling p q → Projects p f → Projects q l →
        Projects (.join p q) (.join f l)

  inductive ProjectsArgs : List Pattern → List Pattern → Prop where
    | nil : ProjectsArgs [] []
    | cons : Projects first f → ProjectsArgs last l → ProjectsArgs (first::last) (f::l)
end

mutual
  theorem projected_tree_produces_the_exact_spelling459 :
      ∀ {p q : Pattern}, Projects p q → pruneRepeatedTags p = q
    | _,_,.var => rfl
    | _,_,.app items => by simp [pruneRepeatedTags,projected_args_produce_the_exact_spelling459 items]
    | _,_,.record f l => by
      simp [pruneRepeatedTags,projected_tree_produces_the_exact_spelling459 f,projected_tree_produces_the_exact_spelling459 l]
    | _,_,.variant sub => by simp [pruneRepeatedTags,projected_tree_produces_the_exact_spelling459 sub]
    | _,_,.repeated sub => by
      rw [pruneRepeatedTags,ite_eq_left ((exactly_written_duplicate_test459 ..).mpr ⟨_,_,rfl,rfl⟩)]
      exact projected_tree_produces_the_exact_spelling459 sub
    | _,_,.keepJoin different f l => by
      have stay := mt (exactly_written_duplicate_test459 ..).mp different
      simp [pruneRepeatedTags,stay,projected_tree_produces_the_exact_spelling459 f,
        projected_tree_produces_the_exact_spelling459 l]
  theorem projected_args_produce_the_exact_spelling459 :
      ∀ {p q : List Pattern}, ProjectsArgs p q → pruneRepeatedTagsArgs p = q
    | _,_,.nil => rfl
    | _,_,.cons h t => by
      simp [pruneRepeatedTagsArgs,projected_tree_produces_the_exact_spelling459 h,
        projected_args_produce_the_exact_spelling459 t]
end

mutual
  theorem reify_projected_source_tree459 : ∀ p : Pattern, Projects p (pruneRepeatedTags p)
    | .var _ => .var
    | .app _ args => .app (reify_projected_source_arguments459 args)
    | .record _ p q => .record (reify_projected_source_tree459 p) (reify_projected_source_tree459 q)
    | .variant _ p => .variant (reify_projected_source_tree459 p)
    | .join p q => by
      by_cases condition : isRepeatedTag p q = true
      · obtain ⟨k,t,eqP,eqQ⟩ := (exactly_written_duplicate_test459 ..).mp condition
        have prior := reify_projected_source_tree459 p
        rw [eqP] at prior
        rw [eqP,eqQ] at condition ⊢
        rw [pruneRepeatedTags,ite_eq_left condition]
        exact .repeated prior
      · simpa only [pruneRepeatedTags,ite_eq_right condition] using
          Projects.keepJoin (mt (exactly_written_duplicate_test459 ..).mpr condition)
            (reify_projected_source_tree459 p) (reify_projected_source_tree459 q)
  theorem reify_projected_source_arguments459 : ∀ p : List Pattern, ProjectsArgs p (pruneRepeatedTagsArgs p)
    | [] => .nil
    | p::ps => .cons (reify_projected_source_tree459 p) (reify_projected_source_arguments459 ps)
end

theorem actual_inductive_projection_iff_computed459 (p q : Pattern) :
    Projects p q ↔ pruneRepeatedTags p = q := by
  constructor
  · exact projected_tree_produces_the_exact_spelling459
  · rintro rfl
    exact reify_projected_source_tree459 p

theorem actual_inductive_args_projection_iff_computed459 (p q : List Pattern) :
    ProjectsArgs p q ↔ pruneRepeatedTagsArgs p = q := by
  constructor
  · exact projected_args_produce_the_exact_spelling459
  · rintro rfl
    exact reify_projected_source_arguments459 p

theorem no_instantiation_selected_by_inductive_projection459 {p q}
    (actual : Projects p q) (capture : Nat → Pattern) :
    normalize (q.subst capture) = normalize (p.subst capture) := by
  rw [←projected_tree_produces_the_exact_spelling459 actual]
  exact same_normalization_under_every_capture459 p capture

end Yulang.GeneralDeclarativeI65.I72.InductiveTagProjection459
