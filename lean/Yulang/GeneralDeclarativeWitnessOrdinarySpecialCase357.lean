import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrdinarySpecialCase357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use SourceMode)
open GeneralDeclarativeWitnessModeCoverage357 (Covers CoversList TermCovered TermsCovered Coverage)
open GeneralDeclarativeWitnessSparseVariance357 (lookup)
open GeneralDeclarationPatterns (Pattern Constructor)
open GeneralSourceMetadataRows291 (constructors interpretation)
open GeneralSourceMetadataBundle291 (registry)

abbrev old := GeneralNominalCenteredHeadWFSource.Coverage

structure OrdinarySource (e : Environment) : Prop where
  absent : ∀ key,lookup e.graph key = none
  aligned : constructors e.source.snapshot = constructors e.source.declared
  named : ∀ n c,constructors e.source.declared n = some c → c.name = n
  explicit : e.source.declared.fallback = .absent ∧ e.source.snapshot.fallback = .absent

theorem constructors_exact {e : Environment} (ordinary : OrdinarySource e) (name arity : Nat) :
    Nonempty (Use e name arity) ↔
      GeneralNominalCenteredHeadWFSource.ConstructorUse (registry e.source).constructors
        (interpretation e.source.snapshot) name arity := by
  constructor
  · rintro ⟨⟨ctor,snap,orig,live,n0,n1,same,arityEq,mode,checked,layout,explicit⟩⟩
    refine ⟨ctor,orig,arityEq,?_⟩
    cases checked with
    | primitive hit _ => exact .inl ⟨_,hit,layout⟩
    | invariant hit _ =>
      refine .inr ⟨hit,?_⟩
      change ctor.parameters = List.replicate ctor.parameters.length .type at layout
      simpa only [arityEq] using layout
    | declared present _ _ =>
      rw [ordinary.absent name] at present
      cases present
  · rintro ⟨ctor,started,arityEq,c₀|c₁⟩
    · obtain ⟨op,metadata,layout⟩ := c₀
      have aligned : constructors e.source.snapshot name = some ctor := by rw [ordinary.aligned]; exact started
      have named := ordinary.named name ctor started
      exact ⟨⟨ctor,ctor,started,aligned,named,named,rfl,arityEq,.primitive op,
        .primitive metadata (ordinary.absent name),layout,ordinary.explicit⟩⟩
    · obtain ⟨mode,layout⟩ := c₁
      have aligned : constructors e.source.snapshot name = some ctor := by rw [ordinary.aligned]; exact started
      have named := ordinary.named name ctor started
      exact ⟨⟨ctor,ctor,started,aligned,named,named,rfl,arityEq,.invariant,
        .invariant mode (ordinary.absent name),by simpa [GeneralDeclarativeWitnessConstructorModes357.Layout,arityEq] using layout,
        ordinary.explicit⟩⟩

mutual
theorem pattern_case {e : Environment} (ordinary : OrdinarySource e) :
    ∀ p : Pattern, Covers e p ↔ GeneralNominalCenteredHeadWFSource.PatternCovered
      (registry e.source).constructors (interpretation e.source.snapshot) p
  | .var _ => Iff.rfl
  | .app name args => and_congr (constructors_exact ordinary name args.length) (patterns_case ordinary args)
  | .record _ a b => and_congr (pattern_case ordinary a) (pattern_case ordinary b)
  | .variant _ a => pattern_case ordinary a
  | .join a b => and_congr (pattern_case ordinary a) (pattern_case ordinary b)

theorem patterns_case {e : Environment} (ordinary : OrdinarySource e) :
    ∀ ps : List Pattern, CoversList e ps ↔ GeneralNominalCenteredHeadWFSource.PatternsCovered
      (registry e.source).constructors (interpretation e.source.snapshot) ps
  | [] => Iff.rfl
  | a::b => and_congr (pattern_case ordinary a) (patterns_case ordinary b)
end

mutual
theorem term_case {e : Environment} (ordinary : OrdinarySource e) :
    ∀ p : Roles.Term, TermCovered e p ↔ GeneralNominalCenteredHeadWFSource.TermCovered
      (registry e.source).constructors (interpretation e.source.snapshot) p
  | .var _ => Iff.rfl
  | .app name args => and_congr (constructors_exact ordinary name args.length) (terms_case ordinary args)

theorem terms_case {e : Environment} (ordinary : OrdinarySource e) :
    ∀ ps : List Roles.Term, TermsCovered e ps ↔ GeneralNominalCenteredHeadWFSource.TermsCovered
      (registry e.source).constructors (interpretation e.source.snapshot) ps
  | [] => Iff.rfl
  | a::b => and_congr (term_case ordinary a) (terms_case ordinary b)
end

theorem declaration_case {e : Environment} (ordinary : OrdinarySource e)
    (d : GeneralDeclarations.Declaration) :
    GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered e d ↔
      GeneralNominalCenteredHeadWFSource.DeclarationCovered (registry e.source).constructors
        (interpretation e.source.snapshot) d := by
  simp only [GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered,
    GeneralNominalCenteredHeadWFSource.DeclarationCovered,pattern_case ordinary,patterns_case ordinary]

theorem coverage_case {e : Environment} (ordinary : OrdinarySource e) :
    Coverage e ↔ old (registry e.source) (interpretation e.source.snapshot) := by
  simp only [Coverage,GeneralDeclarativeWitnessModeCoverage357.DefaultsCovered,
    old,GeneralNominalCenteredHeadWFSource.Coverage,GeneralNominalCenteredHeadWFSource.DefaultsCovered,
    declaration_case ordinary,term_case ordinary]
  rfl

end Yulang.GeneralDeclarativeWitnessOrdinarySpecialCase357
