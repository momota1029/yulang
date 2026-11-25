import Yulang.GeneralDeclarativeI65I74OpenTailIsolation414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs counted encodeArgs coveredArgs
  CountsCovered Smaller StableSmaller)
open GeneralDeclarations (Declaration)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)

/-- The literal X4 tail child is strictly smaller in the original
written, shadow-normalized rows. It is not an arbitrary substitution
for the tail, and is not generated at the pending goal. -/
theorem literal_tail_child_is_smaller414 (label intName binder : Nat) :
    CountsCovered [openHead label intName binder] [.var binder] ∧
    Smaller [openHead label intName binder] [.var binder] := by
  constructor
  · simp [CountsCovered,coveredArgs,openHead,normalizeArgs,normalize,GeneralDeclarationPatterns.hide,GeneralDeclarationPatterns.covered]
  · constructor
    · simp [openHead,counted,normalizeArgs,normalize,GeneralDeclarationPatterns.hide,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
    · intro n
      simp [openHead,counted,normalizeArgs,normalize,GeneralDeclarationPatterns.hide,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem actual_candidate_retains_written_tail_child414 {s q} {a : OpenInput s q}
    (d : OpenCandidate a) :
    CountsCovered d.decl.head ((tailRequirement q.demand.role d.binder d.clause).arguments) ∧
    Smaller d.decl.head ((tailRequirement q.demand.role d.binder d.clause).arguments) := by
  rw [d.head]
  exact literal_tail_child_is_smaller414 a.label d.intName d.binder

def literalOpenPattern (label binder : Nat) : Expr :=
  .record label (.primitive (.scalar .int) []) (.variable binder)

theorem independently_translated_open_candidate414 {s q} {a : OpenInput s q}
    (d : OpenCandidate a) :
    translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (normalize (openHead a.label d.intName d.binder)) =
      some (literalOpenPattern a.label d.binder) := by
  simp [openHead,normalize,normalizeArgs,GeneralDeclarationPatterns.hide,literalOpenPattern,translate,translateMany,d.actualInt]

/-- Exact spec 6.3 boundary: allowing an arbitrary solved-looking
substitution for the *written* tail would produce the known shadow
collapse. The deferred rule does not do that and imposes no old all-
substitutions admission test on the source declaration. -/
theorem arbitrary_shadow_substitution_is_not_the_X4_rule414
    (label intName binder empty : Nat) :
    ¬ StableSmaller [openHead label intName binder] [.var binder] := by
  intro globally
  have bad := (globally (fun _ => .record label (.app intName []) (.app empty []))).1
  simp [GeneralDeclarationPatterns.substArgs,Pattern.subst,openHead,
    counted,normalizeArgs,normalize,GeneralDeclarationPatterns.hide] at bad

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
