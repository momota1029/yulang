import YulangClosure.SimpleSubConstraintSyntax

/-!
R233 stops before defining cached constraining: a paper/source equation is
absent from the frozen structural relation. Paper section 3.2.2 / Fig. 9 and
the pinned Typer.scala:108--114 accept record width. SimpleSub.Sub.recordCons
preserves complete row shape instead; the source module explicitly disclaims
complete optional-row admission. Neither definition is changed here.

The finite pair below requires just one reflexive field comparison in Fig. 9,
but is not related by Sub, even with its transitivity/lattice rules. The
recordDepth interpretation is solely a separating invariant of that existing
inductive relation, not a source semantics, solver readout, or new constrain
operation. All constructors and both kinds of the existing relation remain
in its quantified domain, including the four-port Function rule.

No cached-constrain preservation, Yulang typing counterexample, native
correspondence, parent closure, or production claim follows. Luna owns pinned
verification; the audit commands at the end are requests, not receipts.
-/
namespace YulangClosure.SimpleSub.CachedConstrainR233

/-- A separating interpretation of complete record-tail depth. Other
constructors are interpreted constantly, except for the lattice operations.
This definition gives no source typing or algorithmic meaning to a term. -/
def recordDepth : {kind : Kind} → Term kind → Nat → Prop
  | _, .var _, _ => False
  | _, .atom _, _ => False
  | _, .bottom, _ => False
  | _, .top, _ => True
  | _, .union left right, depth => recordDepth left depth ∨ recordDepth right depth
  | _, .intersection left right, depth => recordDepth left depth ∧ recordDepth right depth
  | _, .function _ _ _ _, _ => False
  | _, .recordNil, depth => depth = 0
  | _, .recordCons _ _ _ _, 0 => False
  | _, .recordCons _ _ _ tail, depth + 1 => recordDepth tail depth
  | _, .tupleNil, _ => False
  | _, .tupleCons _ _, _ => False
  | _, .variantNil, _ => False
  | _, .variantCons _ _ _, _ => False

/-- All rules of the frozen Sub, including transitivity and its lattice
rules, preserve this separating interpretation. -/
theorem recordDepth_mono {kind : Kind} {lower upper : Term kind}
    (comparison : Sub lower upper) :
    ∀ depth, recordDepth lower depth → recordDepth upper depth := by
  induction comparison with
  | refl term =>
      intro depth member
      exact member
  | trans _ _ first second =>
      intro depth member
      exact second depth (first depth member)
  | bottom term =>
      intro depth member
      exact False.elim member
  | top term =>
      intro depth member
      exact True.intro
  | unionLeft left right =>
      intro depth member
      exact Or.inl member
  | unionRight left right =>
      intro depth member
      exact Or.inr member
  | unionElim _ _ left right =>
      intro depth member
      cases member with
      | inl member => exact left depth member
      | inr member => exact right depth member
  | intersectionLeft left right =>
      intro depth member
      exact member.1
  | intersectionRight left right =>
      intro depth member
      exact member.2
  | intersectionIntro _ _ left right =>
      intro depth member
      exact ⟨left depth member, right depth member⟩
  | unionMono _ _ left right =>
      intro depth member
      cases member with
      | inl member => exact Or.inl (left depth member)
      | inr member => exact Or.inr (right depth member)
  | intersectionMono _ _ left right =>
      intro depth member
      exact ⟨left depth member.1, right depth member.2⟩
  | function _ _ _ _ argument argumentEffect resultEffect result =>
      intro depth member
      exact False.elim member
  | recordCons label optional _ _ field tail =>
      intro depth member
      cases depth with
      | zero => exact False.elim member
      | succ depth => exact tail depth member
  | tupleCons _ _ head tail =>
      intro depth member
      exact False.elim member
  | variantCons tag _ _ payloads tail =>
      intro depth member
      exact False.elim member

/-- Two required, distinct, ordered fields. -/
def widthLower : Term .value :=
  .recordCons 0 false (.atom 0) (.recordCons 1 false (.atom 1) .recordNil)

/-- Fig. 9 demands only this field on the right. -/
def widthUpper : Term .value :=
  .recordCons 0 false (.atom 0) .recordNil

def widthDemand : Constraint := ⟨.value, widthLower, widthUpper⟩

/-- The sole recursive comparison in the paper's width example is reflexive.
This is not a formalization of the complete paper constrain relation. -/
theorem width_field_reflexive : Sub (.atom 0 : Term .value) (.atom 0) :=
  Sub.refl _

/-- An unconditional finite obstruction in the frozen structural relation. -/
theorem width_not_sub : ¬ Sub widthLower widthUpper := by
  intro comparison
  have lower : recordDepth widthLower 2 := rfl
  have upper : recordDepth widthUpper 2 := recordDepth_mono comparison 2 lower
  exact Nat.noConfusion upper

/-- Substitution cannot repair this ground pair. This concerns the existing
structural satisfaction definition, not original source typability. -/
theorem width_rejected_by_every_valuation (valuation : Valuation) :
    ¬ widthDemand.Satisfied valuation := by
  intro satisfied
  exact width_not_sub satisfied

end YulangClosure.SimpleSub.CachedConstrainR233

#check @YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation
