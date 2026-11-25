import Yulang.GeneralDeclarativeI65I72CompletedNativeTape407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal names visited visitedList)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open PresenceNormalForm (Atom)

structure NativeUpperTest407 {s q need} (read : CompletedRead407 s q need) where
  upper : Origin
  upperAuthored : upper ∈ s.core.origins
  upperRoute : OriginRoute s.core upper read.arg.upper
  upperPayload : Nat
  upperLiteral : upper.endpoint = unaryNominalPoint404 read.found upperPayload
  compared : Atom.tyLe (.var read.sourcePayload) (.var upperPayload) ∈ s.core.current.ordinary.normal.ordinary

theorem actual_native_upper_derives_comparison407 {s q need}
    (read : CompletedRead407 s q need) (upper : NativeUpperTest407 read) :
    Nonempty (DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes
      false (unaryNominalPoint404 read.found read.sourcePayload)
        (unaryNominalPoint404 read.found upper.upperPayload)) := by
  obtain ⟨use,mode,table⟩ := original_typed_point_has_canonical_declared_mode404 need.expected.rhs read.sourceType
  have authority : Legal s.core.current.environment s.core.modes (read.found,1) := by
    refine ⟨use,[coValue404],?_,table⟩
    change names use.mode 1 = some [coValue404]
    rw [mode]; rfl
  have well : ∀ name, ContextWellFormed s.core.modes false (unaryNominalPoint404 read.found name) :=
    fun _ => .nominal table (.cons (.valuePoint (.ordinary false _)) (.nil false))
  refine ⟨⟨?_,well _,well _,.nominal table (.cons (.covariantValue (.ordinary upper.compared)) .nil)⟩⟩
  intro candidate atCandidate
  have exactIndex : candidate = (read.found,1) := by
    simpa [unaryNominalPoint404,visited,visitedList] using atCandidate
  exact exactIndex ▸ authority

/-- Scope: all visible rows are literal declared unary constructors
with variable children. All root tags are actually observed from the
same completed lower. Same-tag rows require a real comparison, not
a negative hypothesis or lack of evidence about other candidates. -/
structure NativeElectionInput407 (s : State) (q : Request) (need : OutputNeed s) where
  read : CompletedRead407 s q need
  roots : ∀ i : VisibleIndex407 s q, VisibleRoot407 s q i
  checked : Checked (authoredRegistry s.core.current)
  covers : ∀ i : VisibleIndex407 s q, DeclarationCovered s.core.current.environment (visible s.core q)[i]
  positive : NativeUpperTest407 read
  rawSafe : ¬RootCycle s q

def NativeElectionInput407.live {s q need} (input : NativeElectionInput407 s q need) :
    List (VisibleIndex407 s q) :=
  (List.finRange (visible s.core q).length).filter (fun j => TagAgrees407 input.read (input.roots j))

theorem native_live_is_exact_not_first_match407 {s q need} (input : NativeElectionInput407 s q need)
    (i : VisibleIndex407 s q) :
    i ∈ input.live ↔ DeclaredHead404 (input.roots i).unary.key need.expected.rhs := by
  simp [NativeElectionInput407.live, (exact_source_classifies_tag407 input.read (input.roots i)).1]

theorem native_same_tag_really_gets_local_comparison407 {s q need} (input : NativeElectionInput407 s q need)
    (i : VisibleIndex407 s q) (live : i ∈ input.live) :
    Nonempty (DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes
      false (unaryNominalPoint404 (input.roots i).unary.key input.read.sourcePayload)
        (unaryNominalPoint404 (input.roots i).unary.key input.positive.upperPayload)) := by
  have tag := actual_typed_point_yields_literal_declared_code404 need.expected.rhs input.read.sourceType
  have same := a_literal_typed_nominal_cannot_name_different_constructors406 _
    ((native_live_is_exact_not_first_match407 input i).mp live) tag.1
  rw [same]
  exact actual_native_upper_derives_comparison407 input.read input.positive

/-- An exact selection at the local head stage, before any body or
original center read. Both the survivor and all losing roots are
identified by original visible ordinal; no declared binding is erased. -/
structure ElectedNativeHead407 {s q need} (input : NativeElectionInput407 s q need) where
  winner : VisibleIndex407 s q
  one : input.live = [winner]

theorem exact_single_native_hit_elects407 {s q need} (input : NativeElectionInput407 s q need)
    (i : VisibleIndex407 s q) (matchTag : (input.roots i).unary.key = input.read.found)
    (allRivals : ∀ j : VisibleIndex407 s q, j ≠ i → (input.roots j).unary.key ≠ input.read.found) :
    Nonempty (ElectedNativeHead407 input) := by
  refine ⟨⟨i,?_⟩⟩
  have filterSpec : ∀ j : VisibleIndex407 s q,
      TagAgrees407 input.read (input.roots j) = decide (j = i) := by
    intro j
    by_cases same : j = i
    · subst j; simp [TagAgrees407,matchTag]
    · simp [TagAgrees407,same,allRivals _ same]
  change List.filter (fun j => TagAgrees407 input.read (input.roots j))
    (List.finRange (visible s.core q).length) = [i]
  simp only [filterSpec]
  let chosen := List.filter (fun j => decide (j = i)) (List.finRange (visible s.core q).length)
  change chosen = [i]
  have n : chosen.Nodup := (List.nodup_finRange _).filter _
  have m : i ∈ chosen := by simp [chosen]
  have unique : ∀ j ∈ chosen, j = i := by simp [chosen]
  cases eq : chosen with
  | nil => simp [eq] at m
  | cons hd tl =>
    have a : hd = i := unique hd (by simp [eq])
    subst hd
    rw [eq] at n
    have no := (List.nodup_cons.mp n).1
    cases tl with
    | nil => rfl
    | cons z zs =>
      have same := unique z (by simp [eq])
      subst z
      exact (no (by simp)).elim

theorem election_keeps_every_other_actual_mismatch407 {s q need} {input : NativeElectionInput407 s q need}
    (election : ElectedNativeHead407 input) :
    DeclaredHead404 (input.roots election.winner).unary.key need.expected.rhs ∧
    ∀ j : VisibleIndex407 s q, j ≠ election.winner →
      ¬ DeclaredHead404 (input.roots j).unary.key need.expected.rhs := by
  constructor
  · exact (native_live_is_exact_not_first_match407 input election.winner).mp (by simp [election.one])
  · intro j notWinner same
    have member := (native_live_is_exact_not_first_match407 input j).mpr same
    rw [election.one] at member
    exact notWinner (List.mem_singleton.mp member)

end Yulang.GeneralDeclarativeI65.I72
