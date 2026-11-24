import Yulang.GeneralDeclarativeI65I72VariableInstance403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Actual literal variable-only shape, now including repeated binders.
As required by spec 6.3 (Nov. 16), eligibility does not test centers. -/
structure RepeatedRow403 (q : Request) (d : Declaration) where
  binders : List Nat
  literal : d.head = binders.map Pattern.var
  sameArity : binders.length = q.demand.arguments.length

structure RepeatedScope403 (s : State) (q : Request) where
  ready : ∀ a ∈ q.demand.arguments, SourceArgument403 s a
  checked : Checked (authoredRegistry s.core.current)
  covered : ∀ d ∈ visible s.core q, DeclarationCovered s.core.current.environment d
  allVisible : ∀ d ∈ visible s.core q, RepeatedRow403 q d

/-- One literal role choice in the all-variable subrule. No center
equation, result type, output target or model is a field. -/
structure RepeatedElection403 (s : State) (q : Request) (d : Declaration) where
  scope : RepeatedScope403 s q
  rawSafe : ¬ RootCycle s q
  sole : visible s.core q = [d]

/-- Uses occurrence-order input triples. The stored value of the named
binder is the first occurrence; the later actual names are reconciled
with that named binder by an explicit post-selection batch. -/
def selectedInputSpans403 (q : Request) {d : Declaration} (row : RepeatedRow403 q d) :
    List (Nat × Capture) :=
  row.binders.zip q.demand.arguments

def selectedInput403 (q : Request) {d : Declaration} (row : RepeatedRow403 q d) : Nat → Capture :=
  bindings403 row.binders q.demand.arguments


/-- Exact original first binder occurrence, even if later occurrences
share that binder. A default/padding value never supplies this read. -/
theorem first_binding_at_original403 {ns : List Nat} {as : List Capture}
    (lengths : ns.length = as.length) {i n : Nat} {a : Capture}
    (binder : ns[i]? = some n) (arg : as[i]? = some a)
    (first : ∀ j : Nat, j < i → ns[j]? ≠ some n) :
    bindings403 ns as n = a := by
  induction ns generalizing as i with
  | nil => simp at binder
  | cons k ns ih =>
    cases as with
    | nil => simp at lengths
    | cons b as =>
      cases i with
      | zero =>
        simp at binder arg
        subst n; subst a
        simp [bindings403]
      | succ i =>
        have nb : ns[i]? = some n := by simpa using binder
        have ab : as[i]? = some a := by simpa using arg
        have neq : n ≠ k := by
          intro same
          exact first 0 (Nat.zero_lt_succ i) (by simp [same])
        have rest : ∀ j : Nat, j < i → ns[j]? ≠ some n := by
          intro j less atSeen
          exact first (j+1) (Nat.succ_lt_succ less) (by simpa using atSeen)
        simpa [bindings403,List.lookup,beq_eq_false_iff_ne.mpr neq] using
          (ih (Nat.succ.inj lengths) nb ab rest)

def centerTie403 (capture : Nat → Capture) (entry : Nat × Capture) : Equation :=
  ⟨entry.2.center,.variable (capture entry.1).center⟩

def selectedCenterRows403 (q : Request) {d : Declaration} (row : RepeatedRow403 q d) :
    List Equation :=
  ((selectedInputSpans403 q row).filter
    fun entry => entry.2.center != (selectedInput403 q row entry.1).center).map
      (centerTie403 (selectedInput403 q row))

theorem RepeatedElection403.inScope {s q d} (e : RepeatedElection403 s q d) :
    d ∈ visible s.core q := by rw [e.sole]; exact List.mem_cons_self

def RepeatedElection403.row {s q d} (e : RepeatedElection403 s q d) : RepeatedRow403 q d :=
  e.scope.allVisible d e.inScope

/-- The selected rule reads its obligations from this very ordinary
snapshot; an unavailable obligation is not a new reason to delay.
Root-K2 and candidate choice remain pre-output, separate from these rows. -/
def RetainedCenterRows403 {s q d} (e : RepeatedElection403 s q d) : Prop :=
  ∀ eq ∈ selectedCenterRows403 q e.row, eq ∈ s.core.current.ordinary.equations

theorem binder_center_batch_exact403 {q d} (row : RepeatedRow403 q d) {eq : Equation} :
    eq ∈ selectedCenterRows403 q row ↔
      ∃ n a, (n,a) ∈ selectedInputSpans403 q row ∧
        a.center ≠ (selectedInput403 q row n).center ∧ eq = ⟨a.center,.variable
          (selectedInput403 q row n).center⟩ := by
  simp only [selectedCenterRows403,List.mem_map,List.mem_filter,bne_iff_ne]
  constructor
  · rintro ⟨⟨n,a⟩,⟨spans,diff⟩,rfl⟩
    exact ⟨n,a,spans,diff,rfl⟩
  · rintro ⟨n,a,spans,diff,rfl⟩
    exact ⟨(n,a),⟨spans,diff⟩,rfl⟩

theorem binder_center_batch_model403 {s q d} (e : RepeatedElection403 s q d)
    (m : Model) :
    Models (appendFacts s.core.current.ordinary (selectedCenterRows403 q e.row)) m.assignment ↔
      Models s.core.current.ordinary m.assignment ∧
      ∀ n a, (n,a) ∈ selectedInputSpans403 q e.row →
        CommonNominalFullCarrier.Equivalent
          (m.assignment a.center).1
          (m.assignment (selectedInput403 q e.row n).center).1 := by
  rw [model_append]
  constructor
  · rintro ⟨base,rows⟩
    refine ⟨base,fun n a atPos => ?_⟩
    by_cases eq : a.center = (selectedInput403 q e.row n).center
    · rw [eq]
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · have satisfied := rows _ ((binder_center_batch_exact403 e.row).2 ⟨n,a,atPos,eq,rfl⟩)
      exact satisfied
  · rintro ⟨base,tied⟩
    refine ⟨base,fun eq found => ?_⟩
    obtain ⟨n,a,atPos,_,same⟩ := (binder_center_batch_exact403 e.row).1 found
    rw [same]
    exact tied n a atPos

private theorem zipped_head_reads403 (s : State) (capture : Nat → Capture)
    (ns : List Nat) (as : List Capture) (len : ns.length = as.length)
    (bounds : ∀ a ∈ as, Bounds s.core.current.ordinary a)
    (center : ∀ x ∈ ns.zip as,
      GeneralDeclarativeNormalized320.Center s.core.current.ordinary capture x.2 (.variable x.1)) :
    All₂ (DeepHead s.core capture) as (ns.map Pattern.var) := by
  induction ns generalizing as with
  | nil =>
    cases as with
    | nil => exact .nil
    | cons => simp at len
  | cons n ns ih =>
    cases as with
    | nil => simp at len
    | cons a as =>
      refine .cons (.ordinary ⟨bounds a List.mem_cons_self,.variable n,rfl,
        center (n,a) (by simp)⟩) (ih as (Nat.succ.inj len) ?_ ?_)
      · exact fun b seen => bounds b (List.mem_cons_of_mem _ seen)
      · exact fun b seen => center b (List.mem_cons_of_mem _ seen)

theorem selected_repeated_center_read403 {s q d} (e : RepeatedElection403 s q d)
    (retained : RetainedCenterRows403 e) {n a} (atPos : (n,a) ∈ selectedInputSpans403 q e.row) :
    GeneralDeclarativeNormalized320.Center s.core.current.ordinary
      (selectedInput403 q e.row) a (.variable n) := by
  by_cases same : a.center = (selectedInput403 q e.row n).center
  · apply GeneralDeclarativeNormalized320.Center.direct
    apply GeneralDeclarativeSubstitution320.EquationRead.structural
    apply GeneralDeclarativeHead320.Read.capture
    · change GeneralDeclarativeBounds319.Bound _ a.center (selectedInput403 q e.row n).center
      rw [same]
      exact .refl _
    · change GeneralDeclarativeBounds319.Bound _ (selectedInput403 q e.row n).center a.center
      rw [same]
      exact .refl _
  · have member := retained _ ((binder_center_batch_exact403 e.row).mpr ⟨n,a,atPos,same,rfl⟩)
    exact .direct (.whole member)

def selectedRepeatedCandidate403 {s q d} (e : RepeatedElection403 s q d)
    (retained : RetainedCenterRows403 e) : AuthoredCandidate s.core q d :=
  ⟨e.inScope,e.scope.covered d e.inScope,
    (e.scope.checked.2 d ((visible_exact s.core q d).mp e.inScope).1).signature,
    .ordered (selectedInput403 q e.row) (by
      rw [e.row.literal]
      exact zipped_head_reads403 s _ e.row.binders q.demand.arguments e.row.sameArity
        (fun a atArg => (e.scope.ready a atArg).bounds)
        (fun ⟨n,a⟩ atPos => selected_repeated_center_read403 e retained atPos))⟩

/-- The exact current captured source is named at original registry
ordinal, then used by the already audited C401 B6 readback. -/
def selectedRepeatedTape403 {s q d} (e : RepeatedElection403 s q d)
    (retained : RetainedCenterRows403 e) : CandidateTape s.core q (visible s.core q) :=
  e.sole.symm ▸ .next (.matched (selectedRepeatedCandidate403 e retained)) .nil

theorem selected_repeated_tape_exact403 {s q d} (e : RepeatedElection403 s q d)
    (retained : RetainedCenterRows403 e) : TapedMatch s.core q (selectedRepeatedTape403 e retained) d := by
  have h : ∀ rows (eq : rows = [d]),
      let t : CandidateTape s.core q rows := eq.symm ▸ .next
        (.matched (selectedRepeatedCandidate403 e retained)) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows eq
    subst rows
    exact ⟨rfl,rfl⟩
  exact ⟨e.rawSafe,(h _ e.sole).1,(h _ e.sole).2⟩

end Yulang.GeneralDeclarativeI65.I72
