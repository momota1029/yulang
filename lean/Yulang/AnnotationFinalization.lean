import Yulang.AnnotationSnapshots
import Yulang.Horn

/-!
# Positive annotations at binding/SCC finalization

Spec §5.5b fixes the observation point after a binding's entire inference unit,
before generalization. This module implements that point for the finite Horn
fact layer: collect every member's constraints, solve them together, then freeze
the requested signed rows. The least solution is computed, not supplied with an
assumption of order independence. Clause order, duplicates, and member order do
not affect acceptance. A member keeps its resolved fact/row identifiers when
the collection order changes.

Facts name concrete signed occurrences at row slots. Pending rows retain the
existing protection/release/residual syntax. The finite fact interface and its
translation from structural inference are explicit inputs; this is not a solver
for arbitrary recursive types or unbounded signed stacks. After finalization,
scheme instantiation acts on the formula, never on the saved observations.
Nested bindings finalize their own units independently of their parent's unit.
-/

namespace Yulang.AnnotationFinalization

open AnnotationSnapshots
open RowInference (RowExpr signedAlgebra)

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right <;> simp_all

/-- The concrete Horn algorithm is extensional in its full set of models. -/
theorem solve_congr (left right : Horn.Problem k)
    (same : ∀ value, Horn.Models left value ↔ Horn.Models right value) :
    Horn.solve left = Horn.solve right := by
  have checks : Horn.check left = Horn.check right := by
    funext value
    apply bool_eq_of_true_iff
    simpa only [Horn.check_iff] using same value
  simp only [Horn.solve, Horn.allModels, checks]

theorem solve_membership (left right : Horn.Problem k)
    (same : ∀ clause, clause ∈ left ↔ clause ∈ right) :
    Horn.solve left = Horn.solve right := by
  apply solve_congr
  intro value
  constructor
  · intro model clause member
    exact model clause ((same clause).mpr member)
  · intro model clause member
    exact model clause ((same clause).mp member)

theorem solve_permutation {left right : Horn.Problem k} (permutation : left.Perm right) :
    Horn.solve left = Horn.solve right :=
  solve_membership left right (fun _ => permutation.mem_iff)

/-- A true least-solution fact is precisely a consequence of the whole unit. -/
theorem known_iff_forced (problem : Horn.Problem k) (value : Horn.Valuation k)
    (solved : Horn.solve problem = some value) (fact : Fin k) :
    value fact = true ↔ ∀ other, Horn.Models problem other → other fact = true := by
  have least := Horn.solve_principal problem value solved
  exact ⟨fun known other model => least.2 other model fact known,
    fun forced => forced value least.1⟩

abbrev Facts (scopes : Nat) (Key Slot : Type) (k : Nat) :=
  Fin k → Slot × Directed.Occurrence scopes Key

/-- Fixed fact enumeration makes snapshots independent of constraint traversal. -/
def rows [DecidableEq Slot] (facts : Facts scopes Key Slot k)
    (value : Horn.Valuation k) (slot : Slot) : Directed.Row scopes Key :=
  ((List.finRange k).filter fun fact =>
    value fact && decide ((facts fact).1 = slot)).map fun fact => (facts fact).2

theorem selected_fact_mem [DecidableEq Slot] (facts : Facts scopes Key Slot k)
    (value : Horn.Valuation k) (fact : Fin k) (selected : value fact = true) :
    (facts fact).2 ∈ rows facts value (facts fact).1 := by
  apply List.mem_map.mpr
  exact ⟨fact, by simp [selected], rfl⟩

structure Pending (scopes : Nat) (Key Slot : Type) where
  permission : Key → Bool
  row : RowExpr Key (Fin scopes) Slot

def Pending.freeze [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (value : Horn.Valuation k)
    (pending : Pending scopes Key Slot) : Observation scopes Key :=
  ⟨pending.permission, pending.row.eval (signedAlgebra scopes Key) (rows facts value)⟩

def snapshots [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (value : Horn.Valuation k)
    (pending : List (Pending scopes Key Slot)) : List (Observation scopes Key) :=
  pending.map (Pending.freeze facts value)

/-- No observation is taken until all constraints of this unit are available. -/
def finalize [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) : Option (List (Observation scopes Key)) :=
  match Horn.solve problem with
  | none => none
  | some value =>
      let history := snapshots facts value pending
      if checkHistory history then some history else none

def check [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) : Bool :=
  match Horn.solve problem with
  | none => false
  | some value => checkHistory (snapshots facts value pending)

/-- Declarative specification: a least model and admissible final observations. -/
def Finalized [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (history : List (Observation scopes Key)) : Prop :=
  ∃ value, Horn.IsLeastModel problem value ∧
    history = snapshots facts value pending ∧ HistoryAdmissible history

theorem finalize_exact [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (history : List (Observation scopes Key)) :
    finalize facts problem pending = some history ↔ Finalized facts problem pending history := by
  constructor
  · intro accepted
    cases solved : Horn.solve problem with
    | none => simp [finalize, solved] at accepted
    | some value =>
        cases valid : checkHistory (snapshots facts value pending) with
        | false => simp [finalize, solved, valid] at accepted
        | true =>
            have equal : snapshots facts value pending = history := by
              simpa [finalize, solved, valid] using accepted
            exact ⟨value, Horn.solve_principal problem value solved, equal.symm,
              equal ▸ (checkHistory_exact _).mp valid⟩
  · rintro ⟨value, least, equal, valid⟩
    have solved := (Horn.solve_eq_some_iff problem value).mpr least
    have checked := (checkHistory_exact history).mpr valid
    simp [finalize, solved, ← equal, checked]

theorem check_exact [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) :
    check facts problem pending = true ↔
      ∃ value, Horn.IsLeastModel problem value ∧
        HistoryAdmissible (snapshots facts value pending) := by
  constructor
  · intro accepted
    cases solved : Horn.solve problem with
    | none => simp [check, solved] at accepted
    | some value =>
        exact ⟨value, Horn.solve_principal problem value solved,
          (checkHistory_exact _).mp (by simpa [check, solved] using accepted)⟩
  · rintro ⟨value, least, valid⟩
    simp [check, (Horn.solve_eq_some_iff problem value).mpr least,
      (checkHistory_exact _).mpr valid]

theorem finalized_iff_checked [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) :
    (finalize facts problem pending).isSome = check facts problem pending := by
  cases solved : Horn.solve problem with
  | none => simp [finalize, check, solved]
  | some value =>
      cases valid : checkHistory (snapshots facts value pending) <;>
        simp [finalize, check, solved, valid]

theorem finalize_constraint_order [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) {left right : Horn.Problem k}
    (permutation : left.Perm right) (pending : List (Pending scopes Key Slot)) :
    finalize facts left pending = finalize facts right pending := by
  simp only [finalize, solve_permutation permutation]

theorem history_check_membership (left right : List (Observation scopes Key))
    (same : ∀ observation, observation ∈ left ↔ observation ∈ right) :
    checkHistory left = checkHistory right := by
  apply bool_eq_of_true_iff
  simp only [checkHistory_exact, HistoryAdmissible]
  constructor
  · intro valid observation member
    exact valid observation ((same observation).mpr member)
  · intro valid observation member
    exact valid observation ((same observation).mp member)

theorem check_congr [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (left right : Horn.Problem k)
    (constraints : ∀ clause, clause ∈ left ↔ clause ∈ right)
    (first second : List (Pending scopes Key Slot))
    (requests : ∀ request, request ∈ first ↔ request ∈ second) :
    check facts left first = check facts right second := by
  have solved := solve_membership left right constraints
  unfold check
  rw [solved]
  cases Horn.solve right with
  | none => rfl
  | some value =>
      apply history_check_membership
      intro observation
      simp only [snapshots, List.mem_map]
      constructor
      · rintro ⟨request, member, equal⟩
        exact ⟨request, (requests request).mp member, equal⟩
      · rintro ⟨request, member, equal⟩
        exact ⟨request, (requests request).mpr member, equal⟩

structure Member (scopes : Nat) (Key Slot : Type) (k : Nat) where
  constraints : Horn.Problem k
  annotations : List (Pending scopes Key Slot)

def collectConstraints (members : List (Member scopes Key Slot k)) : Horn.Problem k :=
  members.flatMap Member.constraints

def collectAnnotations (members : List (Member scopes Key Slot k)) :
    List (Pending scopes Key Slot) := members.flatMap Member.annotations

def checkSCC [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (members : List (Member scopes Key Slot k)) : Bool :=
  check facts (collectConstraints members) (collectAnnotations members)

private theorem flatMap_membership {α β : Type} {left right : List α}
    (same : ∀ member, member ∈ left ↔ member ∈ right) (f : α → List β) (value : β) :
    value ∈ left.flatMap f ↔ value ∈ right.flatMap f := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨member, present, contains⟩
    exact ⟨member, (same member).mp present, contains⟩
  · rintro ⟨member, present, contains⟩
    exact ⟨member, (same member).mpr present, contains⟩

/-- Reordering members keeps their resolved identifiers and collected obligations. -/
theorem scc_member_order [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) {left right : List (Member scopes Key Slot k)}
    (permutation : left.Perm right) : checkSCC facts left = checkSCC facts right := by
  apply check_congr
  · exact flatMap_membership (fun _ => permutation.mem_iff) Member.constraints
  · exact flatMap_membership (fun _ => permutation.mem_iff) Member.annotations

/-- The finalization gate is applied to the generated body constraints before
they are generalized. It cannot constrain a later scheme instantiation. -/
def gate [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (formula : Inference.Formula α) :
    Inference.Formula α := if check facts problem pending then formula else .bot

theorem gate_exact [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (formula : Inference.Formula α)
    (m : Inference.Model) (ρ : α → Inference.Comp m) :
    (gate facts problem pending formula).Holds m ρ ↔
      (∃ value, Horn.IsLeastModel problem value ∧
        HistoryAdmissible (snapshots facts value pending)) ∧ formula.Holds m ρ := by
  rw [← check_exact facts problem pending]
  cases accepted : check facts problem pending <;>
    simp [gate, accepted, Inference.Formula.Holds]

theorem principal_finalized_exact [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (m : Inference.Model)
    (ρ : α → Inference.Comp m) (sΓ : Inference.SchemeEnv α)
    (Γ : List (Inference.Binding m)) (environment : Inference.EnvRel m ρ sΓ Γ)
    (expression : Inference.Expr) (result : Inference.Comp m) :
    (gate facts problem pending (Inference.principal sΓ expression)).Holds m
      (Inference.extend ρ result) ↔
      (∃ value, Horn.IsLeastModel problem value ∧
        HistoryAdmissible (snapshots facts value pending)) ∧
      Inference.Typing m Γ expression result := by
  rw [gate_exact, Inference.principal_exact m expression sΓ Γ ρ environment result]

theorem gate_subst [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (formula : Inference.Formula α)
    (σ : α → Inference.CompTerm β) :
    (gate facts problem pending formula).subst σ =
      gate facts problem pending (formula.subst σ) := by
  cases accepted : check facts problem pending <;>
    simp [gate, accepted, Inference.Formula.subst]

/-- Generalization is reached only after finalization; future substitutions
change the generated formula but never the finite solved observation history. -/
theorem later_instantiation [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (history : List (Observation scopes Key))
    (accepted : finalize facts problem pending = some history)
    (formula : Inference.Formula α) (σ : α → Inference.CompTerm β)
    (m : Inference.Model) (ρ : β → Inference.Comp m) :
    ((emit history formula).subst σ).Holds m ρ ↔
      formula.Holds m (fun name => (σ name).eval m ρ) := by
  obtain ⟨_, _, _, valid⟩ := (finalize_exact facts problem pending history).mp accepted
  exact valid_observation_adds_no_instantiation_bound history valid formula σ m ρ

theorem forced_forbidden_at_finalization [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (fact : Fin k)
    (forced : ∀ value, Horn.Models problem value → value fact = true) (permission : Key → Bool)
    (request : (⟨permission, .var (facts fact).1⟩ : Pending scopes Key Slot) ∈ pending)
    (visible : Visible (facts fact).2) (denied : permission (facts fact).2.key = false) :
    check facts problem pending = false := by
  cases accepted : check facts problem pending with
  | false => rfl
  | true =>
      obtain ⟨value, least, valid⟩ := (check_exact facts problem pending).mp accepted
      have selected : value fact = true := forced value least.1
      have observation := valid _ (List.mem_map.mpr ⟨_, request, rfl⟩)
      have allowed := observation (facts fact).2 (selected_fact_mem facts value fact selected) visible
      simp [Pending.freeze, denied] at allowed

theorem known_forbidden_at_finalization [DecidableEq Key] [DecidableEq Slot]
    (facts : Facts scopes Key Slot k) (problem : Horn.Problem k)
    (pending : List (Pending scopes Key Slot)) (fact : Fin k)
    (seed : Horn.Clause.seed fact ∈ problem) (permission : Key → Bool)
    (request : (⟨permission, .var (facts fact).1⟩ : Pending scopes Key Slot) ∈ pending)
    (visible : Visible (facts fact).2) (denied : permission (facts fact).2.key = false) :
    check facts problem pending = false :=
  forced_forbidden_at_finalization facts problem pending fact
    (fun _ model => model (.seed fact) seed (by simp [Horn.Clause.seed]))
    permission request visible denied

namespace Examples

def facts : Facts 1 Nat Nat 2 := fun fact =>
  (fact.val, ⟨1, fun _ => 0⟩)

def onlyIO : Nat → Bool := fun key => key == 0
def annotation : Pending 1 Nat Nat := ⟨onlyIO, .var 0⟩

def annotatedMember : Member 1 Nat Nat 2 :=
  ⟨[.include 1 0], [annotation]⟩
def effectfulPeer : Member 1 Nat Nat 2 :=
  ⟨[.seed 1, .include 0 1], []⟩

theorem before_body_constraints_would_accept : check facts [] [annotation] = true := by decide

theorem completed_body_effect_rejected : check facts [.seed 0] [annotation] = false := by decide

theorem peer_effect_rejected : checkSCC facts [annotatedMember, effectfulPeer] = false := by decide

theorem reordered_peer_effect_rejected :
    checkSCC facts [effectfulPeer, annotatedMember] = false := by decide

theorem changing_generation_order_keeps_snapshot :
    finalize facts [.seed 1, .include 1 0] [annotation] =
      finalize facts [.include 1 0, .seed 1] [annotation] :=
  finalize_constraint_order facts (List.Perm.swap _ _ []) [annotation]

def innerHistory : List (Observation 1 Nat) := snapshots facts (fun _ => false) [annotation]

theorem nested_binding_finishes_its_own_unit : finalize facts [] [annotation] = some innerHistory := by
  apply (finalize_exact facts [] [annotation] innerHistory).mpr
  refine ⟨fun _ => false, ?_, rfl, ?_⟩
  · simp [Horn.IsLeastModel, Horn.Models, Horn.Below]
  · exact (checkHistory_exact _).mp (by decide)

theorem outer_effect_does_not_recheck_finished_inner :
    checkHistory innerHistory = true ∧ check facts [.seed 0] [annotation] = false := by decide

end Examples
end Yulang.AnnotationFinalization
