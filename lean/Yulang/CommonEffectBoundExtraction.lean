import Yulang.CommonEffectConstructorNormalisation
import Yulang.CommonEffectScopedBounds
import Yulang.CommonEffectRowQuantifiers

/-! Computed flat-bound extraction below pure local type existentials.
Captured endpoints are inspected recursively. Local row references are
projected to empty only because existsTypes supplies pure types. Unsupported
constructor occurrences and binders remain syntax; they are never rejected
as unsatisfiable or shifted to scheme-parameter conditions. -/
namespace Yulang.CommonEffectBoundExtraction
open Common (Ty)
open Core.PresenceGeneration (TyTerm CompTerm)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula (Formula)
open LayerBoundTemplates (Constraint Problem)
open CommonBoundCoalescing (Models)

variable {scopes count : Nat}

def rigid : TyTerm (α ⊕ Fin count) → Bool
  | .var (.inl _) => true
  | .var (.inr _) => false
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => true
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => rigid first && rigid last
  | .required _ body | .variant _ body => rigid body
  | .arrow arg _ result _ => rigid arg && rigid result

theorem rigid_value_irrelevant (term : TyTerm (α ⊕ Fin count)) (assignment : α → Computation)
    (first last : Fin count → Ty) (good : rigid term = true) :
    term.eval Common.model (localEnv assignment first) = term.eval Common.model (localEnv assignment last) := by
  induction term
  case var name =>
    cases name with
    | inl name => rfl
    | inr name => cases good
  case arrow arg incoming result outgoing iha ihr =>
    have incomingSame := CommonEffectRowQuantifiers.rowTerm_congr incoming (localEnv assignment first)
      (localEnv assignment last) (fun name => by cases name <;> rfl)
    have outgoingSame := CommonEffectRowQuantifiers.rowTerm_congr outgoing (localEnv assignment first)
      (localEnv assignment last) (fun name => by cases name <;> rfl)
    have both := Bool.and_eq_true_iff.mp good
    simp only [TyTerm.eval, iha both.1, ihr both.2, incomingSame, outgoingSame]
  all_goals simp_all only [rigid, Bool.and_eq_true, TyTerm.eval]

def project (term : TyTerm (α ⊕ Fin count)) : TyTerm α :=
  term.subst CommonEffectRowQuantifiers.project

theorem project_exact (term : TyTerm (α ⊕ Fin count)) (assignment : α → Computation)
    (types : Fin count → Ty) (good : rigid term = true) :
    (project term).eval Common.model assignment = term.eval Common.model (localEnv assignment types) := by
  rw [project, TyTerm.eval_subst, CommonEffectRowQuantifiers.project_eval]
  exact rigid_value_irrelevant term assignment (fun _ => .top) types good

def flexName : TyTerm (α ⊕ Fin count) → Option (Fin count)
  | .var (.inr index) => some index
  | _ => none

theorem flexName_exact (term : TyTerm (α ⊕ Fin count)) (index : Fin count)
    (found : flexName term = some index) : term = .var (.inr index) := by
  cases term <;> simp only [flexName, reduceCtorEq] at found
  case var name =>
    cases name <;> simp_all only [Option.some.injEq, reduceCtorEq]

def inspectType (source target : TyTerm (α ⊕ Fin count)) : Option (Constraint count (TyTerm α)) :=
  match flexName source, flexName target with
  | some first, some last => some (.flow first last)
  | some first, none => if rigid target then some (.upper first (project target)) else none
  | none, some last => if rigid source then some (.lower (project source) last) else none
  | none, none => if rigid source && rigid target then some (.check (project source) (project target)) else none

theorem inspectType_exact (source target : TyTerm (α ⊕ Fin count)) (constraint : Constraint count (TyTerm α))
    (found : inspectType source target = some constraint) (assignment : α → Computation) (types : Fin count → Ty) :
    CommonBoundCoalescing.Holds (fun term => term.eval Common.model assignment) types constraint ↔
      Common.Subtype (source.eval Common.model (localEnv assignment types)) (target.eval Common.model (localEnv assignment types)) := by
  unfold inspectType at found
  cases hs : flexName source <;> cases ht : flexName target <;> simp only [hs, ht] at found
  case some.some firstIndex lastIndex =>
    obtain rfl := Option.some.inj found
    rw [flexName_exact source firstIndex hs, flexName_exact target lastIndex ht]
    rfl
  case some.none firstIndex =>
    split at found
    next good =>
      obtain rfl := Option.some.inj found
      rw [flexName_exact source firstIndex hs]
      simp only [CommonBoundCoalescing.Holds, project_exact target assignment types good, TyTerm.eval, localEnv]
      rfl
    next => contradiction
  case none.some lastIndex =>
    split at found
    next good =>
      obtain rfl := Option.some.inj found
      rw [flexName_exact target lastIndex ht]
      simp only [CommonBoundCoalescing.Holds, project_exact source assignment types good, TyTerm.eval, localEnv]
      rfl
    next => contradiction
  case none.none =>
    split at found
    next good =>
      obtain rfl := Option.some.inj found
      have both := Bool.and_eq_true_iff.mp good
      simp only [CommonBoundCoalescing.Holds, project_exact source assignment types both.1,
        project_exact target assignment types both.2]
    next => contradiction

structure Summary (scopes count : Nat) (α : Type) where
  bounds : Problem count (TyTerm α)
  side : Formula scopes α

def Summary.Holds (summary : Summary scopes count α) (assignment : α → Computation) (types : Fin count → Ty) : Prop :=
  Models (fun term => term.eval Common.model assignment) summary.bounds types ∧ summary.side.Holds assignment

def Accepts (summaries : List (Summary scopes count α)) (assignment : α → Computation) (types : Fin count → Ty) : Prop :=
  ∃ summary ∈ summaries, summary.Holds assignment types

def merge (first last : Summary scopes count α) : Summary scopes count α :=
  ⟨first.bounds ++ last.bounds, .and first.side last.side⟩

theorem merge_exact (first last : Summary scopes count α) (assignment : α → Computation) (types : Fin count → Ty) :
    (merge first last).Holds assignment types ↔ first.Holds assignment types ∧ last.Holds assignment types := by
  simp only [merge, Summary.Holds, Models, List.mem_append, or_imp, forall_and, Formula.Holds]
  exact and_and_and_comm

def product (first last : List (Summary scopes count α)) : List (Summary scopes count α) :=
  first.flatMap fun a => last.map fun b => merge a b

theorem product_exact (first last : List (Summary scopes count α)) (assignment : α → Computation) (types : Fin count → Ty) :
    Accepts (product first last) assignment types ↔ Accepts first assignment types ∧ Accepts last assignment types := by
  constructor
  · rintro ⟨summary, member, accepted⟩
    obtain ⟨a, aMember, fromA⟩ := List.mem_flatMap.mp member
    obtain ⟨b, bMember, rfl⟩ := List.mem_map.mp fromA
    have both := (merge_exact a b assignment types).mp accepted
    exact ⟨⟨a, aMember, both.1⟩, ⟨b, bMember, both.2⟩⟩
  · rintro ⟨⟨a, aMember, firstHolds⟩, ⟨b, bMember, lastHolds⟩⟩
    exact ⟨merge a b, List.mem_flatMap.mpr ⟨a, aMember, List.mem_map.mpr ⟨b, bMember, rfl⟩⟩,
      (merge_exact a b assignment types).mpr ⟨firstHolds, lastHolds⟩⟩

theorem append_exact (first last : List (Summary scopes count α)) (assignment : α → Computation) (types : Fin count → Ty) :
    Accepts (first ++ last) assignment types ↔ Accepts first assignment types ∨ Accepts last assignment types := by
  simp only [Accepts, List.mem_append, or_and_right, exists_or]

def pureSide (formula : Formula scopes (α ⊕ Fin count)) : Summary scopes count α :=
  ⟨[], formula.subst CommonEffectRowQuantifiers.project⟩

theorem pureSide_exact (formula : Formula scopes (α ⊕ Fin count)) (only : CommonEffectRowQuantifiers.rowOnly formula = true)
    (assignment : α → Computation) (types : Fin count → Ty) :
    (pureSide formula).Holds assignment types ↔ formula.Holds (localEnv assignment types) := by
  simp only [pureSide, Summary.Holds, Formula.holds_subst, CommonEffectRowQuantifiers.project_eval]
  have emptyModels : Models (fun term : TyTerm α => term.eval Common.model assignment) [] types := by
    intro constraint member; cases member
  exact (and_iff_right emptyModels).trans
    (CommonEffectRowQuantifiers.type_assignment_irrelevant formula only assignment types).symm

def inspectCore : Core.PresenceGeneration.Formula (α ⊕ Fin count) → Option (List (Summary scopes count α))
  | .top => some [⟨[], .core .top⟩]
  | .bot => some []
  | .tyLe source target => (inspectType source target).map fun constraint => [⟨[constraint], .core .top⟩]
  | .rowLe source target => some [pureSide (.core (.rowLe source target))]
  | .and first last => do
      let a ← inspectCore first
      let b ← inspectCore last
      pure (product a b)
  | .or first last => do
      let a ← inspectCore first
      let b ← inspectCore last
      pure (a ++ b)
  | .existsSlot _ => none

theorem inspectCore_exact (formula : Core.PresenceGeneration.Formula (α ⊕ Fin count))
    (summaries : List (Summary scopes count α)) (found : inspectCore formula = some summaries)
    (assignment : α → Computation) (types : Fin count → Ty) :
    Accepts summaries assignment types ↔ formula.Holds Common.model (localEnv assignment types) := by
  cases formula with
  | top =>
    simp only [inspectCore, Option.some.injEq] at found
    subst summaries
    simp [Accepts, Summary.Holds, Models, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
  | bot =>
    simp only [inspectCore, Option.some.injEq] at found
    subst summaries
    simp [Accepts, Core.PresenceGeneration.Formula.Holds]
  | tyLe source target =>
    simp only [inspectCore, Option.map_eq_some_iff] at found
    obtain ⟨constraint, constraintFound, rfl⟩ := found
    change Accepts _ _ _ ↔ Common.Subtype _ _
    simpa only [Accepts, List.mem_singleton, exists_eq_left, Summary.Holds, Models,
      List.mem_singleton, forall_eq, Formula.Holds, Core.PresenceGeneration.Formula.Holds, and_true] using
      inspectType_exact source target constraint constraintFound assignment types
  | rowLe source target =>
    simp only [inspectCore, Option.some.injEq] at found
    subst summaries
    simpa only [Accepts, List.mem_singleton, exists_eq_left, Formula.Holds] using
      pureSide_exact (.core (.rowLe source target)) rfl assignment types
  | and first last =>
    cases aFound : inspectCore (scopes := scopes) first with
    | none => simp [inspectCore, aFound] at found
    | some a =>
      cases bFound : inspectCore (scopes := scopes) last with
      | none => simp [inspectCore, aFound, bFound] at found
      | some b =>
        simp [inspectCore, aFound, bFound] at found
        subst summaries
        exact (product_exact a b assignment types).trans
          (and_congr (inspectCore_exact first a aFound assignment types) (inspectCore_exact last b bFound assignment types))
  | or first last =>
    cases aFound : inspectCore (scopes := scopes) first with
    | none => simp [inspectCore, aFound] at found
    | some a =>
      cases bFound : inspectCore (scopes := scopes) last with
      | none => simp [inspectCore, aFound, bFound] at found
      | some b =>
        simp [inspectCore, aFound, bFound] at found
        subst summaries
        exact (append_exact a b assignment types).trans
          (or_congr (inspectCore_exact first a aFound assignment types) (inspectCore_exact last b bFound assignment types))
  | existsSlot => simp [inspectCore] at found
termination_by sizeOf formula

def inspect : Formula scopes (α ⊕ Fin count) → Option (List (Summary scopes count α))
  | .core body => inspectCore body
  | .rowLe source target => some [pureSide (.rowLe source target)]
  | .and first last => do return product (← inspect first) (← inspect last)
  | .or first last => do return (← inspect first) ++ (← inspect last)
  | .existsSlot _ | .existsTypes _ _ | .forallTypes _ _ => none

theorem inspect_exact (formula : Formula scopes (α ⊕ Fin count))
    (summaries : List (Summary scopes count α)) (found : inspect formula = some summaries)
    (assignment : α → Computation) (types : Fin count → Ty) :
    Accepts summaries assignment types ↔ formula.Holds (localEnv assignment types) := by
  cases formula with
  | core body => exact inspectCore_exact body summaries (by simpa only [inspect] using found) assignment types
  | rowLe source target =>
    simp only [inspect, Option.some.injEq] at found
    subst summaries
    simpa only [Accepts, List.mem_singleton, exists_eq_left] using
      pureSide_exact (.rowLe source target) rfl assignment types
  | and first last =>
    cases aFound : inspect first with
    | none => simp [inspect, aFound] at found
    | some a =>
      cases bFound : inspect last with
      | none => simp [inspect, aFound, bFound] at found
      | some b =>
        simp [inspect, aFound, bFound] at found
        subst summaries
        exact (product_exact a b assignment types).trans
          (and_congr (inspect_exact first a aFound assignment types) (inspect_exact last b bFound assignment types))
  | or first last =>
    cases aFound : inspect first with
    | none => simp [inspect, aFound] at found
    | some a =>
      cases bFound : inspect last with
      | none => simp [inspect, aFound, bFound] at found
      | some b =>
        simp [inspect, aFound, bFound] at found
        subst summaries
        exact (append_exact a b assignment types).trans
          (or_congr (inspect_exact first a aFound assignment types) (inspect_exact last b bFound assignment types))
  | existsSlot | existsTypes | forallTypes => simp [inspect] at found
termination_by sizeOf formula

def Summary.eliminate (summary : Summary scopes count α) : Formula scopes α :=
  .and (CommonEffectScopedBounds.eliminate summary.bounds) summary.side

theorem Summary.eliminate_exact (summary : Summary scopes count α) (assignment : α → Computation) :
    summary.eliminate.Holds assignment ↔ ∃ types : Fin count → Ty, summary.Holds assignment types := by
  change ((CommonEffectScopedBounds.eliminate summary.bounds).Holds assignment ∧ summary.side.Holds assignment) ↔ _
  rw [CommonEffectScopedBounds.eliminate_consistent]
  exact (and_congr (CommonBoundCoalescing.consistent_iff_satisfiable
    (fun term : TyTerm α => term.eval Common.model assignment) summary.bounds) Iff.rfl).trans exists_and_right.symm

def disjoin : List (Summary scopes count α) → Formula scopes α
  | [] => .core .bot
  | summary :: rest => .or summary.eliminate (disjoin rest)

theorem disjoin_exact (summaries : List (Summary scopes count α)) (assignment : α → Computation) :
    (disjoin summaries).Holds assignment ↔ ∃ types : Fin count → Ty, Accepts summaries assignment types := by
  induction summaries with
  | nil => simp [disjoin, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Accepts]
  | cons summary rest ih =>
    simp only [disjoin, Formula.Holds, Summary.eliminate_exact, ih, Accepts, List.mem_cons, exists_eq_or_imp, exists_or]

def eraseExists (count : Nat) (body : Formula scopes (α ⊕ Fin count)) : Formula scopes α :=
  match inspect body with
  | none => .existsTypes count body
  | some summaries => disjoin summaries

theorem eraseExists_exact (body : Formula scopes (α ⊕ Fin count)) (assignment : α → Computation) :
    (eraseExists count body).Holds assignment ↔ (Formula.existsTypes count body).Holds assignment := by
  cases found : inspect body with
  | none => simp only [eraseExists, found]
  | some summaries =>
    simp only [eraseExists, found, disjoin_exact, Formula.Holds]
    exact exists_congr (fun types => inspect_exact body summaries found assignment types)

def eliminate : Formula scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe source target => .rowLe source target
  | .and first last => .and (eliminate first) (eliminate last)
  | .or first last => .or (eliminate first) (eliminate last)
  | .existsSlot body => .existsSlot (eliminate body)
  | .existsTypes count body => eraseExists count (eliminate body)
  | .forallTypes count body => .forallTypes count (eliminate body)

theorem eliminate_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (eliminate formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => rfl
  | and first last iha ihb => exact and_congr (iha assignment) (ihb assignment)
  | or first last iha ihb => exact or_congr (iha assignment) (ihb assignment)
  | existsSlot body ih => exact exists_congr (fun value => ih _)
  | existsTypes count body ih =>
    exact (eraseExists_exact (eliminate body) assignment).trans (exists_congr (fun types => ih _))
  | forallTypes count body ih => exact forall_congr' (fun types => ih _)

end Yulang.CommonEffectBoundExtraction
