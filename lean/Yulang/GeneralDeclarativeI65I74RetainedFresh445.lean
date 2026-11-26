import Yulang.GeneralDeclarativeI65I74RetainedMatch445
import Yulang.GeneralNominalCenteredHeadMatExtension

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open MixedFixed442
open Checker408 (Problem)
open GeneralNominalState (atomSources typeSources rowSources)
open GeneralNominalCenteredModelExtension (atom_same type_eval_same row_eval_same)
open GeneralNominalCenteredHeadMatExtension (names value_congr)
open GeneralDeclarativeHead320 (environment)
open GeneralDeclarativeWitnessDeclaredState357 (evaluate)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl)

def argumentNames : CommonNominalConstraints.ArgumentTerm Nat → List Nat
  | .value t => typeSources t
  | .row r => rowSources r

inductive OldModelReads (s : GeneralDeclarativeI65.State) : Nat → Prop where
  | atom (present : a ∈ s.current.ordinary.normal.ordinary)
      (read : n ∈ atomSources a) : OldModelReads s n
  | lower (present : (n,hi) ∈ s.current.ordinary.normal.intervals) : OldModelReads s n
  | upper (present : (lo,n) ∈ s.current.ordinary.normal.intervals) : OldModelReads s n
  | left (present : e ∈ s.current.ordinary.equations) : OldModelReads s e.left
  | right (present : e ∈ s.current.ordinary.equations)
      (read : n ∈ names e.right) : OldModelReads s n
  | seen (present : o ∈ s.current.visible) (arg : a ∈ o.arguments)
      (read : n ∈ argumentNames a) : OldModelReads s n

theorem fits_respects_old_model_dependencies445
    {s : GeneralDeclarativeI65.State} (m n : I72.Model)
    (agree : ∀ k, OldModelReads s k → m.assignment k = n.assignment k)
    (views : m.authoredValues = n.authoredValues) (sameSyntax : m.nativeSyntax = n.nativeSyntax)
    (fit : GeneralDeclarativeI65.Fits s m) : GeneralDeclarativeI65.Fits s n := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro a present
    exact (atom_same a (fun k h => agree k (.atom present h))).mp (fit.1.1.1.1 a present)
  · rintro ⟨lo,hi⟩ present
    have old := fit.1.1.1.2 (lo,hi) present
    simpa only [agree lo (.lower present),agree hi (.upper present)] using old
  · intro eq present
    have old := fit.1.1.2 eq present
    have rhs := value_congr eq.right (first := environment m.assignment) (last := environment n.assignment)
      (mode := .actual) (fun _ k read => congrArg Prod.fst (agree k (.right present read)))
    simpa only [agree eq.left (.left present),rhs] using old
  · intro o present
    obtain ⟨v,read,tag,key,args⟩ := fit.1.2 o present
    have original : o.arguments.map (evaluate m.assignment) =
        o.arguments.map (evaluate n.assignment) := by
      apply List.map_congr_left
      intro a seen
      cases a with
      | value t =>
        change Sum.inl (t.eval CommonNominalFullCarrier.model m.assignment) =
          Sum.inl (t.eval CommonNominalFullCarrier.model n.assignment)
        exact congrArg Sum.inl (type_eval_same t (fun k h => agree k (.seen present seen h)))
      | row r =>
        change Sum.inr (r.eval CommonNominalFullCarrier.model m.assignment) =
          Sum.inr (r.eval CommonNominalFullCarrier.model n.assignment)
        exact congrArg Sum.inr (row_eval_same r (fun k h => agree k (.seen present seen h)))
    exact ⟨v,views ▸ read,tag,key,args.trans original⟩
  · intro origin here
    exact sameSyntax ▸ fit.2 origin here

def putFixedType (m : I72.Model) (target : Nat) (v : Ty) : I72.Model :=
  { m with assignment := fun n => if n = target then (v,(m.assignment n).2) else m.assignment n }

theorem fresh_original_fits_extend_at_same_target445
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q}
    {i : Fin q.demand.outputs.length} (a : OriginalOutput (s := s) f i)
    (m : I72.Model) (fit : I72.Fits s m)
    (fresh : ¬OldModelReads s.core q.demand.outputs[i].target)
    (notValueInput : a.valueCap.center ≠ q.demand.outputs[i].target) :
    let target := q.demand.outputs[i].target
    let n := putFixedType m target (a.actualValue m)
    I72.Fits s n ∧
      (∀ k, k ≠ target → n.assignment k = m.assignment k) ∧
      (∀ k, (n.assignment k).2 = (m.assignment k).2) ∧
      n.authoredValues = m.authoredValues ∧ n.nativeSyntax = m.nativeSyntax ∧
      Equivalent (n.assignment target).1 (a.actualValue n) := by
  dsimp only
  let target := q.demand.outputs[i].target
  let n := putFixedType m target (a.actualValue m)
  have untouched (k : Nat) (ne : k ≠ target) : n.assignment k = m.assignment k := by
    simp [n,putFixedType,ne]
  have rows (k : Nat) : (n.assignment k).2 = (m.assignment k).2 := by
    by_cases h : k = target <;> simp [n,putFixedType,h]
  have no : ¬OldModelReads s.core target := fresh
  have fitN : I72.Fits s n :=
    fits_respects_old_model_dependencies445 m n
      (fun k support => (untouched k (fun h => no (h ▸ support))).symm) rfl rfl fit
  refine ⟨fitN,untouched,rows,rfl,rfl,?_⟩
  have checked : a.actualValue n = a.actualValue m := by
    unfold OriginalOutput.actualValue
    rw [rows,untouched _ notValueInput]
  have atTarget : (n.assignment target).1 = a.actualValue m := by simp [n,putFixedType]
  change Equivalent (n.assignment target).1 (a.actualValue n)
  rw [checked,atTarget]
  exact ⟨subtype_refl _,subtype_refl _⟩

/-- Conservative, executable footprint of all old model dependencies.
Structural/native provenance and model view locations are not modified
by a type assignment to one target; the semantic view ARGUMENTS are reads. -/
def oldReadNames (s : GeneralDeclarativeI65.State) : List Nat :=
  s.current.ordinary.normal.ordinary.flatMap atomSources ++
  (s.current.ordinary.normal.intervals.flatMap (fun i => [i.1,i.2]) ++
  (s.current.ordinary.equations.flatMap (fun e => e.left :: names e.right) ++
  s.current.visible.flatMap (fun v => v.arguments.flatMap argumentNames)))

theorem every_old_read_is_covered445 {s : GeneralDeclarativeI65.State} {n}
    (read : OldModelReads s n) : n ∈ oldReadNames s := by
  unfold oldReadNames
  simp only [List.mem_append,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
  cases read with
  | atom present uses => exact .inl ⟨_,present,uses⟩
  | lower present => exact .inr (.inl ⟨_,present,.inl rfl⟩)
  | upper present => exact .inr (.inl ⟨_,present,.inr rfl⟩)
  | left present => exact .inr (.inr (.inl ⟨_,present,.inl rfl⟩))
  | right present uses => exact .inr (.inr (.inl ⟨_,present,.inr uses⟩))
  | seen present term uses => exact .inr (.inr (.inr ⟨_,present,_,term,uses⟩))

def FreshOutput {p : Problem} (source : SourceSelection p) : Prop :=
  let t := p.root.demand.outputs[source.origin.i0].target
  t ∉ oldReadNames p.state.core ∧ source.own.2.out.valueCap.center ≠ t

def checkFresh {p : Problem} (source : SourceSelection p) : Bool :=
  let t := p.root.demand.outputs[source.origin.i0].target
  decide (t ∉ oldReadNames p.state.core ∧ source.own.2.out.valueCap.center ≠ t)

theorem check_fresh_exact445 {p : Problem} (source : SourceSelection p) :
    checkFresh source = true ↔ FreshOutput source := by
  simp [checkFresh,FreshOutput]

/-- Adequacy for the conservative fresh singleton lane: if the
old snapshot has any model, adding the authentic typed equation has
one. This does not decide global satisfiability of old constraints. -/
theorem matched_fresh_singleton_has_fit_if_old_fits445
    {s : FullState} {q : I72.Request} {source : SourceSelection ⟨s.base,q⟩}
    (fresh : FreshOutput source) (kept : StoredSelection s source)
    (single : s.retained = [kept.row]) (m : I72.Model) (fit : Fits s.base m) :
    ∃ n : I72.Model, FitsFull s n := by
  let r := source.origin
  let a := source.own.2.out
  have noReads : ¬OldModelReads s.base.core q.demand.outputs[r.i0].target :=
    fun read => fresh.1 (every_old_read_is_covered445 read)
  obtain ⟨newFit,_,_,_,_,same⟩ :=
    fresh_original_fits_extend_at_same_target445 a m fit noReads fresh.2
  refine ⟨_,newFit,?_⟩
  intro row found
  rw [single] at found
  cases List.mem_singleton.mp found
  exact (stored_selection_means_iff_exact_targets445 kept _).mpr
    ((original_replayed_ref_is_the_fixed_target_slice442 r a _).mpr same)

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
