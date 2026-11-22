import Yulang.GeneralDeclarativeHead320
import Yulang.GeneralNominalState

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedShape335
open Core.PresenceGeneration (TyTerm)
open GeneralNominalState (Parameter Descriptor Fits FitsAll Denotes)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatCompilerSemantics (nominal_congr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Ty Argument Equivalent nominal)

def one (p : Parameter n) : Option (Fin n) :=
  match p with
  | .type (lo,hi) => if lo = hi then some lo else none
  | .row _ => none

def point (ps : List (Parameter n)) : Option (List (Fin n)) := ps.mapM one

theorem one_exact (p : Parameter n) (index : Fin n) :
    one p = some index ↔ p = .type (index,index) := by
  cases p with
  | row => simp [one]
  | type pair =>
    obtain ⟨lo,hi⟩ := pair
    by_cases h : lo = hi
    · subst hi
      simp [one]
    · simp [one,h]
      intro a b
      exact h (a.trans b.symm)

theorem point_front (p : Parameter n) (ps : List (Parameter n))
    (indices : List (Fin n)) (exactly : point (p::ps) = some indices) :
    ∃ first rest, p = .type (first,first) ∧ point ps = some rest ∧ indices = first::rest := by
  cases he : one p with
  | none => simp [point,List.mapM_cons,he] at exactly
  | some first =>
    cases ht : point ps with
    | none => simp [point,List.mapM_cons,he,show List.mapM one ps = none from ht] at exactly
    | some rest =>
      have eq : first::rest = indices := by
        simpa [point,List.mapM_cons,he,show List.mapM one ps = some rest from ht] using exactly
      exact ⟨first,rest,(one_exact _ _).mp he,rfl,eq.symm⟩

def assigned (base : GeneralSourceState.State) (m : Assignment) (indices : List (Fin base.slots)) : List Ty :=
  indices.map (fun s => (m (base.source s)).1)

theorem values_of_fit (base : GeneralSourceState.State) (m : Assignment)
    {ps : List (Parameter base.slots)} {indices : List (Fin base.slots)}
    (fit : FitsAll base m ps vals) (points : point ps = some indices) :
    ∃ actual : List Ty, vals = actual.map Sum.inl ∧ Aligned Equivalent actual (assigned base m indices) := by
  induction fit generalizing indices with
  | nil =>
    have empty : indices = [] := (Option.some.inj points).symm
    subst indices
    exact ⟨[],rfl,.nil⟩
  | @cons p v ps vals h _ ih =>
    obtain ⟨first,rests,kind,more,rfl⟩ := point_front p ps indices points
    subst p
    cases v with
    | inr _ => exact False.elim h
    | inl t =>
      obtain ⟨actual,rfl,aligned⟩ := ih more
      exact ⟨t::actual,rfl,.cons ⟨h.2,h.1⟩ aligned⟩

theorem chosen_points_fit (base : GeneralSourceState.State) (m : Assignment)
    {ps : List (Parameter base.slots)} {indices : List (Fin base.slots)}
    (reads : point ps = some indices) :
    FitsAll base m ps ((assigned base m indices).map Sum.inl) := by
  induction ps generalizing indices with
  | nil =>
    have empty : indices = [] := (Option.some.inj reads).symm
    subst indices
    exact .nil
  | cons p ps ih =>
    obtain ⟨first,rest,rfl,more,rfl⟩ := point_front p ps indices reads
    exact .cons (eqv_refl _) (ih more)

def descriptorExpr (base : GeneralSourceState.State) (d : Descriptor base.slots) : Option Expr :=
  (point d.arguments).map (fun ks => .nominal d.declaration.name (ks.map fun j => .variable (base.source j)))

theorem name_values (base : GeneralSourceState.State) (m : Assignment) (ks : List (Fin base.slots)) :
    values (environment m) .actual (ks.map (fun j => .variable (base.source j))) = assigned base m ks := by
  induction ks with
  | nil => rfl
  | cons _ _ ih => simp [values,value,assigned,environment] at ih ⊢; exact ih

theorem descriptor_semantics (base : GeneralSourceState.State) (slot : Fin base.slots)
    (d : Descriptor base.slots) (m : Assignment) (encoded : descriptorExpr base d = some e) :
    Denotes base m slot d ↔
      Equivalent (m (base.source slot)).1 (value (environment m) .actual e) := by
  unfold descriptorExpr at encoded
  obtain ⟨ks,points,same⟩ := Option.map_eq_some_iff.mp encoded
  subst e
  change Denotes base m slot d ↔ Equivalent (m (base.source slot)).1
    (nominal d.declaration.name ((values (environment m) .actual (ks.map fun j => .variable (base.source j))).map Sum.inl))
  rw [name_values]
  constructor
  · rintro ⟨arguments,fit,lower⟩
    obtain ⟨actual,rfl,aligned⟩ := values_of_fit base m fit points
    exact eqv_trans lower (nominal_congr _ aligned)
  · intro ok
    exact ⟨_,chosen_points_fit base m points,ok⟩

def headExpr : TyTerm n → Option Expr
  | .base b => some (.primitive (.scalar b) [])
  | _ => none

theorem head_semantics (base : GeneralSourceState.State) (m : Assignment)
    (term : TyTerm (Fin base.slots)) (encoded : headExpr term = some e) :
    term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base m) =
      value (environment m) .actual e := by
  cases term <;> simp [headExpr] at encoded
  subst e
  rfl

end Yulang.GeneralStoppedShape335
