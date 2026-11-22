import Yulang.GeneralDeclarativeWitnessReceipt349
import Yulang.GeneralDeclarativeExactDeleteAuth337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessManifest349
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessBound349 (Shared tied alias_sound)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open CommonRoleCanonicalRows (Row)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- The row manifest comes from the caller's fixed source projection,
not the solver witness. This checker verifies literal current membership;
it does not authenticate an arbitrary representation of a source file. -/
structure Manifest where
  sourceRows : List Equation

structure Attached (s : State) (manifest : Manifest) : Type where
  subset : manifest.sourceRows ⊆ s.equations

def attach (s : State) (p : Manifest) : Option (Attached s p) :=
  if h : p.sourceRows.all (fun e => decide (e ∈ s.equations)) = true
    then some ⟨fun e member => of_decide_eq_true (List.all_eq_true.mp h e member)⟩
    else none

def support {s : State} {p : Manifest} (a : Attached s p) : Supported s (fun _ => False) :=
  ⟨fun row origin => row ∈ p.sourceRows ∧ origin = .source,
    fun h => a.subset h.1⟩

theorem authored {s : State} {p : Manifest} (a : Attached s p) {i : Nat} {e : Equation}
    (found : p.sourceRows[i]? = some e) :
    e ∈ (restriction (support a)).equations :=
  from_source _ ⟨List.mem_iff_getElem?.mpr ⟨i,found⟩,rfl⟩

theorem cannot_promote {s : State} {p : Manifest} (a : Attached s p) {e : Equation}
    (notSource : e ∉ p.sourceRows) :
    e ∉ (restriction (support a)).equations := by
  intro invented
  obtain ⟨_,origin,_⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp invented
  exact notSource origin.1

/-- An alias proof used by an input read must either be literal same-name
or be justified by mutual bounds. Arbitrary ordinary row equalities are
not imported into the source-restricted state. -/
inductive Link where
  | same
  | order (paths : Shared)

def link {s : State} {p : Manifest} (a : Attached s p) (x y : Nat) :
    Link → Option {_n : Unit // Alias (restriction (support a)) x y}
  | .same =>
    if h : x = y then some ⟨(),h ▸ alias_refl x⟩ else none
  | .order w =>
    if h : tied s x y w = true then
      some ⟨(),.bounds (GeneralDeclarativeWitnessBound349.sound (s := s) (splitAnd h).1)
        (GeneralDeclarativeWitnessBound349.sound (s := s) (splitAnd h).2)⟩
    else none

def peel : Expr → Row Expr × Expr
  | .record label payload tail =>
    let (rows,last) := peel tail
    ((label,payload)::rows,last)
  | other => ([],other)

theorem peel_exact (e : Expr) : withTail (peel e).1 (peel e).2 = e := by
  cases e with
  | record k lo hi =>
    have recur := peel_exact hi
    change Expr.record k lo (withTail (peel hi).1 (peel hi).2) = _
    rw [recur]
  | «variable» _ | primitive _ _ | nominal _ _ | variant _ _ | join _ _ => rfl
termination_by sizeOf e

def terminal : (e : Expr) → Option {_n : Unit // Terminal e}
  | .primitive .emptyRecord [] => some ⟨(),.width⟩
  | .primitive .exactEmpty [] => some ⟨(),.exactEnd⟩
  | _ => none

inductive Code where
  | inline (rowIndex : Nat) (owner : Link)
  | prefix (rowIndex : Nat) (owner : Link) (next : Code)

structure Decoded {s : State} {p : Manifest} (a : Attached s p) (root : Nat) where
  fields : Row Expr
  ending : Expr
  spine : Spine (restriction (support a)) root fields ending

/-- Finite readback follows only literal authored rows. For a named
tail, it restarts the authorized lookup at that exact tail name. -/
def replay {s : State} {p : Manifest} (a : Attached s p) (root : Nat) :
    Code → Option (Decoded a root)
  | .inline i owner => do
    match found : p.sourceRows[i]? with
    | none => none
    | some r =>
      let own ← link a root r.left owner
      let done ← terminal (peel r.right).2
      let seen : (⟨r.left,withTail (peel r.right).1 (peel r.right).2⟩ : Equation) ∈
          (restriction (support a)).equations := by rw [peel_exact]; exact authored a found
      pure ⟨(peel r.right).1,(peel r.right).2,.inline own.property done.property seen⟩
  | .prefix i owner next => do
    match found : p.sourceRows[i]? with
    | none => none
    | some r =>
      let own ← link a root r.left owner
      match tail : (peel r.right).2 with
      | .variable rest =>
        let later ← replay a rest next
        let seen : (⟨r.left,withTail (peel r.right).1 (.variable rest)⟩ : Equation) ∈
            (restriction (support a)).equations := by
          rw [← tail,peel_exact]
          exact authored a found
        pure ⟨(peel r.right).1 ++ later.fields,later.ending,.prefixed own.property seen later.spine⟩
      | _ => none
termination_by code => sizeOf code

end Yulang.GeneralDeclarativeWitnessManifest349
