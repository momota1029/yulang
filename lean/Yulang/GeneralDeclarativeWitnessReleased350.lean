import Yulang.GeneralDeclarativeWitnessUnfinished350
import Yulang.GeneralDeclarativeWitnessAllocation350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReleased350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessOrigins350 (Table Attached visible visible_iff support)
open GeneralDeclarativeWitnessManifest349 (Code Link peel peel_exact terminal)
open GeneralDeclarativeWitnessBound349 (tied alias_sound fits bounds_sound)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (Jobs template ready)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeEndpointOverlay336 (footprintKeep spans receipts)
open GeneralDeclarativeWitnessProjection349 (unpack unpack_exact)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeOrderedRecord326 (order)
open CommonRoleCanonicalRows (Row normalize)

def link {s : State} {t : Table} (a : Attached s t) (x y : Nat) :
    Link → Option {_u : Unit // Alias (restriction (support a)) x y}
  | .same =>
    if same : x = y then some ⟨(),same ▸ alias_refl x⟩ else none
  | .order proof =>
    if proven : tied s x y proof = true then
      some ⟨(),.bounds (GeneralDeclarativeWitnessBound349.sound (s := s) (splitAnd proven).1)
        (GeneralDeclarativeWitnessBound349.sound (s := s) (splitAnd proven).2)⟩
    else none

theorem usable {s : State} {t : Table} (a : Attached s t) {i : Nat} {e : Equation}
    (found : (visible t)[i]? = some e) : e ∈ (restriction (support a)).equations :=
  (visible_iff a e).mpr (List.mem_iff_getElem?.mpr ⟨i,found⟩)

structure Decoded {s : State} {t : Table} (a : Attached s t) (root : Nat) where
  fields : Row Expr
  ending : Expr
  spine : Spine (restriction (support a)) root fields ending

/-- Reuses the syntax checker, but its proof is against the original
producer/release view, not an invented source row. The witness can
index only the already visible table, not mark a producer released. -/
def replay {s : State} {t : Table} (a : Attached s t) (root : Nat) :
    Code → Option (Decoded a root)
  | .inline i owner => do
    match found : (visible t)[i]? with
    | none => none
    | some r =>
      let own ← link a root r.left owner
      let done ← terminal (peel r.right).2
      let seen : (⟨r.left,withTail (peel r.right).1 (peel r.right).2⟩ : Equation) ∈
          (restriction (support a)).equations := by rw [peel_exact]; exact usable a found
      pure ⟨(peel r.right).1,(peel r.right).2,.inline own.property done.property seen⟩
  | .prefix i owner next => do
    match found : (visible t)[i]? with
    | none => none
    | some r =>
      let own ← link a root r.left owner
      match tail : (peel r.right).2 with
      | .variable rest =>
        let later ← replay a rest next
        let seen : (⟨r.left,withTail (peel r.right).1 (.variable rest)⟩ : Equation) ∈
            (restriction (support a)).equations := by
          rw [← tail,peel_exact]
          exact usable a found
        pure ⟨(peel r.right).1 ++ later.fields,later.ending,.prefixed own.property seen later.spine⟩
      | _ => none
termination_by code => sizeOf code

structure Checked {s : State} {t : Table} (a : Attached s t) (arg : Capture) (pat : Pattern) where
  fields : List (Nat × Nat)
  tail : Nat
  low : Decoded a arg.lower
  high : Decoded a arg.upper
  lo : Row Expr
  hi : Row Expr
  pattern : normalize pat = template fields tail
  actual : Read (support a) arg (fields.map Prod.fst) low.fields high.fields lo hi low.ending high.ending
  jobs : Jobs
  computed : ready arg fields tail low.fields high.fields lo hi low.ending high.ending = some jobs

def project {s : State} {t : Table} (a : Attached s t) (arg : Capture) (pat : Pattern)
    (w : GeneralDeclarativeWitnessRecord349.Wire) : Option (Checked a arg pat) :=
  match found : unpack (normalize pat) with
  | some (head::tail,last) =>
    let fields := head :: tail
    if bounded : fits s arg w.bounds = true then
      if unique : (fields.map Prod.fst).Nodup then do
        let lo ← replay a arg.lower w.lower
        let hi ← replay a arg.upper w.upper
        match lr : order (normalize lo.fields) (fields.map Prod.fst),
          hr : order (normalize hi.fields) (fields.map Prod.fst) with
        | some lower,some upper =>
          match made : ready arg fields last lo.fields hi.fields lower upper lo.ending hi.ending with
          | some jobs => pure ⟨fields,last,lo,hi,lower,upper,unpack_exact found,
              ⟨bounds_sound bounded,unique,lo.spine,hi.spine,lr,hr⟩,jobs,made⟩
          | none => none
        | _,_ => none
      else none
    else none
  | _ => none

theorem input {s : State} {t : Table} {a : Attached s t} {arg : Capture} {pat : Pattern}
    (seen : Checked a arg pat) (keep : List Nat) :
    GeneralDeclarativeTaggedInputs340.Input (support a) c i keep s arg pat
      (prepare s (footprintKeep keep seen.jobs) seen.jobs.length)
      (spans s (footprintKeep keep seen.jobs) seen.jobs)
      (receipts s (footprintKeep keep seen.jobs) seen.jobs) :=
  .prior (.record seen.pattern seen.actual seen.computed)

end Yulang.GeneralDeclarativeWitnessReleased350
