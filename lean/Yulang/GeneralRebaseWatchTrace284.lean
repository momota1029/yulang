import Yulang.GeneralRebaseWatchJoint284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchTrace284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseFutureWatch284 (Closed Covers)
open GeneralRebaseActualWatch284 (Cache bump)
open GeneralRebaseWatchStep284 (NoReveal next advance)
open GeneralRebaseHistoryOrder282 (history)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralRebaseProspectiveDelta283 (coherent_history)

structure Frame (roles : Roles.RoleDecls) where
  raw : State roles
  watch : List Nat

inductive Certified (registry : Registry) (root : Occurrence roles) : Frame roles → Frame roles → Type
  | administrative {a b} : Actual registry root a.raw b.raw → a.raw.plans = b.raw.plans →
      Closed b.watch (history b.raw) → NoReveal a.watch b.watch (history a.raw) →
      Certified registry root a b
  | installing {a} (e : Effect roles) (new : List Nat) :
      Actual registry root a.raw (install a.raw e) → e.snapshot = a.raw.core →
      Closed new (history (install a.raw e)) → NoReveal a.watch new (history a.raw) →
      Certified registry root a ⟨install a.raw e,new⟩

def update (move : Certified r root a b) (defs : List (Entry Nat)) : List (Entry Nat) :=
  match move with
  | .administrative .. => next b.watch defs []
  | .installing e watch .. => bump watch defs e

theorem frame_same {a b : Frame roles} (same : a.raw.plans = b.raw.plans) :
    history a.raw = history b.raw := by
  unfold history GeneralNominalVersionedMixedSeedLedger237.entries
  rw [same]

theorem raw_step {a b : Frame roles} (move : Certified r root a b) : Actual r root a.raw b.raw := by
  cases move with
  | administrative step => exact step
  | installing _ _ step => exact step

theorem valid_step {a b : Frame roles} (move : Certified r root a b)
    (seen : Reachable r root a.raw) (valid : Cache a.raw a.watch defs) :
    Cache b.raw b.watch (update move defs) := by
  cases move with
  | administrative action same closed noReveal =>
    have after := reachable_step seen action
    obtain ⟨covers,sorted⟩ := advance valid.covers valid.sorted (delta := [])
      (fun row => by rw [frame_same same]; simp)
      (coherent_history _ (GeneralNominalVersionedMixedSeedLedger237.reachable after)) closed noReveal
    exact ⟨covers,sorted⟩
  | installing e watch action snap closed noReveal =>
    exact GeneralRebaseActualWatch284.install_valid valid
      (GeneralNominalVersionedMixedSeedLedger237.reachable seen) snap closed noReveal

theorem bounded_step {a b : Frame roles} (move : Certified r root a b)
    (seen : Reachable r root a.raw) (valid : Cache a.raw a.watch defs) :
    (update move defs).length ≤ b.watch.length := by
  cases move with
  | administrative action same closed noReveal =>
    exact GeneralRebaseWatchStep284.length_limit
      (valid_step (.administrative action same closed noReveal) seen valid).sorted
  | installing e watch action snap closed noReveal =>
    exact GeneralRebaseWatchStep284.length_limit
      (valid_step (.installing e watch action snap closed noReveal) seen valid).sorted

inductive Trace (r : Registry) (root : Occurrence roles) : Frame roles → Frame roles → Type
  | nil (a : Frame roles) : Trace r root a a
  | tail : Trace r root a b → Certified r root b c → Trace r root a c

def execute (path : Trace r root a b) (defs : List (Entry Nat)) : List (Entry Nat) :=
  match path with
  | .nil _ => defs
  | .tail before move => update move (execute before defs)

theorem trace_correct {a b : Frame roles} (path : Trace r root a b)
    (seen : Reachable r root a.raw) (valid : Cache a.raw a.watch defs) :
    Reachable r root b.raw ∧ Cache b.raw b.watch (execute path defs) := by
  induction path with
  | nil => exact ⟨seen,valid⟩
  | tail before start ih => exact ⟨reachable_step ih.1 (raw_step start),valid_step start ih.1 ih.2⟩

theorem trace_size {a b : Frame roles} (path : Trace r root a b)
    (seen : Reachable r root a.raw) (valid : Cache a.raw a.watch defs)
    (bounded : defs.length ≤ a.watch.length) : (execute path defs).length ≤ b.watch.length := by
  cases path with
  | nil => exact bounded
  | tail before last =>
    exact bounded_step last (trace_correct before seen valid).1 (trace_correct before seen valid).2

end Yulang.GeneralRebaseWatchTrace284
