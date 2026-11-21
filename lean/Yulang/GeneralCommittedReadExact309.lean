import Yulang.GeneralCommittedReadErasure309
import Yulang.GeneralGeneratedDictionaryHeight299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralCommittedReadExact309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralGeneratedDictionaryRun299 (Read run run_exact)
open GeneralGeneratedDictionaryHeight299 (height tall lower_bound)
open GeneralCommittedReadTrace309 (Trace)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralCommittedReadEvidence309 (CommittedRead)
open GeneralOrderedDictionaryCheck309 (validate)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
variable {m : Assignment} {read : Read} {decode : Nat → Occurrence roles}

mutual
  theorem trace_runs (d : Payload) (i fuel : Nat) (e : Trace r s root m read decode i d)
      (enough : height d ≤ fuel) : run read fuel i = some d := by
    cases e with
    | node j row ds _ seen below =>
      have h : tall ds + 1 ≤ fuel := by simpa only [height] using enough
      cases fuel with
      | zero => omega
      | succ n =>
        exact (run_exact ..).mpr
          ⟨row,ds,seen.1,trace_forest_runs ds row.children n below (by omega),rfl⟩
  termination_by sizeOf d

  theorem trace_forest_runs (ds : List Payload) (is : List Nat) (fuel : Nat)
      (forest : All₂ (Trace r s root m read decode) is ds) (enough : tall ds ≤ fuel) :
      All₂ (fun i d => run read fuel i = some d) is ds := by
    cases forest with
    | nil => exact .nil
    | @cons i d rest tail head next =>
      have size : max (height d) (tall tail) ≤ fuel := by simpa only [tall] using enough
      obtain ⟨first,others⟩ := Nat.max_le.mp size
      exact .cons (trace_runs d i fuel head first)
        (trace_forest_runs tail rest fuel next others)
  termination_by sizeOf ds
end

/-- Height is the exact amount of fuel required for this certified,
source-positioned tree, not a global saturation bound. -/
theorem certify_exact (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (reader : CommittedRead r s read decode) (valid : Models s m)
    (fuel i : Nat) (d : Payload)
    (reached : GeneralNominalSaturationState.Generated s.core.erased.current root (decode i)) :
    validate read fuel i d = .ok () ↔ height d ≤ fuel ∧ Trace r s root m read decode i d := by
  rw [GeneralOrderedDictionaryCheck309.exact]
  refine ⟨fun h => ⟨lower_bound _ _ _ _ h,?_⟩,?_⟩
  · exact GeneralCommittedReadTrace309.construct checked path read decode reader m valid fuel i d reached h
  · rintro ⟨sized,e⟩
    exact trace_runs d i fuel e sized

end Yulang.GeneralCommittedReadExact309
