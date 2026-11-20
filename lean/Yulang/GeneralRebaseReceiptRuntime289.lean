import Yulang.GeneralRebaseReceiptPublic289

/-! Executable controls use the exact normalized wires of the two real
raw endpoints. The Lean equality to actual extraction is separate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptRuntime289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptWire289
open GeneralRebaseReceiptMachine289 (Phase Stop run tick)
open GeneralRebaseReceiptCompile289 (Mark observe actualMark concrete_compile)
open GeneralRebaseReceiptFixture289 (wire request expectedWire wire_exact expected_decision)
open GeneralRebaseReceiptScopedTrace289 (finalPhase)
open GeneralRebaseReceiptControls289 (wrongTarget detached effectiveChild)

def runNormalized (choice : Bool) : Phase := run (expectedWire choice) (request choice)

def decisionLabel : Decision → String
  | .wrongWorld => "wrong-registry"
  | .missingProducer => "no-producer"
  | .detached => "not-generated"
  | .notUnique => "not-unique"
  | .nonInert => "has-effects"
  | .unobserved => "missing-head"
  | .unfinished => "inspection-pending"
  | .ready => "ready"

def labels : Phase → String
  | .scan => "scan"
  | .received _ => "receipt"
  | .published _ => "published"
  | .stopped .stale => "stale-stamp"
  | .stopped (.denied d) => decisionLabel d

def outputLabels : List String :=
  [labels (runNormalized true),labels (runNormalized false),
    labels (run (expectedWire true) wrongTarget),
    labels (run detached (request true)),
    labels (run effectiveChild (request true)),
    (tick (expectedWire false) (request false) (.received (request true))).map labels |>.getD "none",
    (tick (expectedWire false) (request true) (.received (request true))).map labels |>.getD "none"]

theorem normalized_endpoint (choice : Bool) : runNormalized choice = run (wire choice (after choice)) (request choice) := by
  rw [wire_exact]
  rfl

theorem exact_runtime (choice : Bool) : runNormalized choice = finalPhase choice := by
  unfold runNormalized
  cases choice with
  | false =>
    have result := expected_decision false
    have deny : check (expectedWire false) (request false) ≠ .ready := by rw [result]; decide
    rw [GeneralRebaseReceiptMachine289.run_denial _ _ deny,result]
    rfl
  | true =>
    rw [GeneralRebaseReceiptMachine289.run_ready _ _ (expected_decision true)]
    rfl

theorem stale_normalized :
    tick (expectedWire false) (request false) (.received (request true)) = some (.stopped .stale) := by
  apply GeneralRebaseReceiptMachine289.stale_stops
  intro same
  exact GeneralRebaseReceiptControls289.world_disagrees (congrArg Offer.world same).symm

theorem keep_stamp_recheck :
    tick (expectedWire false) (request true) (.received (request true)) = some (.stopped (.denied .wrongWorld)) := by
  have wrong : check (expectedWire false) (request true) = .wrongWorld := by
    have h := GeneralRebaseReceiptControls289.stale_offer_rejected
    change check (wire false (after false)) (request true) = .wrongWorld at h
    rwa [wire_exact] at h
  simp [tick,wrong]

theorem exact_mark_output (choice : Bool) :
    observe root (runNormalized choice) = if choice then some actualMark else none := by
  cases choice
  · rw [exact_runtime]
    rfl
  · rw [exact_runtime]
    exact concrete_compile true

end Yulang.GeneralRebaseReceiptRuntime289
