import Yulang.GeneralNominalCatalogueExtension305
import Yulang.GeneralDictionaryGroundCopy218Source

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalReportBranchFixture305
open GeneralDictionaryGroundCopy218Source (snapshot context)
open GeneralNominalCatalogueExtension305 (extend equivalent)
open GeneralNominalReportContext305 (EquivalentContexts)
open GeneralNominalRecursiveInspection (Origin Report inspect)
open GeneralNominalReportSourceTransport (moveBounds moveReport)
open GeneralNominalInspection (Query)

theorem unused : ∀ i, snapshot.view.shapes i ≠ .pair := by
  intro _ eq
  cases eq

def expanded : GeneralNominalCandidates.Context :=
  ⟨extend snapshot .pair (by trivial) unused,context.interpretation⟩

def coordinates : EquivalentContexts context expanded := equivalent context .pair (by trivial) unused

def branch : Query := .nominal 5 [.node (.variant 0) [.variables [7,7]],.scalar .int]

def first := inspect snapshot branch (6,6) (some (.source 6))
def second := inspect expanded.state branch (moveBounds coordinates.geometry.slot (6,6)) (some (.source 6))

theorem exact : second = moveReport coordinates.geometry.slot first :=
  GeneralNominalReportRecompute305.inspect_exact coordinates.geometry branch (6,6) (some (.source 6))

def origins : Origin := .structural (.nominal (.source 6) 5 0) (.variant 0) 0

def summary {s : GeneralNominalState.State} (r : Report s) :
    List (Nat × Nat × Nat × Option Origin) × List (Nat × Nat) × List Origin :=
  (r.captures.map fun c => (c.name,c.bounds.1.val,c.bounds.2.val,c.origin),
    r.conflicts.map fun p => (p.1.val,p.2.val),r.tests.map Prod.fst)

def expected : List (Nat × Nat × Nat × Option Origin) × List (Nat × Nat) × List Origin :=
  ([(7,0,1,some origins),(7,0,1,some origins)],[(2,3)],
    [.source 6,.nominal (.source 6) 5 0,.nominal (.source 6) 5 1])

theorem both_branch_outputs : summary first = expected ∧ summary second = expected := by
  constructor
  · decide +kernel
  · rw [exact]
    decide +kernel

end Yulang.GeneralNominalReportBranchFixture305
