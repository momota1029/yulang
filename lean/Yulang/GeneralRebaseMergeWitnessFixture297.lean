import Yulang.GeneralRebaseRawDepthReplay297
import Yulang.GeneralRebaseNonliteralMergeFixture269
import Yulang.GeneralRebaseMergeScanFixture267

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMergeWitnessFixture297
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Site SameInputs rootSite)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseMergeQuestions297 (Pair atModel counter equal semantic_exact counter_exact equal_exact)
open GeneralRebaseFiniteWitnessTable297 (Covers)

namespace EqualCenter
open GeneralRebaseNonliteralMergeFixture269 (journal first last same_nonliteral not_literal)
open GeneralDeclarationExamples (roles)
def pair : Pair roles := (first,last)

def test (_ : Pair roles) (_ : Assignment) : Bool := false

theorem no_counter : ¬ ∃ m, counter journal pair m :=
  ((counter_exact ..).mp same_nonliteral).2

theorem coverage : Covers (counter journal) [pair] [] := by
  intro q listed witness
  cases List.mem_singleton.mp listed
  exact False.elim (no_counter witness)

theorem computed : equal [] test pair = true := rfl

theorem determined :
    equal [] test pair = true ↔ SameInputs (Models journal) first last :=
  equal_exact journal _ _ coverage test pair (List.mem_cons_self ..) (by intro _ h; cases h)

theorem same_not_literal : equal [] test pair = true ∧ GeneralRebaseMergeCenters267.same first last = false :=
  ⟨computed,not_literal⟩

end EqualCenter

namespace DifferentCenter
open GeneralDictionaryOutputDepth252 (roles root initial snapshot model initial_model F S)
open CommonNominalFullCarrier (Equivalent)

/-- Comparison control in the real initial journal; the second site is
hypothetical and not claimed registered or reachable. -/
def extra : GeneralSourceDictionaries.Occurrence roles :=
  ⟨8,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
def pair : Pair roles := (rootSite snapshot.seed root,rootSite snapshot.seed extra)
def test (_ : Pair roles) (_ : Assignment) : Bool := true

theorem not_equal : ¬ atModel pair model := by
  intro both
  have h := both (2,0) (by change (2,0) ∈ [(2,0)]; simp)
  change Equivalent F S at h
  exact GeneralRebaseDepthMinimal285.scalar_ne_foo ⟨h.2,h.1⟩

theorem loss : counter initial pair model := ⟨initial_model,not_equal⟩

theorem coverage : Covers (counter initial) [pair] [model] := by
  intro q listed _
  cases List.mem_singleton.mp listed
  exact ⟨model,List.mem_cons_self ..,loss⟩

theorem computed : equal [model] test pair = false := rfl

theorem determined :
    equal [model] test pair = true ↔ SameInputs (Models initial) pair.1 pair.2 := by
  apply equal_exact initial [pair] [model] coverage test pair (List.mem_cons_self ..)
  intro m listed
  cases List.mem_singleton.mp listed
  exact ⟨fun _ => loss,fun _ => rfl⟩

theorem missing_counter_unsound :
    equal [] test pair = true ∧ ¬ SameInputs (Models initial) pair.1 pair.2 :=
  ⟨rfl,fun same => ((counter_exact ..).mp same).2 ⟨model,loss⟩⟩

end DifferentCenter

namespace ActualStep
open GeneralNominalCenteredHeadAllocMergeSource (root registry roles)
open GeneralNominalCenteredHeadAllocMergeInstall (aSite bSite)
open GeneralRebaseMergeRegression264 (sample merged owners pool projection_changed)

def tested (_ : Pair roles) (_ : Assignment) : Bool := false


theorem listed : (aSite,bSite) ∈ GeneralRebaseMergeScan267.scan sample root
    (fun a b => equal [] tested (a,b)) := by
  apply (GeneralRebaseMergeScan267.scan_exact ..).mpr
  have r := (GeneralRebaseMergeScan267.scan_exact ..).mp GeneralRebaseMergeScanFixture267.listed
  exact ⟨r.1,Or.inr (by decide +kernel)⟩

theorem actual_preserved :
    GeneralNominalVersionedMixedKernel234.Step registry root sample merged ∧
      GeneralRebaseLiveProjection264.project owners pool merged ≠ GeneralRebaseLiveProjection264.project owners pool sample := by
  refine ⟨GeneralRebaseMergeScan267.source_step registry sample root (fun a b => equal [] tested (a,b))
    aSite bSite listed (fun _ => ⟨rfl,.nil⟩),projection_changed⟩

end ActualStep
end Yulang.GeneralRebaseMergeWitnessFixture297
