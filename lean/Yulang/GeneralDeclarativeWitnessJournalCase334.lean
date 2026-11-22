import Yulang.GeneralDeclarativeWitnessReobserve334
import Yulang.GeneralDeclarativeWitnessFixture334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessJournalCase334
open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsResult332 (current to_final dictionary)
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl checked)
open GeneralDeclarativeNestedSiblingsModels332 (inhabited)
open GeneralDeclarativeNestedDecl332 (root normal normalizedExpr)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedFrame332 (spans fallback)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeWitnessFixture334 (waiting root_reads root_choice one_choice two_choice secondWitness)
open GeneralDeclarativeWitnessReobserve334 (ReaderGrowth Journal successful_reobserve)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeWitnessNode334 (Generation)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Tree Summarizes Classify)

abbrev noneDone : Nat → Prop := fun _ => False
abbrev oneDone : Nat → Prop := (· = 100)
abbrev allDone : Nat → Prop := fun _ => True

theorem source_parent : Extends source parent :=
  trans (actual_head noneDone).1.grows grow_parent

def rootHistorical : Supported parent noneDone := preserve (origins noneDone) source_parent
def firstHistorical : Supported firstDone oneDone := preserve (origins oneDone) (trans source_parent grow_one)

noncomputable def historicalRoot : Generation rootHistorical registry interpretation root impl childList where
  slice := ⟨source,origins noneDone,source_parent,sources_grow _ source_parent⟩
  protect := keep
  fallback := fallback
  targets := targets
  named := stage
  spans := spans
  source := .cons (.inline (view := fun _ => none) (point_bounded _ _) normal (root_reads noneDone) rfl) .nil
  ordinary := parent
  compiled := exact_order_writes.1
  receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _)

def historicalFirst : Generation firstHistorical registry interpretation first leaf [] where
  slice := ⟨parent,preserve (origins oneDone) source_parent,grow_one,sources_grow _ grow_one⟩
  protect := keep
  fallback := fallback
  targets := targets
  named := parent
  spans := spansOne
  source := .cons (.named ⟨bound_one,.variable 0,[⟨0,.actual,3⟩],rfl,.capture,
    .cons ⟨rfl,rfl,bound_one⟩ .nil⟩) .nil
  ordinary := firstDone
  compiled := exact_order_writes.2.1
  receipt := literal (GeneralDeclarativeClauseBatch327.reflexive _)

theorem rootLater : ReaderGrowth rootHistorical (current allDone) :=
  ⟨trans grow_one grow_two,fun _ _ yes => yes,fun _ _ => True.intro⟩

theorem firstLater : ReaderGrowth firstHistorical (current allDone) :=
  ⟨grow_two,fun _ _ yes => yes,fun _ _ => True.intro⟩

theorem lastLater : ReaderGrowth (current allDone) (current allDone) :=
  ⟨GeneralDeclarativeClauseBatch327.reflexive _,fun _ _ yes => yes,fun _ yes => yes⟩

abbrev exactTree : Tree := .selected impl.id [.selected leaf.id [],.selected leaf.id []]

theorem ordinary_phases_differ : parent.equations ≠ firstDone.equations ∧ firstDone.equations ≠ final.equations := by
  constructor <;> intro eq <;> have h := congrArg List.length eq <;> cases h

theorem chronological :
    Journal (current allDone) registry interpretation waiting root exactTree :=
  .node rootLater historicalRoot (root_choice _)
    (.cons (.node firstLater historicalFirst (one_choice _) .nil)
      (.cons (.node lastLater (secondWitness allDone).toGeneration (two_choice _) .nil) .nil))

theorem recovered :
    Classify (Rule (current allDone) registry interpretation waiting) root (.selected dictionary) ∧
      ∀ m, Models final m → Evidence registry interpretation m root dictionary := by
  apply successful_reobserve checked covered wanted_root chronological
  exact .selected (.cons (.selected .nil (.selected rfl)) (.cons (.selected .nil (.selected rfl)) .nil))
      (.selected rfl)

theorem inhabited_recovery :
    ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨m,fit,recovered.2 m fit⟩

end Yulang.GeneralDeclarativeWitnessJournalCase334
