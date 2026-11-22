import Yulang.GeneralDeclarativeVersionedTree342
import Yulang.GeneralDeclarativeVersionedEndpointOnly342
import Yulang.GeneralDeclarativeVersionedRootRead342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13500
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeclarativeVersionedPaired342
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereVersionCompiler317 (schema)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralWhereOriginSingleCells318 (loOld loNow hi)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralDictionaryJournalRefinement228Source (root interpretation)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarativeVersionedPhysical342 (current)
open GeneralDeclarativeVersionedChildView342 (d lower upper)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeVersionedRows342 (ordinary)
open GeneralDeclarativeVersionedTree342 (CurrentInstance modern_raw_tree actual_place)

abbrev LeafRule := GeneralDeclarativeTaggedDictionary340.Rule
  GeneralDeclarativeVersionedChildWitness342.current [] sourceRegistry interpretation waiting

/-- This joins the actual post-transaction *versioned* recursive tree
to the current child's witness-backed dictionary in one assignment
over the full old journal footprint. It is not a classifier proof for
the root, nor a theorem about the existing Rust executor. -/
structure Paired (m : Assignment) : Prop where
  exactChild : GeneralWhereVersionCompiler317.children current = [newChild.occurrence]
  placed : GeneralDeclarativeStoppedPaired341.Placement final.mixed
    GeneralDeclarativeVersionedChildBody342.expanded newChild.occurrence d
  classified : Classify LeafRule d (.selected (.node leaf.id []))
  exactRows : (schema current).equations.map (ordinary current) = [ownerOutput,lower,upper]
  incompatibleHistory : ¬ Equivalent (m loOld).1 (m loNow).1
  common : ∃ n, Models final n ∧ (∀ k ∈ journalSources final, n k = m k) ∧
    GeneralSourceDictionaries.ErasedEvidence (CurrentInstance n) root (.node declaration.id [.node leaf.id []]) ∧
    GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n d (.node leaf.id []) ∧
    (∀ row ∈ [ownerOutput,lower,upper], GeneralDeclarativeEntailment320.Holds n row) ∧
    GeneralDeclarativeEntailment320.Holds n GeneralDeclarativeVersionedRootRead342.publicRow

theorem same_assignment (m : Assignment) (fit : Models final m) : Paired m := by
  obtain ⟨_,_,currentChild,n,finalFit,stays,_,seen⟩ := GeneralDeclarativeVersionedChildWitness342.actual m fit
  refine ⟨GeneralDeclarativeVersionedPhysical342.actual_children,actual_place,currentChild,
    GeneralDeclarativeVersionedReceipt342.current_order,GeneralDeclarativeVersionedSeparation342.not_current_lower m fit,
    n,finalFit,stays,modern_raw_tree n finalFit,seen,?_,GeneralDeclarativeVersionedRootRead342.raw_root n finalFit⟩
  exact (GeneralDeclarativeVersionedReceipt342.current_literals n finalFit).2.1

end Yulang.GeneralDeclarativeVersionedPaired342
