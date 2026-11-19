import Yulang.FiniteBehaviorDriver269
import Yulang.GeneralRebaseKeyedWeakScheduler268

namespace Yulang.GeneralRebaseBehavior269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseWeakProgress268 (Weak Lull Counted lull_same weak_source)
open GeneralNominalVersionedMixedKernel234 (Step)
open FiniteRankBehavior269 (Code catalogue)
open FiniteBehaviorClassifier269 (classify)
open FiniteBehaviorDriver269 (Trace Advances reflect_trace simulate_trace)
open GeneralRebaseStep258 (Fact state_ext)
open GeneralRebaseFiniteSlices268 (slices exact_slices)

def sourceBasis (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 FiniteBehaviorClassifier269.Basis (State roles) (List Fact) where
 observe := fun source => (project owners pool source).remaining
 move := Weak registry root owners pool
 rank := fun source => (project owners pool source).remaining.length
 labels := slices (Basis owners pool)
 supported := fun source => (exact_slices ..).mpr (project owners pool source).canonical
 decreases := fun _ _ step => GeneralRebaseWeakProgress268.decrease step

noncomputable def code (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) : Code (List Fact) := classify (sourceBasis registry root owners pool) source

def codebook (owners : List Nat) (pool : List Output) : List (Code (List Fact)) :=
 catalogue (slices (Basis owners pool)) (Basis owners pool).length

theorem code_finite (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) : code registry root owners pool source ∈ codebook owners pool :=
 FiniteBehaviorClassifier269.finite (sourceBasis registry root owners pool) _ source
  (project owners pool source).canonical.length_le

theorem code_label (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) : (code registry root owners pool source).label = (project owners pool source).remaining :=
 FiniteBehaviorClassifier269.classifier_label (sourceBasis registry root owners pool) source

theorem advance_exact (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (target : Code (List Fact)) :
 Advances (code registry root owners pool source) target ↔
 ∃ after, Weak registry root owners pool source after ∧ code registry root owners pool after = target :=
 FiniteBehaviorClassifier269.child_iff (sourceBasis registry root owners pool) source target

theorem same_code_project (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) (same : code registry root owners pool first = code registry root owners pool last) :
 project owners pool first = project owners pool last := by
 apply state_ext
 rw [←code_label registry root owners pool first,←code_label registry root owners pool last,same]

theorem same_code_bisim (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (one two after : State roles) (same : code registry root owners pool one = code registry root owners pool two)
 (step : Weak registry root owners pool one after) :
 ∃ companion, Weak registry root owners pool two companion ∧
  code registry root owners pool after = code registry root owners pool companion :=
 FiniteBehaviorClassifier269.transfer_step (sourceBasis registry root owners pool) same step

theorem terminal_iff (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) :
 (code registry root owners pool source).children = [] ↔
 ∀ after, B4Target.Steps (Step registry root) source after → project owners pool after = project owners pool source :=
 (FiniteBehaviorClassifier269.terminal_iff (sourceBasis registry root owners pool) source).trans
   (GeneralRebaseWeakTerminal268.terminal_iff registry root owners pool source)

theorem trace_old (trace : Trace (Weak registry root owners pool) count first last) :
 B4Target.Steps (Step registry root) first last := by
 induction trace with
 | nil => exact .refl
 | cons one _ ih => exact GeneralRebaseWeakTerminal268.append (weak_source one) ih

theorem snoc {R : α → α → Prop} (trace : Trace R count first middle) (step : R middle last) :
 Trace R (count+1) first last := by
 induction trace with
 | nil => exact .cons step (.nil _)
 | cons move _ ih => exact .cons move (ih step)

theorem counted_to_trace (trace : Counted registry root owners pool count first last) :
 Trace (Weak registry root owners pool) count first last := by
 induction trace with
 | nil => exact .nil _
 | tail _ step ih => exact snoc ih step

theorem abstract_trace_old (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (trace : Trace Advances count (code registry root owners pool source) target) :
 ∃ after, B4Target.Steps (Step registry root) source after ∧ code registry root owners pool after = target := by
 obtain ⟨after,recovered,related⟩ := reflect_trace (sourceBasis registry root owners pool) trace source rfl
 exact ⟨after,trace_old recovered,related⟩

/-- A finite old trace yields an abstract trace with its strict count and
final observation; the stutter suffix need not have preserved the code. -/
theorem old_to_abstract (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source after : State roles) (trace : B4Target.Steps (Step registry root) source after) :
 ∃ n codeEnd, Trace Advances n (code registry root owners pool source) codeEnd ∧
 codeEnd.label = (project owners pool after).remaining ∧
 n + (project owners pool after).remaining.length ≤ (project owners pool source).remaining.length := by
 obtain ⟨n,mid,steps,stutter,_⟩ := GeneralRebaseWeakProgress268.decomposition registry root owners pool trace
 have observe := congrArg GeneralRebaseStep258.State.remaining (lull_same stutter)
 refine ⟨n,code registry root owners pool mid,
   simulate_trace (sourceBasis registry root owners pool) (counted_to_trace steps),?_,?_⟩
 · exact (code_label registry root owners pool mid).trans observe.symm
 · simpa only [observe] using GeneralRebaseWeakProgress268.budget steps

/-- The finite quotient drive terminates at an observation stable under all
finite old continuations; its initial code is not constructively extracted. -/
theorem settle (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) :
 let result := FiniteBehaviorDriver269.drive (Basis owners pool).length (code registry root owners pool source)
 ∃ after, B4Target.Steps (Step registry root) source after ∧
 result.2.label = (project owners pool after).remaining ∧
 (∀ future, B4Target.Steps (Step registry root) after future → project owners pool future = project owners pool after) ∧
 result.1 + (project owners pool after).remaining.length ≤ (project owners pool source).remaining.length := by
 obtain ⟨after,trace,repr,terminal,budget⟩ := FiniteBehaviorDriver269.drive_correct
   (sourceBasis registry root owners pool) (Basis owners pool).length source
   (project owners pool source).canonical.length_le
 exact ⟨after,trace_old trace,(congrArg Code.label repr).symm.trans (code_label registry root owners pool after),
   (GeneralRebaseWeakTerminal268.terminal_iff registry root owners pool after).mp terminal,budget⟩

end Yulang.GeneralRebaseBehavior269
