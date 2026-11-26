import Yulang.GeneralDeclarativeI65I72CompletedUnaryTrace406
import Yulang.GeneralDeclarativeI65I74CompletedLowerRetained437

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438

open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Summarizes)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)

/-- A new source lane, limited to an actually selected completed-native
leaf. Ordinary, projected and completed heads remain different. The
retained row belongs to the original output of the actual producer in
the invocation's finite `SupportForest`, not another trace at its target. -/
structure CompletedHead18 {s : I72.State} {q : Request}
    (event : CompletedInvocation406 s q []) where
  other : event.chosen.need.producer.occurrence ≠ q.occurrence
  retained : CompletedLower437.Payload event.chosen.gate.arg.lower
    (event.chosen.producer.event.outputs event.chosen.need.ordinal).receipt
  code : fixedValueCode403 (event.chosen.producer.event.outputs event.chosen.need.ordinal).rhs =
    some retained.code

/-- No model gives permission to elect. This packages the independent
source derivation and the even more precise literal row address. -/
structure Selected18 (s : I72.State) (q : Request) where
  invocation : CompletedInvocation406 s q []
  head : CompletedHead18 invocation

def Selected18.dictionary {s q} (selected : Selected18 s q) : Dictionary :=
  .node selected.invocation.row.id []

def Classifies18 (prior : SourcePrimitives .withEndpoint)
    (s : I72.State) (q : Request) (r : Result) : Prop :=
  I72.Classifies prior s q r ∨ ∃ selected : Selected18 s q, r = .selected selected.dictionary

/-- The original body plan, exact associated output and fixed slot
are interpreted by the same model as the consumer's invocation.
The `nativeSyntax` at the lower name is not a field of this evidence. -/
def CompletedHead18.Means {s : I72.State} {q : Request} {event : CompletedInvocation406 s q []}
    (_head : CompletedHead18 event) (m : I72.Model) : Prop :=
  let producer := event.chosen.producer
  let i := event.chosen.need.ordinal
  let out := producer.event.outputs i
  ∃ ty,
    s.b6.read event.chosen.need.producer producer.event.frame.ordinal i out.body = some out.plan ∧
    evaluateMixedRhs401 (sourceRead401 m (producer.event.frame.slots out.body)) out.plan = some ty ∧
    out.receipt.actualEquation m = some (event.chosen.gate.arg.lower,ty) ∧
    Equivalent (m.assignment event.chosen.gate.arg.lower).1 ty

inductive DictionaryEvidence18 (s : I72.State) (m : I72.Model) : Request → Dictionary → Prop where
  | previous : I72.DictionaryEvidence s m q d → DictionaryEvidence18 s m q d
  | completed (selected : Selected18 s q) :
      selected.head.Means m → CompletedInvocationMeaning406 selected.invocation m →
      DictionaryEvidence18 s m q selected.dictionary

theorem completed_head_has_literal_original_meaning438 {s : I72.State} {q : Request}
    {event : CompletedInvocation406 s q []} (head : CompletedHead18 event)
    (m : I72.Model) (fit : I72.Fits s m) : head.Means m := by
  exact CompletedLower437.lower_retention_uses_original_B6_value437
    (event.chosen.producer.event.outputs event.chosen.need.ordinal) head.retained head.code m fit

theorem completed_selected_evidence438 {s q} (selected : Selected18 s q)
    (m : I72.Model) (fit : I72.Fits s m) : DictionaryEvidence18 s m q selected.dictionary :=
  .completed selected (completed_head_has_literal_original_meaning438 selected.head m fit)
    (completed_invocation_means_one_state_and_model406 selected.invocation m fit)

theorem dictionary_sound_of_prior438 {prior : SourcePrimitives .withEndpoint}
    (old : I72.DictionarySound prior) :
    ∀ s q d, Classifies18 prior s q (.selected d) →
      ∀ m, I72.Fits s m → DictionaryEvidence18 s m q d := by
  intro s q d claimed m fit
  rcases claimed with before | ⟨selected, same⟩
  · exact .previous (old s q d before m fit)
  · have eq : d = selected.dictionary := Result.selected.inj same
    subst d
    exact completed_selected_evidence438 selected m fit

theorem raw_root_K2_has_priority438 {prior : SourcePrimitives .withEndpoint} {s q}
    (raw : RootCycle s q) :
    Classifies18 prior s q .rejected ∧ ∀ d, ¬Classifies18 prior s q (.selected d) := by
  refine ⟨.inl (root_k2_is_rejected_for_every_primitive_system raw),?_⟩
  rintro d (old | ⟨selected,_⟩)
  · exact root_k2_never_selects raw old
  · exact selected.invocation.chosen.rootSafe raw

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
