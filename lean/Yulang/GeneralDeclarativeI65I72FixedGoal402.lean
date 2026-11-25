import Yulang.GeneralDeclarativeI65MixedQualification401
import Yulang.GeneralDeclarativeI65I75ProjectedEventSource426

namespace Yulang.GeneralDeclarativeI65
namespace I72

open CommonRoleOutermostResolver (Tree Result Dictionary Summarizes)
open CommonNominalFullCarrier (Equivalent)

/-- The C365 logical snapshot plus actual B6 annotation input,
indexed by original request, declaration ordinal, output index,
and authored body. No solver state is added. -/
structure State where
  core : GeneralDeclarativeI65.State
  b6 : B6OccurrenceAtlas401 core

abbrev Request := GeneralDeclarativeI65.Request
abbrev Model := GeneralDeclarativeI65.Model

def Fits (s : State) (m : Model) : Prop := GeneralDeclarativeI65.Fits s.core m

/-- Source terms and logical slots, but no model-valued proof. -/
structure Event (s : State) (q : Request) where
  frame : AuthoredBodyFrame393 s.core q
  head : SourceHead s.core q frame.decl
  outputs : ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 frame i

def Event.kids {s q} (e : Event s q) : List Request := frameWhereKids400 e.frame

/-- Exact completed logical producer and emitted output. No release,
version, solver history, or authority attached to the name alone. -/
structure OutputNeed (s : State) where
  producer : Request
  dictionary : Dictionary
  ordinal : Fin producer.demand.outputs.length
  expected : NamedMixedReceipt401 s.core

inductive OtherVerdict where
  | pending
  | ambiguous
  | rejected

def OtherVerdict.tree : OtherVerdict → Tree
  | .pending => .pending
  | .ambiguous => .ambiguous
  | .rejected => .rejected

/-- Open primitive source-rule boundary. No solver or model is an
argument, and finite dependencies are constructed below. A language
instance must supply actual whole visible-candidate tests, precise
authorized visits and priorities, and independent source choice.
This boundary is not a finished definition of all source rules. -/
structure SourcePrimitives where
  elected : (s : State) → (q : Request) → Event s q → List (OutputNeed s) → Prop
  other : (s : State) → Request → OtherVerdict → List (OutputNeed s) → Prop

def RootCycle (s : State) (q : Request) : Prop :=
  ∃ a ∈ q.demand.arguments,
    GeneralDeclarativeK2Alias321.AliasCycle s.core.current.ordinary
      (GeneralDeclarativeGraphRows321.observed s.core.current.ordinary) a.lower

mutual
/-- A finite derivation. Ordered where children and smaller read
producer proofs are distinct. Raw root K2 is unfiltered and
precedes every other case. -/
inductive SourceTrace (R : SourcePrimitives) (s : State) :
    (q : Request) → Tree → Option (Event s q) → Type where
  | rootK2 (cycle : RootCycle s q) : SourceTrace R s q .rejected none
  | other (verdict : OtherVerdict) (rawSafe : ¬ RootCycle s q)
      (primitive : R.other s q verdict needs) :
      SupportForest R s needs → SourceTrace R s q verdict.tree none
  | selected (event : Event s q) (rawSafe : ¬ RootCycle s q)
      (primitive : R.elected s q event needs) :
      SupportForest R s needs → WhereForest R s event.kids trees →
      SourceTrace R s q (.selected event.frame.decl.id trees) (some event)

inductive WhereForest (R : SourcePrimitives) (s : State) :
    List Request → List Tree → Type where
  | nil : WhereForest R s [] []
  | cons : SourceTrace R s q t event → WhereForest R s qs ts →
      WhereForest R s (q::qs) (t::ts)

inductive SupportForest (R : SourcePrimitives) (s : State) : List (OutputNeed s) → Type where
  | nil : SupportForest R s []
  | cons {n : OutputNeed s} {e : Event s n.producer} :
      SourceTrace R s n.producer t (some e) →
      Summarizes t (.selected n.dictionary) →
      (e.outputs n.ordinal).receipt = n.expected →
      SupportForest R s rest →
      SupportForest R s (n::rest)
end

/-- Structural classifier relative to explicitly open primitive source
rules. The concrete Yulang instance is still to be supplied. -/
def Classifies (R : SourcePrimitives) (s : State) (q : Request) (result : Result) : Prop :=
  ∃ t : Tree, ∃ event : Option (Event s q),
    Nonempty (SourceTrace R s q t event) ∧ Summarizes t result

/-- Meaning of the original literal RHS alone. This layer does not
equate its value to the assigned fixed target. -/
def LocalRhsMeaning {s q} (m : Model) (e : Event s q) : Prop :=
  ∀ i : Fin q.demand.outputs.length, ExactNamedOutputMeaning401 m (e.outputs i)

/-- Separate fixed-target semantic obligation in this same model. -/
def FixedTargets {s q} (m : Model) (e : Event s q) : Prop :=
  ∀ i : Fin q.demand.outputs.length,
    ∃ value, (e.outputs i).receipt.actualEquation m = some (q.demand.outputs[i].target,value) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 value

structure LocalMeaning {s q} (m : Model) (e : Event s q) : Prop where
  head : HeadModel s.core m q e.frame.decl e.head
  rhs : LocalRhsMeaning m e

/-- Convert the independently authored endpoint head. The exact
payload comes from the same original B6 leaf, not the named frame. -/
def canonicalEndpointHead426 {s : State} {q : Request}
    (e : ProjectedCore425.OriginalProjectedLeaf426 s.core s.b6 q) :
    SourceHead s.core q e.out.row .endpoint :=
  .endpointRecord e.head.request e.head.pattern e.head.distinct e.head.endpoints

theorem original_projected_leaf_has_canonical_head426 {s : State} {q : Request}
    (e : ProjectedCore425.OriginalProjectedLeaf426 s.core s.b6 q) (m : Model) (fit : Fits s m) :
    HeadModel s.core m q e.out.row (canonicalEndpointHead426 e) :=
  source_head_sound _ m fit

mutual
/-- Recursive semantic evidence, not a checker or source classifier. -/
inductive DictionaryEvidence (s : State) (m : Model) : Request → Dictionary → Prop where
  | node (event : Event s q) :
      LocalMeaning m event → FixedTargets m event →
      DictionaryEvidenceForest s m event.kids ds →
      DictionaryEvidence s m q (.node event.frame.decl.id ds)

  | endpointLeaf
      (event : ProjectedCore425.OriginalProjectedLeaf426 s.core s.b6 q) :
      HeadModel s.core m q event.out.row (canonicalEndpointHead426 event) →
      (∀ i : Fin q.demand.outputs.length, ∃ v,
        event.out.valueAt m = some (q.occurrence,event.out.ordinal,i.val,q.demand.outputs[i].target,v) ∧
        Equivalent (m.assignment q.demand.outputs[i].target).1 v) →
      DictionaryEvidence s m q event.dictionary

inductive DictionaryEvidenceForest (s : State) (m : Model) : List Request → List Dictionary → Prop where
  | nil : DictionaryEvidenceForest s m [] []
  | cons : DictionaryEvidence s m q d → DictionaryEvidenceForest s m qs ds →
      DictionaryEvidenceForest s m (q::qs) (d::ds)
end

/-- Produce the added canonical evidence only from the actual
endpoint head, original typed B6 output and independent retention. -/
theorem original_projected_leaf_with_retention_has_dictionary_evidence426
    {s : State} {q : Request}
    (event : ProjectedCore425.OriginalProjectedLeaf426 s.core s.b6 q)
    (kept : ProjectedCore425.RequiredRetention426 event.out)
    (m : Model) (fit : Fits s m) : DictionaryEvidence s m q event.dictionary := by
  have facts := ProjectedCore425.one_projected_leaf_keeps_output_at_original_target426 event kept m fit
  refine .endpointLeaf event (.endpointRecord facts.1) ?_
  intro i
  obtain ⟨v,_,seen,eq⟩ := facts.2 i
  exact ⟨v,seen,eq⟩

/-- The fixed quantifiers and implications, relative to the open
source primitive system. No soundness premise has been added. -/
def DictionarySound (R : SourcePrimitives) : Prop :=
  ∀ s q d, Classifies R s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence s m q d

theorem root_k2_forces_original_trace_verdict {R s q t e}
    (cycle : RootCycle s q) (trace : SourceTrace R s q t e) :
    t = .rejected := by
  cases trace with
  | rootK2 => rfl
  | other _ safe _ _ => exact (safe cycle).elim
  | selected _ safe _ _ _ => exact (safe cycle).elim


theorem root_k2_is_rejected_for_every_primitive_system {R s q} (cycle : RootCycle s q) :
    Classifies R s q .rejected :=
  ⟨.rejected,none,⟨.rootK2 cycle⟩,.rejected⟩

theorem root_k2_never_selects {R s q d} (cycle : RootCycle s q) :
    ¬ Classifies R s q (.selected d) := by
  rintro ⟨t,_,⟨trace⟩,summary⟩
  rw [root_k2_forces_original_trace_verdict cycle trace] at summary
  cases summary

end I72
end Yulang.GeneralDeclarativeI65
