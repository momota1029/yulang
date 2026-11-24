import Yulang.GeneralDeclarativeI65I72Assembly402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72

open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open CommonDeclaredNominalInspection (Kind)

/-- Data for a genuinely entered candidate inspection. The normative
source predicates which say *which* visits are required and supported
are an explicit open interface in this typed skeleton. -/
structure CandidateVisit where
  declarationOrdinal : Nat
  argumentOrdinal : Nat
  path : List Nat
  kind : Kind
  upper : Bool
  site : Nat

inductive BodyKind where
  | ordinary
  | typedOrMixed

structure SourceSpecification (R : SourcePrimitives) where
  required : ∀ s q, Event s q → CandidateVisit → Prop
  supported : ∀ s q, Event s q → CandidateVisit → Prop
  spans : ∀ s q, Event s q → List (Nat × Capture) → Prop
  bodyCase : ∀ s q, Event s q → BodyKind

structure SelectedSource (R : SourcePrimitives) {s q} (e : Event s q)
    (needs : List (OutputNeed s)) (supports : SupportForest R s needs) where
  tape : CandidateTape s.core q (visible s.core q)
  origin : SelectedHeadOrigin395 (row := e.frame.decl) tape
  atOriginal : origin.rawOrdinal = e.frame.ordinal
  visits : List CandidateVisit

/-- Inversion obligation. The source event and exact support proof
are inputs of the conclusion's index; no arbitrary frame or different
finite producer can be substituted at a matching dictionary key. -/
def S02 (R : SourcePrimitives) : Prop :=
  ∀ s q (e : Event s q) needs, ¬ RootCycle s q → R.elected s q e needs →
    ∀ supports : SupportForest R s needs, Nonempty (SelectedSource R e needs supports)

def CurrentCycleAt (s : State) (slot : Nat) : Prop :=
  GeneralDeclarativeK2Alias321.AliasCycle s.core.current.ordinary
    (GeneralDeclarativeGraphRows321.observed s.core.current.ordinary) slot

def SelectedPriority {R s q e needs supports} (K : SourceSpecification R)
    (src : SelectedSource (s := s) (q := q) R e needs supports) : Prop :=
  ¬ RootCycle s q ∧
    (∀ site, site ∈ src.visits ↔ K.required s q e site) ∧
    (∀ site ∈ src.visits, K.supported s q e site ∧ ¬ CurrentCycleAt s site.site) ∧
    src.tape.waits = false ∧ src.tape.live = [e.frame.decl]

def S03 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (src : SelectedSource R e needs supports),
    ¬ RootCycle s q → R.elected s q e needs → SelectedPriority K src

def SameAuthoredHead {R s q e needs supports}
    (src : SelectedSource (s := s) (q := q) R e needs supports)
    (head : SourceHead s.core q e.frame.decl) : Prop :=
  head = src.origin.pick.head ∧ head = e.head

def S04 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (src : SelectedSource R e needs supports),
    SelectedPriority K src →
    ∃ head : SourceHead s.core q e.frame.decl, SameAuthoredHead src head

structure GeneralCapture {s q} (e : Event s q) (head : SourceHead s.core q e.frame.decl) where
  spans : List (Nat × Capture)
  names : Nat → Capture

/-- Same-name repeated centers are tied in the actual, unfiltered
current ordinary state; equal bounds are not substituted for them. -/
def TieRows {s q} {e : Event s q} {head}
    (capture : GeneralCapture e head) : Prop :=
  ∀ n a b, (n,a) ∈ capture.spans → (n,b) ∈ capture.spans →
    GeneralDeclarativeEqualities322.Derives s.core.current.ordinary
      (.variable a.center) (.variable b.center)

def ExactCapture {R s q} (K : SourceSpecification R) {e : Event s q} {head}
    (capture : GeneralCapture e head) : Prop :=
  K.spans s q e capture.spans ∧ capture.names = e.frame.names.input ∧
    CapturesActualHead e ∧ TieRows capture

def S05 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (src : SelectedSource R e needs supports)
      (head : SourceHead s.core q e.frame.decl),
    SameAuthoredHead src head →
    ∃ capture : GeneralCapture e head, ExactCapture K capture

structure LiteralReceipt {s q} (e : Event s q) where
  written : List (NamedMixedReceipt401 s.core)
  kids : List Request
  sameOutput : written = List.ofFn (fun i => (e.outputs i).receipt)
  sameWhere : kids = e.kids

def S06 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (_ : SelectedSource R e needs supports)
      head (capture : GeneralCapture e head),
    ExactCapture K capture → K.bodyCase s q e = .ordinary → Nonempty (LiteralReceipt e)

/-- I-67 removes physical release, and I-71 requires the typed tree
rather than the retired wire. Logical same-model target retention is
a different obligation, S13bbbb, not an election input. -/
def S07 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (_ : SelectedSource R e needs supports)
      head (capture : GeneralCapture e head),
    ExactCapture K capture → K.bodyCase s q e = .typedOrMixed → Nonempty (LiteralReceipt e)

def S08 {R : SourcePrimitives} (K : SourceSpecification R) : Prop :=
  ∀ s q (e : Event s q) needs supports (src : SelectedSource R e needs supports)
      (head : SourceHead s.core q e.frame.decl) (capture : GeneralCapture e head),
    SameAuthoredHead src head → ExactCapture K capture → LiteralReceipt e → GeneralNode e

theorem provide_node_at_same_selected_source {R : SourcePrimitives} (K : SourceSpecification R) :
    S02 R → S03 K → S04 K → S05 K → S06 K → S07 K → S08 K → S10 R := by
  intro invert priorities read capture ordinary typed assembleNode s q event needs raw chosen supports
  obtain ⟨src⟩ := invert s q event needs raw chosen supports
  obtain ⟨head,same⟩ := read s q event needs supports src (priorities s q event needs supports src raw chosen)
  obtain ⟨cap,exactCap⟩ := capture s q event needs supports src head same
  have packet : Nonempty (LiteralReceipt event) := by
    cases kindAt : K.bodyCase s q event with
    | ordinary => exact ordinary s q event needs supports src head cap exactCap kindAt
    | typedOrMixed => exact typed s q event needs supports src head cap exactCap kindAt
  obtain ⟨receipt⟩ := packet
  exact assembleNode s q event needs supports src head cap same exactCap receipt

/-- The named dependency chain for the draft signature. The missing
source primitives are explicit and not discharged by this assembly. -/
theorem assemble_named {R : SourcePrimitives} (K : SourceSpecification R) :
    S01 R → S02 R → S03 K → S04 K → S05 K → S06 K → S07 K → S08 K →
    S09 → S11 R → S13a R → S13ba R → S13bba R → S13bbba → S13bbbb →
    DictionarySound R := by
  intro a b c d e f g h semantics lowering align preserve addresses sourceRhs fixed
  exact assemble R a (provide_node_at_same_selected_source K b c d e f g h)
    lowering (general_tree_meaning_from_local R semantics) align preserve addresses sourceRhs fixed


/-- After applying the checked structural lemmas, this lists the nine
remaining hypotheses of the *uninstantiated signature*. It is not a
count of completed production Yulang lemmas. -/
theorem assemble_remaining {R : SourcePrimitives} (K : SourceSpecification R) :
    S02 R → S03 K → S04 K → S05 K → S06 K → S07 K → S08 K →
    S13bbba → S13bbbb → DictionarySound R := by
  intro a b c d e f g src fixed
  exact assemble_named K (classifies_unpacks_source_in_signature R) a b c d e f g
    semantic_node_in_signature (lower_selected_at_exact_trace R)
    (typed_replay_alignment_in_signature R)
    (typed_replay_keeps_same_event_meaning R)
    (typed_replay_keeps_original_addresses R) src fixed

end Yulang.GeneralDeclarativeI65.I72
