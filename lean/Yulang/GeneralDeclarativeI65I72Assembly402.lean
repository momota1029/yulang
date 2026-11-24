import Yulang.GeneralDeclarativeI65I72FixedGoal402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72

open CommonRoleOutermostResolver (Tree Result Dictionary Frontier Resolves Summarizes All₂ Combine)
open GeneralDeclarativeWitnessTree349 (dictionaryTree dictionaryForest)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (DeclarationChecked)

def OtherSupported (R : SourcePrimitives) (s : State) (q : Request) (verdict : OtherVerdict) : Prop :=
  ∃ needs, ¬ RootCycle s q ∧ R.other s q verdict needs ∧ Nonempty (SupportForest R s needs)

def LocalSource (R : SourcePrimitives) (s : State) (q : Request) : Frontier Request → Prop
  | .pending => OtherSupported R s q .pending
  | .ambiguous => OtherSupported R s q .ambiguous
  | .rejected => RootCycle s q ∨ OtherSupported R s q .rejected
  | .selected key kids =>
    ∃ (event : Event s q) (needs : List (OutputNeed s)), event.frame.decl.id = key ∧ event.kids = kids ∧
      ¬ RootCycle s q ∧ R.elected s q event needs ∧ Nonempty (SupportForest R s needs)

theorem source_trace_projects {R s q t e} (trace : SourceTrace R s q t e) :
    Resolves (LocalSource R s) q t := by
  exact SourceTrace.rec
    (motive_1 := fun q t _ _ => Resolves (LocalSource R s) q t)
    (motive_2 := fun qs ts _ => All₂ (Resolves (LocalSource R s)) qs ts)
    (motive_3 := fun _ _ => True)
    (fun cycle => .rejected (.inl cycle))
    (fun verdict raw primitive support _ => by
      have someSupport : OtherSupported R s _ verdict := ⟨_,raw,primitive,⟨support⟩⟩
      cases verdict with
      | pending => exact .pending someSupport
      | ambiguous => exact .ambiguous someSupport
      | rejected => exact .rejected (.inr someSupport))
    (fun e raw primitive support _ _ whereDerives =>
      .selected ⟨e,_,rfl,rfl,raw,primitive,⟨support⟩⟩ whereDerives)
    .nil
    (fun _ _ a b => .cons a b)
    .intro
    (fun _ _ _ _ _ _ => True.intro)
    trace

structure SourceTreeTrace (R : SourcePrimitives) (s : State) (q : Request) (t : Tree)
    (projection : Resolves (LocalSource R s) q t) where
  event : Option (Event s q)
  source : SourceTrace R s q t event
  projected : source_trace_projects source = projection

def S01 (R : SourcePrimitives) : Prop :=
  ∀ s q d, Classifies R s q (.selected d) →
    ∃ t : Tree, ∃ tree : Resolves (LocalSource R s) q t,
      ∃ _trace : SourceTreeTrace R s q t tree, Summarizes t (.selected d)

theorem classifies_unpacks_source_in_signature (R : SourcePrimitives) : S01 R := by
  rintro s q d ⟨t,e,⟨source⟩,outcome⟩
  exact ⟨t,source_trace_projects source,⟨e,source,rfl⟩,outcome⟩

/-- A nonsemantic check linking the actual captured centers in the
head to the frame before emission. The uninstantiated plain/mixed
kernel still has to supply the full ordered capture and ties. -/
def CapturesActualHead {s q} (e : Event s q) : Prop :=
  match e.head with
  | .ordered before _ =>
    ∀ n ∈ e.frame.decl.inputNames, (e.frame.names.input n).center = (before n).center
  | .joined read =>
    ∀ n ∈ e.frame.decl.inputNames, (e.frame.names.input n).center = read.actualValue

structure GeneralNode {s q} (e : Event s q) : Prop where
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles e.frame.decl
  captures : CapturesActualHead e

def S09 : Prop :=
  ∀ s q (e : Event s q), GeneralNode e → ∀ m, Fits s m → LocalMeaning m e

def ProvidesGeneralNode (R : SourcePrimitives) (s : State) : Prop :=
  ∀ q (e : Event s q) needs, ¬ RootCycle s q → R.elected s q e needs →
    SupportForest R s needs → GeneralNode e

def S10 (R : SourcePrimitives) : Prop := ∀ s, ProvidesGeneralNode R s

mutual
inductive GeneralTree {R : SourcePrimitives} {s : State} :
    {q : Request} → {t : Tree} → {e : Option (Event s q)} →
    SourceTrace R s q t e → Dictionary → Type where
  | node {event : Event s q} {rawSafe : ¬ RootCycle s q}
      {primitive : R.elected s q event needs}
      {support : SupportForest R s needs} {kids : WhereForest R s event.kids ts} :
      GeneralNode event → GeneralForest kids ds →
      GeneralTree (.selected event rawSafe primitive support kids) (.node event.frame.decl.id ds)

inductive GeneralForest {R : SourcePrimitives} {s : State} :
    {qs : List Request} → {ts : List Tree} → WhereForest R s qs ts → List Dictionary → Type where
  | nil : GeneralForest .nil []
  | cons : GeneralTree a d → GeneralForest b ds → GeneralForest (.cons a b) (d::ds)
end

structure LoweringPair (R : SourcePrimitives) (s : State) : Prop where
  tree : ∀ {q t e d} (trace : SourceTrace R s q t e), Summarizes t (.selected d) →
    Nonempty (GeneralTree trace d) ∧ t = dictionaryTree d
  forest : ∀ {qs ts ds} (trace : WhereForest R s qs ts), All₂ Summarizes ts (ds.map Result.selected) →
    Nonempty (GeneralForest trace ds) ∧ ts = dictionaryForest ds

def S11 (R : SourcePrimitives) : Prop := ∀ s, ProvidesGeneralNode R s → LoweringPair R s

mutual
inductive Ledger (s : State) : Request → Dictionary → Type where
  | node (e : Event s q) : LedgerForest s e.kids ds → Ledger s q (.node e.frame.decl.id ds)

inductive LedgerForest (s : State) : List Request → List Dictionary → Type where
  | nil : LedgerForest s [] []
  | cons : Ledger s q d → LedgerForest s qs ds → LedgerForest s (q::qs) (d::ds)
end

mutual
def GeneralTree.ledger {R s q t e d} {trace : SourceTrace R s q t e}
    (tree : GeneralTree trace d) : Ledger s q d :=
  match tree with
  | @GeneralTree.node _ _ _ _ _ _ event _ _ _ _ _ kids => .node event kids.ledger

def GeneralForest.ledger {R s qs ts ds} {trace : WhereForest R s qs ts}
    (tree : GeneralForest trace ds) : LedgerForest s qs ds :=
  match tree with
  | .nil => .nil
  | .cons a b => .cons a.ledger b.ledger
end

mutual
def LedgerMeaning {s q d} (P : ∀ {q}, Event s q → Prop) : Ledger s q d → Prop
  | .node e kids => P e ∧ LedgerForestMeaning P kids

def LedgerForestMeaning {s qs ds} (P : ∀ {q}, Event s q → Prop) : LedgerForest s qs ds → Prop
  | .nil => True
  | .cons a b => LedgerMeaning P a ∧ LedgerForestMeaning P b
end

mutual
def TreeMeaningOver {R s q t e d} {trace : SourceTrace R s q t e}
    (P : ∀ {q}, Event s q → Prop) : GeneralTree trace d → Prop
  | @GeneralTree.node _ _ _ _ _ _ event _ _ _ _ _ kids => P event ∧ ForestMeaningOver P kids

def ForestMeaningOver {R s qs ts ds} {trace : WhereForest R s qs ts}
    (P : ∀ {q}, Event s q → Prop) : GeneralForest trace ds → Prop
  | .nil => True
  | .cons a b => TreeMeaningOver P a ∧ ForestMeaningOver P b
end

def S12 (R : SourcePrimitives) : Prop :=
  ∀ s q t e d (trace : SourceTrace R s q t e) (lowered : GeneralTree trace d) m,
    Fits s m → TreeMeaningOver (LocalMeaning m) lowered

mutual
def Ledger.written {s q d} : Ledger s q d → List (NamedMixedReceipt401 s.core)
  | .node e kids => List.ofFn (fun i => (e.outputs i).receipt) ++ kids.written

def LedgerForest.written {s qs ds} : LedgerForest s qs ds → List (NamedMixedReceipt401 s.core)
  | .nil => []
  | .cons a b => a.written ++ b.written
end

/-- Canonical alignment records the very same data, not an equal key. -/
def CanonicalReplay {R s q t e d} {trace : SourceTrace R s q t e}
    (tree : GeneralTree trace d) (ledger : Ledger s q d) : Prop :=
  tree.ledger = ledger ∧ t = dictionaryTree d ∧ ledger.written = tree.ledger.written

def Addresses {s q} (e : Event s q) : Prop :=
  (authoredRegistry s.core.current).declarations[e.frame.ordinal]? = some e.frame.decl ∧
  ∀ i : Fin q.demand.outputs.length,
    (e.outputs i).receipt.occurrence = q.occurrence ∧
    (e.outputs i).receipt.outputOrdinal = i.val ∧
    (e.outputs i).receipt.original = q.demand.outputs[i]

def ExactSourceRhs {s q} (e : Event s q) : Prop :=
  ∀ i : Fin q.demand.outputs.length,
    let out := e.outputs i
    GeneralDictionaryAssociatedProvenance.Supplies (authoredRegistry s.core.current).roles
      e.frame.decl q.demand.outputs[i].name out.body ∧
    s.b6.read q e.frame.ordinal i out.body = some out.plan ∧
    substituteMixedRhs401 (instantiateName401 (e.frame.slots out.body)) out.plan = some out.rhs

def S13a (R : SourcePrimitives) : Prop :=
  ∀ s q t e d (trace : SourceTrace R s q t e) (lowered : GeneralTree trace d),
    t = dictionaryTree d → ∃ ledger, CanonicalReplay lowered ledger

def S13ba (R : SourcePrimitives) : Prop :=
  ∀ s q t e d (trace : SourceTrace R s q t e) (lowered : GeneralTree trace d) ledger m,
    CanonicalReplay lowered ledger → TreeMeaningOver (LocalMeaning m) lowered →
      LedgerMeaning (LocalMeaning m) ledger

def S13bba (R : SourcePrimitives) : Prop :=
  ∀ s q t e d (trace : SourceTrace R s q t e) (lowered : GeneralTree trace d) ledger,
    CanonicalReplay lowered ledger → LedgerMeaning Addresses ledger

def S13bbba : Prop :=
  ∀ s q d (ledger : Ledger s q d) m,
    LedgerMeaning Addresses ledger → LedgerMeaning (LocalMeaning m) ledger →
      LedgerMeaning ExactSourceRhs ledger

def S13bbbb : Prop :=
  ∀ s q d (ledger : Ledger s q d) m written,
    LedgerMeaning Addresses ledger → ledger.written = written → LedgerMeaning (LocalMeaning m) ledger →
    LedgerMeaning ExactSourceRhs ledger → DictionaryEvidence s m q d

/-- C380's top wiring, now typechecked for the explicit kernel signature.
It does not prove that the missing source-rule instance or any input
obligation holds. Its conclusion retains the frozen goal's quantifiers. -/
theorem assemble (R : SourcePrimitives) :
    S01 R → S10 R → S11 R → S12 R → S13a R → S13ba R → S13bba R →
      S13bbba → S13bbbb → DictionarySound R := by
  intro unpack localNode lower meaning align semantics addresses exactRhs retain s q d selected m fits
  obtain ⟨t,_,source,summary⟩ := unpack s q d selected
  obtain ⟨⟨node⟩,rendered⟩ := (lower s (localNode s)).tree source.source summary
  obtain ⟨ledger,same⟩ := align s q t source.event d source.source node rendered
  have actual := semantics s q t source.event d source.source node ledger m same
    (meaning s q t source.event d source.source node m fits)
  have address := addresses s q t source.event d source.source node ledger same
  exact retain s q d ledger m node.ledger.written address same.2.2 actual (exactRhs s q d ledger m address actual)


theorem semantic_node_in_signature : S09 := by
  intro s q e prepared m fits
  refine ⟨source_head_sound e.head m fits,fun i => ?_⟩
  let out := e.outputs i
  have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact _ _
    prepared.checked.identified.2.2.1 _ _).mpr out.supplied
  exact ⟨rfl,rfl,rfl,supplied,out.originalTyped,named_mixed_output_is_fixed_equation401 out m⟩

private theorem lowering_at_actual_trace {R s} (locals : ProvidesGeneralNode R s)
    {q t e} (trace : SourceTrace R s q t e) :
    ∀ d, Summarizes t (.selected d) → Nonempty (GeneralTree trace d) ∧ t = dictionaryTree d := by
  exact SourceTrace.rec
    (motive_1 := fun _ t _ trace => ∀ d, Summarizes t (.selected d) →
      Nonempty (GeneralTree trace d) ∧ t = dictionaryTree d)
    (motive_2 := fun _ trees forest => ∀ ds, All₂ Summarizes trees (ds.map Result.selected) →
      Nonempty (GeneralForest forest ds) ∧ trees = dictionaryForest ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ impossible => by cases impossible)
    (fun verdict _ _ _ _ _ impossible => by cases verdict <;> cases impossible)
    (fun event raw selected support _ _ child d summary => by
      cases summary with
      | selected rows combine =>
        cases combine with
        | selected exacts =>
          rw [exacts] at rows
          obtain ⟨⟨kids⟩,literal⟩ := child _ rows
          exact ⟨⟨.node (locals _ event _ raw selected support) kids⟩,by
            simp only [dictionaryTree,literal]⟩)
    (fun ds summary => by
      cases ds with
      | nil => exact ⟨⟨.nil⟩,by simp [dictionaryForest]⟩
      | cons d ds => cases summary)
    (fun _ _ head tail ds summary => by
      cases ds with
      | nil => cases summary
      | cons d ds =>
        cases summary with
        | cons first rest =>
          obtain ⟨⟨first⟩,atHead⟩ := head d first
          obtain ⟨⟨rest⟩,atTail⟩ := tail ds rest
          exact ⟨⟨.cons first rest⟩,by simp only [dictionaryForest,atHead,atTail]⟩)
    .intro
    (fun _ _ _ _ _ _ => True.intro)
    trace

private theorem lowering_original_forest {R s} (locals : ProvidesGeneralNode R s)
    {qs trees} (trace : WhereForest R s qs trees) :
    ∀ ds, All₂ Summarizes trees (ds.map Result.selected) →
      Nonempty (GeneralForest trace ds) ∧ trees = dictionaryForest ds := by
  intro ds h
  cases trace with
  | nil =>
    cases ds with
    | nil => exact ⟨⟨.nil⟩,by simp [dictionaryForest]⟩
    | cons _ _ => cases h
  | cons first rest =>
    cases ds with
    | nil => cases h
    | cons d ds =>
      cases h with
      | cons once later =>
        obtain ⟨⟨a⟩,atA⟩ := lowering_at_actual_trace locals first d once
        obtain ⟨⟨b⟩,atB⟩ := lowering_original_forest locals rest ds later
        exact ⟨⟨.cons a b⟩,by simp only [dictionaryForest,atA,atB]⟩

termination_by sizeOf trees

theorem lower_selected_at_exact_trace (R : SourcePrimitives) : S11 R := by
  intro s locals
  exact ⟨fun tree h => lowering_at_actual_trace locals tree _ h,
    fun forest h => lowering_original_forest locals forest _ h⟩

theorem general_tree_meaning_from_local (R : SourcePrimitives) (one : S09) : S12 R := by
  intro s q t e d trace lowered m fit
  exact GeneralTree.rec
    (motive_1 := fun {_ _ _} _ _ tree => TreeMeaningOver (LocalMeaning m) tree)
    (motive_2 := fun {_ _} _ _ forest => ForestMeaningOver (LocalMeaning m) forest)
    (fun witness _ below => by
      rw [TreeMeaningOver]
      exact ⟨one _ _ _ witness m fit,below⟩)
    (by simp only [ForestMeaningOver])
    (fun _ _ a b => by rw [ForestMeaningOver]; exact ⟨a,b⟩)
    lowered

theorem typed_replay_alignment_in_signature (R : SourcePrimitives) : S13a R := by
  intro s q t e d trace lowered rendered
  exact ⟨lowered.ledger,rfl,rendered,rfl⟩

private theorem same_event_meaning_in_ledger {R s q t e d} {trace : SourceTrace R s q t e}
    (P : ∀ {q}, Event s q → Prop) (tree : GeneralTree trace d) :
    TreeMeaningOver P tree → LedgerMeaning P tree.ledger := by
  exact GeneralTree.rec
    (motive_1 := fun {_ _ _} _ _ tree => TreeMeaningOver P tree → LedgerMeaning P tree.ledger)
    (motive_2 := fun {_ _} _ _ forest => ForestMeaningOver P forest → LedgerForestMeaning P forest.ledger)
    (fun _ _ below h => by
      rw [TreeMeaningOver] at h
      rw [GeneralTree.ledger,LedgerMeaning]
      exact ⟨h.1,below h.2⟩)
    (by simp only [ForestMeaningOver,GeneralForest.ledger,LedgerForestMeaning,imp_self])
    (fun _ _ a b h => by
      rw [ForestMeaningOver] at h
      rw [GeneralForest.ledger,LedgerForestMeaning]
      exact ⟨a h.1,b h.2⟩)
    tree

theorem typed_replay_keeps_same_event_meaning (R : SourcePrimitives) : S13ba R := by
  intro s q t e d trace lowered ledger m aligned sem
  rw [← aligned.1]
  exact same_event_meaning_in_ledger _ lowered sem

private theorem ledger_has_literal_addresses {s q d} (ledger : Ledger s q d) :
    LedgerMeaning Addresses ledger := by
  exact Ledger.rec
    (motive_1 := fun _ _ tree => LedgerMeaning Addresses tree)
    (motive_2 := fun _ _ forest => LedgerForestMeaning Addresses forest)
    (fun e _ below => by
      rw [LedgerMeaning]
      exact ⟨⟨e.frame.authored,fun _ => ⟨rfl,rfl,rfl⟩⟩,below⟩)
    (by simp only [LedgerForestMeaning])
    (fun _ _ a b => by rw [LedgerForestMeaning]; exact ⟨a,b⟩)
    ledger

theorem typed_replay_keeps_original_addresses (R : SourcePrimitives) : S13bba R := by
  intro s q t e d trace lowered ledger _
  exact ledger_has_literal_addresses ledger

end Yulang.GeneralDeclarativeI65.I72
