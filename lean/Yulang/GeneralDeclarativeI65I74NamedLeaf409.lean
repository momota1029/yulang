import Yulang.GeneralDeclarativeI65I73UnifiedEntry408
import Yulang.GeneralDeclarativeWitnessRank350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Named409
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names visited Legal)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open CommonRoleOutermostResolver (All₂)

structure NamedHead (s : I72.State) (q : I72.Request) (d : Declaration) where
  only : visible s.core q = [d]
  authoredRole : ∃ row ∈ s.core.current.environment.source.roles.rows, row.role = q.demand.role
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles d
  covered : DeclarationCovered s.core.current.environment d
  arg : Capture
  asked : q.demand.arguments = [arg]
  key : Nat
  named : d.head = [.app key []]
  origin : Origin
  authored : origin ∈ s.core.origins
  lo : origin.slot = arg.lower
  hi : origin.slot = arg.upper
  endpoint : origin.endpoint = .nominal key []
  use : Use s.core.current.environment key 0
  mode : names use.mode 0 = some []
  table : s.core.modes[key]? = some []
  noWhere : d.requirements = []
  noOutputs : q.demand.outputs = []

theorem NamedHead.endpointWellFormed {s q d} (a : NamedHead s q d) :
    ContextWellFormed s.core.modes false (Endpoint.nominal a.key [] : Endpoint Nat) :=
  .nominal a.table (.nil false)

def NamedHead.compare {s q d} (a : NamedHead s q d) :
    DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes false
      (.nominal a.key []) (.nominal a.key []) where
  actualSource := by
    intro site seen
    have same : site = (a.key,0) := by
      simpa [visited.eq_def,GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] using seen
    subst site
    exact ⟨a.use,[],a.mode,a.table⟩
  left := a.endpointWellFormed
  right := a.endpointWellFormed
  compared := .nominal a.table .nil

def NamedHead.window {s q d} (a : NamedHead s q d) :
    ModeWindow s.core a.arg (.app a.key []) :=
  ⟨a.origin,a.origin,a.lo ▸ .direct,a.hi ▸ .direct,a.authored,a.authored,
    a.key,[],rfl,[],[],a.endpoint,a.endpoint,by rw [a.endpoint]; exact a.compare⟩

def NamedHead.head {s q d} (a : NamedHead s q d) : SourceHead s.core q d := by
  refine .ordered (fun _ => emptyCapture403) ?_
  rw [a.asked,a.named]
  refine .cons (.declared (found := []) a.window ?_) .nil
  change DeepRead s.core (fun _ => emptyCapture403) false (.app a.key [])
    a.origin.endpoint a.origin.endpoint []
  rw [a.endpoint]
  exact .nominal a.use a.mode a.table .nil

def NamedHead.candidate {s q d} (a : NamedHead s q d) : AuthoredCandidate s.core q d :=
  let mem : d ∈ visible s.core q := by simp [a.only]
  ⟨mem,a.covered,a.checked.signature,a.head⟩

def NamedHead.tape {s q d} (a : NamedHead s q d) : CandidateTape s.core q (visible s.core q) :=
  a.only.symm ▸ .next (.matched a.candidate) .nil

theorem named_sole_selected_without_opening409 {s q d} (a : NamedHead s q d)
    (safe : ¬ RootCycle s q) : TapedMatch s.core q a.tape d := by
  have yes : ∀ rows (shape : rows = [d]),
      let t : CandidateTape s.core q rows := shape.symm ▸ .next (.matched a.candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows eq; cases eq; exact ⟨rfl,rfl⟩
  exact ⟨safe,(yes _ a.only).1,(yes _ a.only).2⟩

structure NamedRead {s q} (e : Event s q) where
  test : NamedHead s q e.frame.decl
  head : e.head = test.head
  input : e.frame.input = preoutputInputOfHead399 e.head (fun _ => emptyCapture403)

/-- Declarative rule on the original source. The bare, zero-parameter written
name and original authored endpoint are recognized without unfolding a
recursive body. There is no Bool checker or desired report in this rule. -/
def namedLocal409 : SourcePrimitives where
  elected := fun _ _ event needs => needs = [] ∧ Nonempty (NamedRead event)
  other := fun _ _ _ _ => False

theorem named_local_evidence409 : LocalEvidence407 namedLocal409 := by
  intro s q e needs yes
  obtain ⟨w⟩ := yes.2
  refine ⟨node_from_exact_preoutput_head405 e w.test.checked (fun _ => emptyCapture403) w.input, .inl ?_⟩
  intro i
  have notPossible := i.isLt
  simp [w.test.noOutputs] at notPossible

def R1 : SourcePrimitives where
  elected := fun s q e needs => R0.elected s q e needs ∨ namedLocal409.elected s q e needs
  other := R0.other

theorem R1_local_evidence409 : LocalEvidence407 R1 := by
  intro s q event needs rule
  exact rule.elim (R0_elected_has_local_evidence407 s q event needs)
    (named_local_evidence409 s q event needs)

theorem dictionary_sound_R1 : DictionarySound R1 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 R1 := fun s q event needs _ localRule _ =>
    (R1_local_evidence409 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 R1 := fun s q event needs localRule =>
    (R1_local_evidence409 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)

/-- The named head was genuinely absent from the positive rule union:
it is neither variable-only nor a unary native payload pattern. -/
theorem new_named_leaf_is_not_old_election409 {s q} {e : Event s q}
    (new : NamedRead e) {needs} : ¬R0.elected s q e needs := by
  intro old
  rcases R0_selection_uses_independent_original_rule407 e old with ordinary | native
  · have inScope : e.frame.decl ∈ visible s.core q := by simp [new.test.only]
    have atHead : Pattern.app new.test.key [] ∈ e.frame.decl.head := by simp [new.test.named]
    obtain ⟨_,incompatible,_⟩ := ordinary.2 _ inScope _ atHead
    cases incompatible
  · obtain ⟨native⟩ := native
    have eq := native.test.writtenHead.symm.trans new.test.named
    have same := (List.cons.inj eq).1
    have arity := congrArg List.length (Pattern.app.inj same).2
    cases arity

end Yulang.GeneralDeclarativeI65.I72.Named409
