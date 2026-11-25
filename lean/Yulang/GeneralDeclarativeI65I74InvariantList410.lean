import Yulang.GeneralDeclarativeI65I74NamedCompatibility409
import Yulang.GeneralDeclarativeI65I74RootEscape410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.List410
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names visited Legal)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open CommonDeclaredNominalInspection (Parameter)
open CommonRoleOutermostResolver (All₂)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)

/-- X8's captured variable is in the declared invariant value slot
of one actual nominal source. None of the supplied keys is an answer
or an inspection of the possible cyclic payload. -/
def invariantValue410 : Parameter := ⟨.value,.invariant⟩

def listPoint410 (key payload : Nat) : Endpoint Nat :=
  .nominal key [.inl (.point (.ordinary (.var payload)))]

structure InvariantListHead (s : I72.State) (q : I72.Request) (d : Declaration) where
  only : visible s.core q = [d]
  authoredRole : ∃ row ∈ s.core.current.environment.source.roles.rows, row.role = q.demand.role
  validRoles : GeneralSourceMetadataRoles291.Valid s.core.current.environment.source.roles
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles d
  covered : DeclarationCovered s.core.current.environment d
  arg : Capture
  asked : q.demand.arguments = [arg]
  key : Nat
  binder : Nat
  named : d.head = [.app key [.var binder]]
  origin : Origin
  authored : origin ∈ s.core.origins
  lower : origin.slot = arg.lower
  center : origin.slot = arg.center
  upper : origin.slot = arg.upper
  payload : Nat
  endpoint : origin.endpoint = listPoint410 key payload
  use : Use s.core.current.environment key 1
  mode : names use.mode 1 = some [invariantValue410]
  table : s.core.modes[key]? = some [invariantValue410]
  atom : Atom.tyLe (.var payload) (.var payload) ∈ s.core.current.ordinary.normal.ordinary
  noWhere : d.requirements = []
  noOutputs : q.demand.outputs = []

def InvariantListHead.capture {s q d} (a : InvariantListHead s q d) (n : Nat) : Capture :=
  if n = a.binder then point a.payload else emptyCapture403

theorem InvariantListHead.payloadBound {s q d} (a : InvariantListHead s q d) :
    ValueBind s.core (a.capture a.binder) (.var a.payload) (.var a.payload) := by
  have resolved : a.capture a.binder = point a.payload := by simp [InvariantListHead.capture]
  rw [resolved]
  exact ⟨a.atom,a.atom,a.atom,a.atom⟩

theorem InvariantListHead.endpointWellFormed {s q d} (a : InvariantListHead s q d) :
    ContextWellFormed s.core.modes false (listPoint410 a.key a.payload) :=
  .nominal a.table (.cons (.valuePoint (.ordinary true (.var a.payload))) (.nil false))

def InvariantListHead.compare {s q d} (a : InvariantListHead s q d) :
    DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes false
      (listPoint410 a.key a.payload) (listPoint410 a.key a.payload) where
  actualSource := by
    intro site seen
    have same : site = (a.key,1) := by
      simpa [listPoint410,visited.eq_def,
        GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] using seen
    subst site
    exact ⟨a.use,[invariantValue410],a.mode,a.table⟩
  left := a.endpointWellFormed
  right := a.endpointWellFormed
  compared := .nominal a.table (.cons (.invariantValue
    (.ordinary a.atom) (.ordinary a.atom) (.ordinary a.atom) (.ordinary a.atom)) .nil)

def InvariantListHead.window {s q d} (a : InvariantListHead s q d) :
    ModeWindow s.core a.arg (.app a.key [.var a.binder]) :=
  ⟨a.origin,a.origin,a.lower ▸ .direct,a.upper ▸ .direct,a.authored,a.authored,
    a.key,[.var a.binder],rfl,_,_,a.endpoint,a.endpoint,by rw [a.endpoint]; exact a.compare⟩

def InvariantListHead.head {s q d} (a : InvariantListHead s q d) : SourceHead s.core q d := by
  let binding := Binding.value a.binder (.var a.payload) (.var a.payload)
  refine .ordered a.capture ?_
  rw [a.asked,a.named]
  refine .cons (.declared (found := [binding,binding]) a.window ?_) .nil
  change DeepRead s.core a.capture false (.app a.key [.var a.binder])
    a.origin.endpoint a.origin.endpoint [binding,binding]
  rw [a.endpoint]
  refine .nominal a.use a.mode a.table ?_
  let p : Endpoint Nat := .ordinary (.var a.payload)
  let span : CommonRecursiveNominalIntervals.Bounds (Endpoint Nat) := .point p
  have single : DeepRead s.core a.capture true (.var a.binder) p p [binding] :=
    .bind a.payloadBound
  have doubled : DeepArgument s.core a.capture true invariantValue410 (.var a.binder)
      (.inl span) (.inl span) ([binding] ++ [binding]) :=
    .invariantValue (a := span) (b := span) single single
  have parts : DeepArguments s.core a.capture false [invariantValue410] [.var a.binder]
      [.inl span] [.inl span] (([binding] ++ [binding]) ++ []) :=
    .cons doubled .nil
  exact parts

def InvariantListHead.candidate {s q d} (a : InvariantListHead s q d) : AuthoredCandidate s.core q d :=
  let mem : d ∈ visible s.core q := by simp [a.only]
  ⟨mem,a.covered,a.checked.signature,a.head⟩

def InvariantListHead.tape {s q d} (a : InvariantListHead s q d) :
    CandidateTape s.core q (visible s.core q) :=
  a.only.symm ▸ .next (.matched a.candidate) .nil

theorem invariant_list_selected_without_visit410 {s q d} (a : InvariantListHead s q d)
    (safe : ¬ RootCycle s q) : TapedMatch s.core q a.tape d := by
  have yes : ∀ rows (shape : rows = [d]),
      let t : CandidateTape s.core q rows := shape.symm ▸ .next (.matched a.candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows eq; cases eq; exact ⟨rfl,rfl⟩
  exact ⟨safe,(yes _ a.only).1,(yes _ a.only).2⟩

theorem literal_binder_has_no_structural_payload_visit410 {s q d} (a : InvariantListHead s q d) :
    ∀ (view : GeneralDeclarativeK2Graph321.View) (inspect : Nat),
      ¬GeneralDeclarativeInspect321.Visit view a.payload (.variable a.binder) inspect :=
  fun _ _ => GeneralDeclarativeInspect321.variable_has_no_visit

structure InvariantListRead {s q} (e : Event s q) where
  test : InvariantListHead s q e.frame.decl
  head : e.head = test.head
  input : e.frame.input = preoutputInputOfHead399 e.head (fun _ => emptyCapture403)

/-- Independent local rule for a single literal invariant list binder with
an actual authored point. The verdict does not depend on the availability
of a colouring or on the result of executing any checker. -/
def listLocal410 : SourcePrimitives where
  elected := fun _ _ event needs => needs = [] ∧ Nonempty (InvariantListRead event)
  other := fun _ _ _ _ => False

theorem list_local_evidence410 : LocalEvidence407 listLocal410 := by
  intro s q e needs yes
  obtain ⟨w⟩ := yes.2
  refine ⟨node_from_exact_preoutput_head405 e w.test.checked (fun _ => emptyCapture403) w.input, .inl ?_⟩
  intro i
  have notPossible := i.isLt
  simp [w.test.noOutputs] at notPossible

def R2 : SourcePrimitives where
  elected := fun s q e needs => Named409.R1.elected s q e needs ∨ listLocal410.elected s q e needs
  other := Named409.R1.other

theorem R2_local_evidence410 : LocalEvidence407 R2 := by
  intro s q event needs rule
  exact rule.elim (Named409.R1_local_evidence409 s q event needs)
    (list_local_evidence410 s q event needs)

theorem dictionary_sound_R2 : DictionarySound R2 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 R2 := fun s q event needs _ localRule _ =>
    (R2_local_evidence410 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 R2 := fun s q event needs localRule =>
    (R2_local_evidence410 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)

end Yulang.GeneralDeclarativeI65.I72.List410
