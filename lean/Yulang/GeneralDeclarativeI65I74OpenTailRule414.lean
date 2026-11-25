import Yulang.GeneralDeclarativeI65I74MixedRecordReplayOrder413
import Yulang.GeneralDeclarativeI65I74MixedRecordConservative413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralSourceMetadataRows291 (interpretation)

def openTerm (label field tail : Nat) : CommonRecursiveNominalIntervals.Endpoint Nat :=
  .ordinary (.record label (.var field) (.var tail))

def openRow (root label field tail : Nat) : Equation :=
  ⟨root,.record label (.variable field) (.variable tail)⟩

def intRow (field : Nat) : Equation := ⟨field,.primitive (.scalar .int) []⟩

def openHead (label intName binder : Nat) : Pattern :=
  .record label (.app intName []) (.var binder)

def tailRequirement (role binder clause : Nat) : Clause := ⟨clause,role,[.var binder],[]⟩

/-- Exact restricted source state for X4, not an unsuccessful attempt
to find a match. The tail is an original variable, not an empty row. -/
structure OpenInput (s : I72.State) (q : I72.Request) where
  root : Nat
  label : Nat
  field : Nat
  tail : Nat
  args : q.demand.arguments = [point root]
  noOutputs : q.demand.outputs = []
  rootField : root ≠ field
  rootTail : root ≠ tail
  fieldTail : field ≠ tail
  origin : Origin
  original : origin ∈ s.core.origins
  originSlot : origin.slot = root
  literal : origin.endpoint = openTerm label field tail
  noTailOrigin : ∀ o ∈ s.core.origins, o.slot ≠ tail
  exactRows : s.core.current.ordinary.equations = [openRow root label field tail,intRow field]
  noAtoms : s.core.current.ordinary.normal.ordinary = []
  noBounds : s.core.current.ordinary.normal.intervals = []
  noNative : s.core.current.visible = []
  noRoute : s.core.routes = []

structure OpenCandidate {s q} (input : OpenInput s q) where
  decl : Declaration
  exactVisible : visible s.core q = [decl]
  intName : Nat
  binder : Nat
  clause : Nat
  head : decl.head = [openHead input.label intName binder]
  requirements : decl.requirements = [tailRequirement q.demand.role binder clause]
  associated : decl.associated = []
  noOutputBinders : decl.outputBinders = []
  covered : GeneralDeclarativeWitnessModeCoverage357.DeclarationCovered s.core.current.environment decl
  header : RecordK2412.header412 s.core.current decl = true
  actualInt : application (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) intName [] =
      some (.primitive (.scalar .int) [])

structure OpenTailPending (s : I72.State) (q : I72.Request) where
  input : OpenInput s q
  candidate : OpenCandidate input

theorem no_row_for_actual_tail414 {s q} (a : OpenInput s q) :
    ∀ e ∈ s.core.current.ordinary.equations, e.left ≠ a.tail := by
  intro row belongs
  rw [a.exactRows] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with h|h
  · rw [h]; exact a.rootTail
  · rw [h]; exact a.fieldTail

def openTailLocal414 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs => needs = [] ∧ v = .pending ∧ Nonempty (OpenTailPending s q)

def R6 : SourcePrimitives where
  elected := MixedRecord413.R5.elected
  other := fun s q v needs => MixedRecord413.R5.other s q v needs ∨ openTailLocal414.other s q v needs

theorem dictionary_sound_R6 : DictionarySound R6 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 R6 := fun s q event needs _ localRule _ =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 R6 := fun s q event needs localRule =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
