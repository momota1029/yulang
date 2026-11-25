import Yulang.GeneralDeclarativeI65I74WhereListCoherence411

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Clause Declaration DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural literal_head)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open Core.PresenceGeneration (TyTerm)

def closedHead412 (box tick empty binder : Nat) : Pattern :=
  .record box (.record tick (.var binder) (.app empty [])) (.app empty [])

def closedWhere412 (box empty binder : Nat) : Pattern :=
  .record box (.var binder) (.app empty [])

def recordInput412 (box site : Nat) : CommonRecursiveNominalIntervals.Endpoint Nat :=
  .ordinary (.record box (.var site) .emptyRecord)

def recordRow412 (root field site : Nat) : GeneralDeclarativeHead320.Equation :=
  ⟨root,.record field (.variable site) (.primitive .emptyRecord [])⟩

def query412 (box tick binder : Nat) : Expr :=
  .record box (.record tick (.variable binder) (.primitive .emptyRecord [])) (.primitive .emptyRecord [])

/-- The cursor belongs to the original candidate and actual field. The
independently observed point authorizes opening the outer record; the
raw row merely gives the exact logical operand, never its completion. -/
structure ActualRecordField (s : I72.State) (q : I72.Request) (d : Declaration) where
  only : visible s.core q = [d]
  role : ∃ row ∈ s.core.current.environment.source.roles.rows, row.role = q.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid s.core.current.environment.source.roles
  checked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles d
  input : Capture
  asked : q.demand.arguments = [input]
  noOutputs : q.demand.outputs = []
  box : Nat
  tick : Nat
  empty : Nat
  binder : Nat
  head : d.head = [closedHead412 box tick empty binder]
  clause : Clause
  clauseAt : d.requirements = [clause]
  clauseRole : clause.role = q.demand.role
  clauseArgs : clause.arguments = [closedWhere412 box empty binder]
  clauseOutputs : clause.outputs = []
  translated : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot)
    (normalize (closedHead412 box tick empty binder)) = some (query412 box tick binder)
  origin : Origin
  original : origin ∈ s.core.origins
  originLower : origin.slot = input.lower
  originCenter : origin.slot = input.center
  originUpper : origin.slot = input.upper
  site : Nat
  endpoint : origin.endpoint = recordInput412 box site
  ordinaryRow : recordRow412 input.lower box site ∈ s.core.current.ordinary.equations

theorem actual_record_field_is_entered412 {s q d} (a : ActualRecordField s q d) :
    Visit (structural s.core.current.ordinary) a.input.lower
      (query412 a.box a.tick a.binder) a.site := by
  have actual := literal_head a.ordinaryRow
    (show GeneralDeclarativeGraphRows321.shapeOf (recordRow412 a.input.lower a.box a.site).right =
      some (.record [(a.box,a.site)]) from rfl)
  unfold query412
  refine .field (query := .record a.tick (.variable a.binder) (.primitive .emptyRecord [])) actual List.mem_cons_self ?_ (.here .record)
  exact List.mem_cons_self

theorem actual_record_field_K2_on_unfiltered_graph412 {s q d} (a : ActualRecordField s q d)
    (cycle : AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) a.site) :
    PatternK2 s.core.current.ordinary a.input.lower (query412 a.box a.tick a.binder) :=
  ⟨a.site,actual_record_field_is_entered412 a,cycle⟩

structure RecordRejection (s : I72.State) (q : I72.Request) where
  decl : Declaration
  field : ActualRecordField s q decl
  cycle : AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) field.site

/-- The new local rule is a head-inspection diagnostic only. It cannot
generate a child demand, a chosen dictionary, or output receipts. -/
def recordLocal412 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q verdict needs => needs = [] ∧ verdict = .rejected ∧ Nonempty (RecordRejection s q)

def R4 : SourcePrimitives where
  elected := WhereCycle411.R3.elected
  other := fun s q v needs => WhereCycle411.R3.other s q v needs ∨ recordLocal412.other s q v needs

theorem dictionary_sound_R4 : DictionarySound R4 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 R4 := fun s q event needs _ localRule _ =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 R4 := fun s q event needs localRule =>
    (WhereCycle411.R3_local_evidence411 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)

theorem actual_field_not_emitted_where412 {s q} (rejected : RecordRejection s q)
    (rootSafe : ¬RootCycle s q) :
    Nonempty (SourceTrace R4 s q .rejected none) :=
  ⟨.other .rejected rootSafe (.inr ⟨rfl,rfl,⟨rejected⟩⟩) .nil⟩

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
