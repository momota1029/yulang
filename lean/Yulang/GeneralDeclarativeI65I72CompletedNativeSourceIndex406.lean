import Yulang.GeneralDeclarativeI65I72FiniteNativeK2406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open CommonRoleOutermostResolver (Summarizes Result)
open GeneralDeclarationPatterns (Pattern)

structure NativeInputAddress406 where
  occurrence : List Nat
  argumentOrdinal : Nat
  payloadPath : List Nat
  originalSourceOrdinal : Nat
  deriving DecidableEq

/-- The source-input premise can carry the literal ordinal supplied
by the actual originating typed occurrence, not an arbitrary matching
kind/name or a choice among equal endpoint denotations. This indexes
the stored authored *typed input* list, not a solver-release journal. -/
structure IndexedOriginalPath406 {s q row need} (front : UnaryHeadAt406 s q row need) where
  sourceOrdinal : Nat
  read : OriginalPathAt406 front
  atSource : s.core.origins[sourceOrdinal]? = some read.original

def IndexedOriginalPath406.address {s q row need} {front : UnaryHeadAt406 s q row need}
    (stored : IndexedOriginalPath406 front) : NativeInputAddress406 :=
  ⟨q.occurrence,0,[0],stored.sourceOrdinal⟩

/-- Once given the exact original source index, the stored original
is the only object consulted for the payload name. An incompatible
typed node does not mean a role rejection. -/
def readExplicitSourceIndex406 {s q row need}
    (front : UnaryHeadAt406 s q row need) (sourceOrdinal : Nat) (source : Origin)
    (indicated : s.core.origins[sourceOrdinal]? = some source)
    (route : OriginRoute s.core source front.gate.arg.center)
    (witness : ∀ name, literalUnaryPayloadName406 front.gate.key source.endpoint = some name →
      Bounds s.core.current.ordinary ⟨front.gate.lowerPayload,name,front.gate.upperPayload⟩) :
    Option (IndexedOriginalPath406 front) :=
  match atPath : literalUnaryPayloadName406 front.gate.key source.endpoint with
  | none => none
  | some name => some ⟨sourceOrdinal,
    ⟨source,List.mem_of_getElem? indicated,route,name,atPath,witness name atPath⟩,indicated⟩

theorem exact_source_index_readback406 {s q row need}
    (front : UnaryHeadAt406 s q row need) (k : Nat) (source : Origin)
    (stored : s.core.origins[k]? = some source) (route : OriginRoute s.core source front.gate.arg.center)
    (bounds : ∀ name, literalUnaryPayloadName406 front.gate.key source.endpoint = some name →
      Bounds s.core.current.ordinary ⟨front.gate.lowerPayload,name,front.gate.upperPayload⟩)
    {name : Nat} (literal : literalUnaryPayloadName406 front.gate.key source.endpoint = some name) :
    ∃ found : IndexedOriginalPath406 front,
      readExplicitSourceIndex406 front k source stored route bounds = some found ∧
        found.address = ⟨q.occurrence,0,[0],k⟩ ∧ found.read.name = name ∧
        found.read.original = source := by
  unfold readExplicitSourceIndex406
  split
  · rename_i miss
    rw [literal] at miss
    cases miss
  · rename_i observed hit
    have original : observed = name := Option.some.inj (hit.symm.trans literal)
    subst observed
    exact ⟨_,rfl,rfl,rfl,rfl⟩

theorem same_annotated_source_chooses_same_exact_center406 {s q row need}
    {front : UnaryHeadAt406 s q row need} (left right : IndexedOriginalPath406 front)
    (sameAddress : left.address = right.address) :
    left.read.original = right.read.original ∧ left.read.name = right.read.name ∧
      (unaryFrameAt406 front left.read).input = (unaryFrameAt406 front right.read).input := by
  have ordinal : left.sourceOrdinal = right.sourceOrdinal :=
    congrArg NativeInputAddress406.originalSourceOrdinal sameAddress
  have lhs := left.atSource
  rw [ordinal,right.atSource] at lhs
  have original := Option.some.inj lhs.symm
  have decoded := left.read.decoded
  rw [original,right.read.decoded] at decoded
  have name : left.read.name = right.read.name := Option.some.inj decoded.symm
  refine ⟨original,name,?_⟩
  unfold unaryFrameAt406 frameAtSource395
  rw [name]

/-- Having the checked gate/finite producer does not create a name
for an unrepresented original input. This proves only a missing
proof input in the current carrier, not a new role result. -/
theorem cannot_read_from_unrouted_original_source406 {s q row need}
    (front : UnaryHeadAt406 s q row need)
    (missing : ∀ original ∈ s.core.origins, ¬OriginRoute s.core original front.gate.arg.center) :
    ¬Nonempty (IndexedOriginalPath406 front) := by
  rintro ⟨read⟩
  exact missing read.read.original read.read.inSource read.read.routed

/-- Exact source-indexed positive consumer after arbitrary represented
finite completion. The root cannot choose another actual-name input
(and the producer occupies the literal previous ordinal). This
narrow receiver has no additional requested outputs or where edges. -/
theorem exact_original_index_drives_a_new_native_source406 {s producer d original q row}
    (before : FiniteNative406 s producer d original) (i : Fin producer.demand.outputs.length)
    (front : UnaryHeadAt406 s q row ⟨producer,d,i,original i⟩)
    (index : Nat) (stored : Origin) (address : s.core.origins[index]? = some stored)
    (routed : OriginRoute s.core stored front.gate.arg.center)
    (bounds : ∀ name, literalUnaryPayloadName406 front.gate.key stored.endpoint = some name →
      Bounds s.core.current.ordinary ⟨front.gate.lowerPayload,name,front.gate.upperPayload⟩)
    {given : Nat} (read : literalUnaryPayloadName406 front.gate.key stored.endpoint = some given)
    (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    ∃ (actual : IndexedOriginalPath406 front)
      (step : FiniteUnaryStep406 s q ⟨producer,d,i,original i⟩ []),
      readExplicitSourceIndex406 front index stored address routed bounds = some actual ∧
      actual.address = ⟨q.occurrence,0,[0],index⟩ ∧
      step.row = row ∧ HEq step.head front ∧ HEq step.actual actual.read ∧
      actual.read.name = given ∧
      ∃ ledger : FiniteNativeLedger406 s (FiniteNative406.advance before step (dChildren := []) .nil),
        ∀ m, Fits s m → ledger.Means m := by
  obtain ⟨actual,returned,atPath,name,_⟩ := exact_source_index_readback406 front index stored address routed bounds read
  have emptyOut : ∀ j : Fin q.demand.outputs.length, False := by
    intro j
    obtain ⟨k,impossible⟩ := j
    simp [noOutputs] at impossible
  have emptyKids : frameWhereKids400 (unaryFrameAt406 front actual.read) = [] := by
    simp [frameWhereKids400,AuthoredBodyFrame393.clauses,unaryFrameAt406,frameAtSource395,noWhere,children]
  let step : FiniteUnaryStep406 s q ⟨producer,d,i,original i⟩ [] :=
    ⟨row,front,actual.read,fun j => (emptyOut j).elim,fun j => (emptyOut j).elim,
      by simp [LiteralVariableWhere403,noWhere],emptyKids.symm ▸ .nil⟩
  exact ⟨actual,step,returned,atPath,rfl,HEq.rfl,HEq.rfl,name,
    (finite_completed_native_source_assembles_exact_ledger406
      (FiniteNative406.advance before step (dChildren := []) .nil)).2⟩

/-- The new positive case is not just a rewording of an authored
ModeWindow. When no lower Origin exists, this exact authored nominal
head is unavailable in the pre-C406 source head representation. -/
theorem completed_unary_gate_is_not_an_old_source_head406 {s q row need}
    (gate : CompletedUnaryGate406 s q row need)
    (noLower : ∀ o : Origin, o ∈ s.core.origins → ¬OriginRoute s.core o gate.arg.lower) :
    ¬Nonempty (SourceHead s.core q row) := by
  rintro ⟨head⟩
  cases head with
  | ordered cap all =>
    have atI : DeepHead s.core cap gate.arg (authoredUnaryPattern405 gate.key gate.binder) :=
      ordered_head_at all (i := 0) (by simp [gate.exactArg]) (by simp [gate.exactHead])
    cases atI with
    | ordinary view =>
      obtain ⟨_,_,translation,_⟩ := view
      obtain ⟨use,mode,_⟩ := original_typed_point_has_canonical_declared_mode404 need.expected.rhs gate.lowerTyped
      have unsupported := declared_application_not_ordinary (s := s.core) (ps := [.var gate.binder])
        (mode ▸ use.sourced)
      unfold authoredUnaryPattern405 at translation
      rw [unsupported] at translation
      cases translation
    | declared old _ =>
      exact noLower old.lower old.lowerAuthored old.lo
  | joined split =>
    have shape := (List.cons.inj (split.head.symm.trans gate.exactHead)).1
    have normal := split.normalized
    rw [shape] at normal
    change Pattern.app gate.key [.var gate.binder] = _ at normal
    cases normal

theorem actual_completed_native_selection_needs_the_new_head_carrier406 {s q trees d}
    (event : CompletedInvocation406 s q trees)
    (done : Summarizes (.selected event.row.id trees) (.selected d))
    (noLower : ∀ o : Origin, o ∈ s.core.origins → ¬OriginRoute s.core o event.chosen.gate.arg.lower) :
    ScopedClassifies406 s q (.selected d) ∧ ¬Classifies PriorSource406 s q (.selected d) := by
  refine ⟨completed_invocation_gives_source_verdict406 event done,?_⟩
  rintro ⟨t,_,⟨given⟩,summary⟩
  cases given with
  | rootK2 => cases summary
  | other kind _ _ _ => cases kind <;> cases summary
  | selected e _ _ _ _ =>
    have present := e.frame.inScope
    rw [event.chosen.gate.only] at present
    have shape := List.mem_singleton.mp present
    exact completed_unary_gate_is_not_an_old_source_head406 event.chosen.gate noLower
      ⟨shape ▸ e.head⟩

end Yulang.GeneralDeclarativeI65.I72
