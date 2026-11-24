import Yulang.GeneralDeclarativeI65B6WhereComposition398
import Yulang.GeneralDeclarativeI65AddressedReplay390

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body)

/-- Read the stored event tree at an ordinal. A child with zero
outputs is still present; output lists are not used to find it. -/
def LiteralEventForest.at399 {s : State} :
    LiteralEventForest (s := s) → Nat → Option (LiteralEventTree (s := s))
  | .nil, _ => none
  | .cons event _, 0 => some event
  | .cons _ tail, i+1 => tail.at399 i

/-- The exact event and selected dictionary are read together from
one independent addressed finite derivation. This does not lift a
bare diagnostic tree into an event-bearing rule. -/
theorem addressed_child_event_at399 [judgment : ReplayJudgment]
    {s : State} {qs ds events}
    (forest : AddressedDictionaryForest (judgment := judgment) s qs ds events)
    (i : Nat) {child : Request} (requestAt : qs[i]? = some child) :
    ∃ (event : LiteralLocalEvent s child) (ds0 : List Dictionary)
      (tail : LiteralEventForest (s := s)),
      events.at399 i = some (.node ⟨child,event⟩ tail) ∧
      ds[i]? = some (.node event.declaration.id ds0) ∧
      LiteralTraceRule judgment s child (.selected event.declaration.id event.kids) ⟨child,event⟩ ∧
      AddressedDictionaryForest (judgment := judgment) s event.kids ds0 tail := by
  induction i generalizing qs ds events child with
  | zero =>
    cases forest with
    | nil => simp at requestAt
    | cons root next =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at requestAt
      subst child
      cases root with
      | node event guard lower =>
        exact ⟨event,_,_,rfl,rfl,guard,lower⟩
  | succ i ih =>
    cases forest with
    | nil => simp at requestAt
    | cons root next =>
      obtain ⟨event,dicts,tail,loc,chosen,guard,children⟩ :=
        ih next (by simpa using requestAt)
      exact ⟨event,dicts,tail,loc,chosen,guard,children⟩

/-- Read the exact authored child at the source where clause ordinal,
not a visible frame guessed by request equality. -/
theorem original_where_selected_event399 [judgment : ReplayJudgment]
    {s q f binder body ds events}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events) :
    ∃ (event : LiteralLocalEvent s origin.child) (ds0 : List Dictionary)
      (tail : LiteralEventForest (s := s)),
      events.at399 origin.clauseOrdinal = some (.node ⟨origin.child,event⟩ tail) ∧
      ds[origin.clauseOrdinal]? = some (.node event.declaration.id ds0) ∧
      LiteralTraceRule judgment s origin.child
        (.selected event.declaration.id event.kids) ⟨origin.child,event⟩ ∧
      AddressedDictionaryForest (judgment := judgment) s event.kids ds0 tail :=
  addressed_child_event_at399 forest origin.clauseOrdinal origin.child_position

/-- Captures and the ordered where ledger are not functions merely of
a syntactic dictionary ID. This relation is only the precise agreement
of two retained pre-output views of the source, not a selection rule. -/
structure SamePreoutputFrame399 {s q} (event : LiteralLocalEvent s q)
    (f : AuthoredBodyFrame393 s q) : Prop where
  sameOrdinal : f.ordinal = event.declarationOrdinal
  sameCaptures : f.captures = event.captures
  sameWhere : f.clauses = event.whereEntries

theorem same_preoutput_declaration399 {s q event f}
    (same : SamePreoutputFrame399 (s := s) (q := q) event f) :
    f.decl = event.declaration := by
  have read := f.authored
  rw [same.sameOrdinal,event.declaredAt] at read
  exact (Option.some.inj read).symm

theorem same_preoutput_slots399 {s q event f}
    (same : SamePreoutputFrame399 (s := s) (q := q) event f)
    (body : Body) : f.slots body = writtenBodySlot392 event body := by
  funext n
  cases body with
  | explicit e =>
    simp only [AuthoredBodyFrame393.slots,writtenBodySlot392,same.sameCaptures]
  | default role name rhs => rfl

theorem same_preoutput_children399 {s q event f}
    (same : SamePreoutputFrame399 (s := s) (q := q) event f) :
    children q (f.clauses.map LiteralWhereEntry.demand) = event.kids := by
  simp only [same.sameWhere,LiteralLocalEvent.kids]

/-- The role resolver's selected declaration ID recovers the
original raw ordinal only when the authored catalogue has unique
declaration IDs. Captures and child entries are not recovered here. -/
theorem exact_frame_ordinal_of_same_selected_id399 {s q}
    (event : LiteralLocalEvent s q) (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (sameKey : f.decl.id = event.declaration.id) :
    f.ordinal = event.declarationOrdinal := by
  let ids := (authoredRegistry s.current).declarations.map Declaration.id
  have fId : ids[f.ordinal]? = some f.decl.id := by
    simp [ids,List.getElem?_map,f.authored]
  have eventId : ids[event.declarationOrdinal]? = some event.declaration.id := by
    simp [ids,List.getElem?_map,event.declaredAt]
  obtain ⟨fi,readF⟩ := List.getElem?_eq_some_iff.mp fId
  obtain ⟨ei,readE⟩ := List.getElem?_eq_some_iff.mp eventId
  exact (checked.1.getElem_inj (hi := fi) (hj := ei)).mp (readF.trans (sameKey.trans readE.symm))

theorem ordinal_capture_where_eq_make_same_preoutput399 {s q}
    (event : LiteralLocalEvent s q) (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (sameKey : f.decl.id = event.declaration.id)
    (sameCaptures : f.captures = event.captures)
    (sameChildren : f.clauses = event.whereEntries) :
    SamePreoutputFrame399 event f :=
  ⟨exact_frame_ordinal_of_same_selected_id399 event f checked sameKey,sameCaptures,sameChildren⟩


open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Supplies lookup lookup_exact)
open GeneralDeclarations (Equation)

/-- No output receipt from the retained event is used to calculate
this RHS. The authoritative inputs are the selected declaration, the
actual capture table, the original demand and the B6 symbolic plan. -/
structure EventLogicalOutput399 {s q} (event : LiteralLocalEvent s q)
    (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name body
  rhs : ExactRoleRhs398 (normalize (bodyPattern body))

def EventLogicalOutput399.equation {s q ev i}
    (result : EventLogicalOutput399 (s := s) (q := q) ev i) : CompoundEquation394 :=
  ⟨q.occurrence,i.val,q.demand.outputs[i],result.body,result.rhs.val⟩

def logicalOutputOfEvent399 {s q} (event : LiteralLocalEvent s q)
    (atlas : B6SymbolicAtlas398 s) (i : Fin q.demand.outputs.length)
    (unique : (event.declaration.associated.map Equation.name).Nodup) :
    Option (EventLogicalOutput399 event i) :=
  let roles := (authoredRegistry s.current).roles
  let request := q.demand.outputs[i]
  match looked : lookup roles event.declaration request.name with
  | none => none
  | some body => do
    let plan ← atlas.read event.declarationOrdinal body
    let rhs ← instantiateB6Value398 (writtenBodySlot392 event body) plan
    pure ⟨body,(lookup_exact roles event.declaration unique request.name body).mp looked,rhs⟩

theorem exact_event_output_at399 {s q} {event : LiteralLocalEvent s q}
    {i : Fin q.demand.outputs.length} (out : EventLogicalOutput399 event i) :
    out.equation.occurrence = q.occurrence ∧
    out.equation.ordinal = i.val ∧
    q.demand.outputs[i.val]? = some out.equation.requested ∧
    out.equation.requested.target = q.demand.outputs[i].target ∧
    Supplies (authoredRegistry s.current).roles event.declaration
      out.equation.requested.name out.equation.originalBody :=
  ⟨rfl,rfl,List.getElem?_eq_getElem i.isLt,rfl,out.supplied⟩

/-- The B6 annotation belongs to the actual supplier read from the
event's declaration. Source meaning is C394, never a guessed literal
mixed wire. Only the named independent B6 data are conditional. -/
theorem event_B6_source_produces_logical_rhs399 {s q} (event : LiteralLocalEvent s q)
    (atlas : B6SymbolicAtlas398 s) (i : Fin q.demand.outputs.length)
    (unique : (event.declaration.associated.map Equation.name).Nodup)
    {body : Body}
    (supplied : Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name body)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern body))}
    (typed : atlas.read event.declarationOrdinal body = some plan)
    (compatible : B6UsesFit398 s (writtenBodySlot392 event body) plan.needs) :
    ∃ out : EventLogicalOutput399 event i, logicalOutputOfEvent399 event atlas i unique = some out ∧
      out.body = body ∧
      CompoundSourceRhs394 s (writtenBodySlot392 event body) false
        (normalize (bodyPattern body)) out.equation.rhs := by
  obtain ⟨rhs,replayed,meaning⟩ := symbolic_replay_meaning_with_supplied_capture_kinds398 plan compatible
  let result : EventLogicalOutput399 event i := ⟨body,supplied,rhs⟩
  refine ⟨result,?_,rfl,meaning⟩
  have hit : lookup (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name =
      some body := (lookup_exact _ _ unique _ _).mpr supplied
  unfold logicalOutputOfEvent399
  dsimp only
  split
  next notFound => rw [hit] at notFound; contradiction
  next found read =>
    rw [hit] at read
    injection read with eqBody
    subst found
    simp [typed,replayed,result]

/-- The chosen retained event's exact declaration/captures/where list
agree with the B4 frame that will receive the independent plan. The
proof indexes this very event; it doesn't reconstruct it from the key. -/
theorem B6_frame_replay_has_same_retained_event_meaning399 {s q}
    (event : LiteralLocalEvent s q) (f : AuthoredBodyFrame393 s q)
    (same : SamePreoutputFrame399 event f)
    (atlas : B6SymbolicAtlas398 s) (i : Fin q.demand.outputs.length)
    (unique : (f.decl.associated.map Equation.name).Nodup)
    {body : Body}
    (supplied : Supplies (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name body)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern body))}
    (typed : atlas.read event.declarationOrdinal body = some plan)
    (compatible : B6UsesFit398 s (writtenBodySlot392 event body) plan.needs) :
    ∃ (frameOut : LogicalRoleOutput398 f i) (eventOut : EventLogicalOutput399 event i),
      logicalOutputAt398 f atlas i unique = some frameOut ∧
      (∃ check : (event.declaration.associated.map Equation.name).Nodup,
        logicalOutputOfEvent399 event atlas i check = some eventOut) ∧
      frameOut.equation = eventOut.equation ∧
      CompoundSourceRhs394 s (writtenBodySlot392 event body) false
        (normalize (bodyPattern body)) eventOut.equation.rhs := by
  have rows := same_preoutput_declaration399 same
  have slots := same_preoutput_slots399 same body
  have checked : (event.declaration.associated.map Equation.name).Nodup := rows ▸ unique
  have framed : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body := rows ▸ supplied
  obtain ⟨rhs,replayed,meaning⟩ := symbolic_replay_meaning_with_supplied_capture_kinds398 plan compatible
  have typedFrame : atlas.read f.ordinal body = some plan := same.sameOrdinal ▸ typed
  have replayFrame : instantiateB6Value398 (f.slots body) plan = some rhs := slots ▸ replayed
  let frameOut : LogicalRoleOutput398 f i := ⟨body,framed,rhs⟩
  let eventOut : EventLogicalOutput399 event i := ⟨body,supplied,rhs⟩
  have frameExact : logicalOutputAt398 f atlas i unique = some frameOut := by
    have hit : lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some body :=
      (lookup_exact _ _ unique _ _).mpr framed
    unfold logicalOutputAt398
    dsimp only
    split
    next notFound => rw [hit] at notFound; contradiction
    next found read =>
      rw [hit] at read
      injection read with eqBody
      subst found
      simp [typedFrame,replayFrame,frameOut]
  have eventExact : logicalOutputOfEvent399 event atlas i checked = some eventOut := by
    have hit : lookup (authoredRegistry s.current).roles event.declaration q.demand.outputs[i].name = some body :=
      (lookup_exact _ _ checked _ _).mpr supplied
    unfold logicalOutputOfEvent399
    dsimp only
    split
    next notFound => rw [hit] at notFound; contradiction
    next found read =>
      rw [hit] at read
      injection read with eqBody
      subst found
      simp [typed,replayed,eventOut]
  exact ⟨frameOut,eventOut,frameExact,⟨checked,eventExact⟩,rfl,meaning⟩


/-- Literal where entries only contain the original parent clause and
its role. This reads the original clause list, not the compiled RHS. -/
theorem original_where_entry_role399 {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body) :
    origin.entry.clause ∈ f.decl.requirements ∧
      origin.child.demand.role = origin.entry.clause.role := by
  change origin.entry.clause ∈ f.decl.requirements ∧ origin.entry.demand.role = origin.entry.clause.role
  have entry := origin.atClause
  unfold AuthoredBodyFrame393.clauses at entry
  rw [List.getElem?_map] at entry
  cases old : f.decl.requirements[origin.clauseOrdinal]? with
  | none => simp [old] at entry
  | some clause =>
    simp only [old,Option.map_some,Option.some.injEq] at entry
    rw [← entry]
    exact ⟨List.mem_of_getElem? old,rfl⟩

/-- Ordinary role coverage supplies an authored body for the original
requested associated name at the selected child. This uses the original
parent clause and checked child signature, not an existing child write,
an output payload, or B6 coverage. -/
theorem selected_where_supplier_exists399 {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (event : LiteralLocalEvent s origin.child)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current)) :
    ∃ source, Supplies (authoredRegistry s.current).roles event.declaration
      origin.child.demand.outputs[origin.outputIndex].name source := by
  let registry := authoredRegistry s.current
  have chosen := checked.2 event.declaration (List.mem_of_getElem? event.declaredAt)
  have parent := checked.2 f.decl (List.mem_of_getElem? f.authored)
  obtain ⟨clause,sourceRole⟩ := original_where_entry_role399 origin
  have written := List.mem_of_getElem? origin.atEquation
  obtain ⟨v,declared⟩ := (parent.signature.2.2.2 origin.entry.clause clause).2 origin.equation written
  have roleEq := (visible_exact s origin.child event.declaration).mp event.inScope |>.2
  have requested : origin.child.demand.outputs[origin.outputIndex] = origin.output :=
    (List.getElem?_eq_some_iff.mp origin.outputAt).2
  have known : ∃ v, (registry.roles event.declaration.role).assoc
      origin.child.demand.outputs[origin.outputIndex].name = some v := by
    refine ⟨v,?_⟩
    rw [roleEq,sourceRole,requested,origin.outputName]
    exact declared
  exact GeneralDictionaryAssociatedProvenance.declared_covered registry.roles
    event.declaration chosen.signature _ known

/-- In an already independently guarded and addressed finite child
derivation, B4 finds the actual selected child event and its actual
checked supplier. Only B6's plan/slot kind input is passed in, for
that event and that supplier. Event slots determine the replay
directly, not a second visible frame for the same request. -/
theorem selected_where_B6_produces_from_actual_event399 [judgment : ReplayJudgment]
    {s q f binder body ds events}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6SymbolicAtlas398 s)
    (b6 : ∀ (event : LiteralLocalEvent s origin.child),
      LiteralTraceRule judgment s origin.child
        (.selected event.declaration.id event.kids) ⟨origin.child,event⟩ →
      ∀ (source : Body), Supplies (authoredRegistry s.current).roles event.declaration
        origin.child.demand.outputs[origin.outputIndex].name source →
      ∃ plan : B6ValuePlan398 s false (normalize (bodyPattern source)),
        atlas.read event.declarationOrdinal source = some plan ∧
        B6UsesFit398 s (writtenBodySlot392 event source) plan.needs) :
    ∃ (event : LiteralLocalEvent s origin.child) (ds0 : List Dictionary)
      (tail : LiteralEventForest (s := s)) (out : EventLogicalOutput399 event origin.outputIndex),
      events.at399 origin.clauseOrdinal = some (.node ⟨origin.child,event⟩ tail) ∧
      ds[origin.clauseOrdinal]? = some (.node event.declaration.id ds0) ∧
      LiteralTraceRule judgment s origin.child
        (.selected event.declaration.id event.kids) ⟨origin.child,event⟩ ∧
      AddressedDictionaryForest (judgment := judgment) s event.kids ds0 tail ∧
      (∃ unique : (event.declaration.associated.map Equation.name).Nodup,
        logicalOutputOfEvent399 event atlas origin.outputIndex unique = some out) ∧
      out.equation.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
      out.equation.ordinal = origin.outputOrdinal ∧ out.equation.requested = origin.output ∧
      (CompoundSourceRhs394 s (writtenBodySlot392 event out.body) false
        (normalize (bodyPattern out.body)) out.equation.rhs) ∧
      f.slots (.explicit body) binder.name =
        some ⟨out.equation.requested.target,out.equation.requested.target,out.equation.requested.target⟩ := by
  obtain ⟨event,whereDicts,later,loc,dict,guard,kids⟩ := original_where_selected_event399 origin forest
  obtain ⟨source,supplied⟩ := selected_where_supplier_exists399 origin event checked
  obtain ⟨plan,annotated,compatible⟩ := b6 event guard source supplied
  have unique := (checked.2 event.declaration (List.mem_of_getElem? event.declaredAt)).identified.2.2.1
  obtain ⟨out,made,same,meaning⟩ :=
    event_B6_source_produces_logical_rhs399 event atlas origin.outputIndex unique
      supplied annotated compatible
  have asked : out.equation.requested = origin.output :=
    (List.getElem?_eq_some_iff.mp origin.outputAt).2
  refine ⟨event,whereDicts,later,out,loc,dict,guard,kids,⟨unique,made⟩,rfl,rfl,asked,?_,?_⟩
  · rw [same]
    exact meaning
  · rw [asked]
    exact origin.slot

end Yulang.GeneralDeclarativeI65
