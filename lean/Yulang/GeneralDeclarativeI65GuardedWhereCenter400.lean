import Yulang.GeneralDeclarativeI65B6AddressedLogicalLedger399
import Yulang.GeneralDeclarativeWitnessCompiler350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeSourceEmission322 (demand exact_at useArg source_var)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeWitnessCompiler350 (Context preparation placed)
open GeneralDeclarativeClauseBatch327 (read_order)
open GeneralDeclarativeClausePlacement327 (placement portAt located)

theorem original_where_entry_origin400 {s q} (f : AuthoredBodyFrame393 s q)
    {i : Nat} {entry : LiteralWhereEntry}
    (atClause : f.clauses[i]? = some entry) :
    f.decl.requirements[i]? = some entry.clause ∧
      entry.demand = demand f.decl entry.clause f.names
        (f.placement.compound entry.clause) (f.placement.targets entry.clause) := by
  unfold AuthoredBodyFrame393.clauses at atClause
  rw [List.getElem?_map] at atClause
  cases original : f.decl.requirements[i]? with
  | none => simp [original] at atClause
  | some cl =>
    simp only [original,Option.map_some,Option.some.injEq] at atClause
    rw [← atClause]
    exact ⟨rfl,rfl⟩

def OriginalWhereRequest400 (q : Request) (i : Nat) (entry : LiteralWhereEntry) : Request :=
  ⟨q.occurrence ++ [i],entry.demand⟩

theorem literal_where_request_position400 {s q} (f : AuthoredBodyFrame393 s q)
    {i : Nat} {entry : LiteralWhereEntry}
    (atClause : f.clauses[i]? = some entry) :
    (children q (f.clauses.map LiteralWhereEntry.demand))[i]? =
      some (OriginalWhereRequest400 q i entry) := by
  have hit : (f.clauses.map LiteralWhereEntry.demand)[i]? = some entry.demand := by
    rw [List.getElem?_map,atClause]
    rfl
  unfold children OriginalWhereRequest400
  rw [List.getElem?_map,List.getElem?_zipIdx]
  simp [hit]

/-- The center name of a bare where argument is the source name;
the unused compound fallback and the center type row are not read. -/
theorem direct_where_argument_preserves_named_center400 {s q}
    (f : AuthoredBodyFrame393 s q) {i j : Nat} {entry : LiteralWhereEntry}
    {p : Pattern} {binder : Nat}
    (atClause : f.clauses[i]? = some entry)
    (atArg : entry.clause.arguments[j]? = some p)
    (bare : normalize p = .var binder) :
    entry.demand.arguments[j]? = some (f.names.input binder) ∧
      (entry.demand.arguments[j]?).map Capture.center = some (f.names.input binder).center := by
  have original := (original_where_entry_origin400 f atClause).2
  have read := exact_at f.names (f.placement.compound entry.clause) 0 entry.clause.arguments j atArg
  rw [source_var _ _ _ bare] at read
  have same : entry.demand.arguments[j]? = some (f.names.input binder) := by
    rw [original]
    exact read
  exact ⟨same,by rw [same]; rfl⟩

/-- Same authored compound position, actual prepared placement,
and actual guarded child of the finite where ledger. Only the
previously allocated name is recovered here; no `Input` assertion
about the center row is a premise and no fallback is used. -/
theorem guarded_where_compound_uses_original_port_center400 [judgment : ReplayJudgment]
    {s q} (f : AuthoredBodyFrame393 s q) (c : Context) {before ports}
    (prepared : preparation c = some (before,ports))
    (frameDecl : f.decl = c.decl) (framePlace : f.placement = placed c ports)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ci ai : Nat} {entry : LiteralWhereEntry} {p : Pattern}
    (atClause : f.clauses[ci]? = some entry)
    (atArg : entry.clause.arguments[ai]? = some p)
    (compound : Compound p)
    {ds events} (forest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events) :
    ∃ (port : GeneralDeclarativeClauseBatch327.Port)
      (event : LiteralLocalEvent s (OriginalWhereRequest400 q ci entry))
      (down : List Dictionary) (tail : LiteralEventForest (s := s)),
      portAt c.decl.requirements ports entry.clause = some port ∧
      entry.demand.arguments[ai]? = some (port.input ai) ∧
      (entry.demand.arguments[ai]?).map Capture.center = some (port.input ai).center ∧
      events.at399 ci = some (.node ⟨OriginalWhereRequest400 q ci entry,event⟩ tail) ∧
      ds[ci]? = some (.node event.declaration.id down) ∧
      LiteralTraceRule judgment s (OriginalWhereRequest400 q ci entry)
        (.selected event.declaration.id event.kids) ⟨OriginalWhereRequest400 q ci entry,event⟩ ∧
      AddressedDictionaryForest (judgment := judgment) s event.kids down tail := by
  obtain ⟨source,emits⟩ := original_where_entry_origin400 f atClause
  have parent := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have unique : (c.decl.requirements.map Clause.id).Nodup := frameDecl ▸ parent.identified.1
  have member : entry.clause ∈ c.decl.requirements := frameDecl ▸ List.mem_of_getElem? source
  have ran := prepared
  unfold preparation at ran
  obtain ⟨port,stored,_⟩ := located (read_order ran).2 unique member
  have actualPlacement : f.placement.compound entry.clause ai = port.input ai := by
    rw [framePlace]
    simp [placed,placement,stored]
  have selected : useArg f.names (f.placement.compound entry.clause ai) p =
      f.placement.compound entry.clause ai := by
    cases shape : normalize p with
    | var n => exact False.elim (compound n shape)
    | app n args => simp only [useArg,shape]
    | record n x y => simp only [useArg,shape]
    | variant n x => simp only [useArg,shape]
    | join x y => simp only [useArg,shape]
  have literal := exact_at f.names (f.placement.compound entry.clause) 0 entry.clause.arguments ai atArg
  have requestArg : entry.demand.arguments[ai]? = some (port.input ai) := by
    rw [Nat.zero_add,selected,actualPlacement] at literal
    rw [emits]
    exact literal
  obtain ⟨event,down,tail,whereEntry,dict,guard,kids⟩ :=
    addressed_child_event_at399 forest ci (literal_where_request_position400 f atClause)
  exact ⟨port,event,down,tail,stored,requestArg,by rw [requestArg]; rfl,
    whereEntry,dict,guard,kids⟩


open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarations (Equation)

theorem original_where_requests_are_declared400 {s q} (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ci : Nat} {entry : LiteralWhereEntry} (atClause : f.clauses[ci]? = some entry) :
    GeneralDeclarativeOutputSource323.Declared (authoredRegistry s.current) entry.demand := by
  obtain ⟨source,emits⟩ := original_where_entry_origin400 f atClause
  have decl := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have sig := decl.signature.2.2.2 entry.clause (List.mem_of_getElem? source)
  rw [emits]
  intro out there
  obtain ⟨eq,original,rfl⟩ := List.mem_map.mp there
  exact sig.2 eq original

/-- Role-side provenance and exact output order come from the original
clause's source, not from a literal receipt pointing to a matching value.
Only the B6 plan with original capture kind compatibility is supplied. -/
theorem B6_logical_original_where_outputs400 [judgment : ReplayJudgment]
    {s q} (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ci : Nat} {entry : LiteralWhereEntry} (atClause : f.clauses[ci]? = some entry)
    (event : LiteralLocalEvent s (OriginalWhereRequest400 q ci entry))
    (guard : LiteralTraceRule judgment s (OriginalWhereRequest400 q ci entry)
      (.selected event.declaration.id event.kids) ⟨OriginalWhereRequest400 q ci entry,event⟩)
    (atlas : B6SymbolicAtlas398 s) (b6 : SuppliesSymbolicB6AtEvents399 (judgment := judgment) s atlas) :
    ∀ i : Fin entry.demand.outputs.length,
      ∃ (out : EventLogicalOutput399 event i) (unique : (event.declaration.associated.map Equation.name).Nodup),
        logicalOutputOfEvent399 event atlas i unique = some out ∧
        out.equation.occurrence = q.occurrence ++ [ci] ∧ out.equation.ordinal = i.val ∧
        out.equation.requested = entry.demand.outputs[i] ∧
        CompoundSourceRhs394 s (writtenBodySlot392 event out.body) false
          (normalize (bodyPattern out.body)) out.equation.rhs := by
  let r := authoredRegistry s.current
  have declared := original_where_requests_are_declared400 f checked atClause
  have chosen := checked.2 event.declaration (List.mem_of_getElem? event.declaredAt)
  have roleEq := (visible_exact s (OriginalWhereRequest400 q ci entry) event.declaration).mp event.inScope |>.2
  intro i
  have requested := declared entry.demand.outputs[i] (List.getElem_mem _)
  obtain ⟨source,supplied⟩ := GeneralDictionaryAssociatedProvenance.declared_covered r.roles
    event.declaration chosen.signature entry.demand.outputs[i].name (roleEq ▸ requested)
  obtain ⟨p,annotated,fit⟩ := b6 (OriginalWhereRequest400 q ci entry) event guard i source supplied
  have unique := chosen.identified.2.2.1
  obtain ⟨out,value,same,meaning⟩ :=
    event_B6_source_produces_logical_rhs399 event atlas i unique supplied annotated fit
  exact ⟨out,unique,value,rfl,rfl,rfl,by simpa only [same]⟩

/-- If the already selected child's own B6 plan reads an original
role positional variable, the same literal guarded child supplies
the original recorded center. No center structure is inspected. -/
theorem B6_default_replays_actual_where_center400 {s q ci entry}
    (event : LiteralLocalEvent s (OriginalWhereRequest400 q ci entry))
    {j : Nat} {cap : Capture} (actual : entry.demand.arguments[j]? = some cap)
    (role name : Nat) (rhs : Roles.Term) :
    (instantiateB6Value398 (writtenBodySlot392 event (.default role name rhs))
      (B6ValuePlan398.binder (s := s) (context := false) j)).map Subtype.val =
      some (.variable j cap.center) := by
  simp [writtenBodySlot392,OriginalWhereRequest400,instantiateB6Value398,actual]

/-- Combine the two independent reads on one and the same child
event. The child's preallocated center name reaches its actual
request, and B6 is then consumed only in that event's exact source
outputs. This is an already-addressed finite derivation, not a new
candidate rule or a mixed literal-wire encoding. -/
theorem guarded_where_center_and_B6_meaning400 [judgment : ReplayJudgment]
    {s q} (f : AuthoredBodyFrame393 s q) (c : Context) {before ports}
    (prepared : preparation c = some (before,ports))
    (frameDecl : f.decl = c.decl) (framePlace : f.placement = placed c ports)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ci ai : Nat} {entry : LiteralWhereEntry} {p : Pattern}
    (atClause : f.clauses[ci]? = some entry)
    (atArg : entry.clause.arguments[ai]? = some p)
    (compound : Compound p)
    {ds events} (forest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (atlas : B6SymbolicAtlas398 s) (b6 : SuppliesSymbolicB6AtEvents399 (judgment := judgment) s atlas) :
    ∃ (port : GeneralDeclarativeClauseBatch327.Port)
      (event : LiteralLocalEvent s (OriginalWhereRequest400 q ci entry))
      (down : List Dictionary) (tail : LiteralEventForest (s := s)),
      portAt c.decl.requirements ports entry.clause = some port ∧
      entry.demand.arguments[ai]? = some (port.input ai) ∧
      (entry.demand.arguments[ai]?).map Capture.center = some (port.input ai).center ∧
      events.at399 ci = some (.node ⟨OriginalWhereRequest400 q ci entry,event⟩ tail) ∧
      ds[ci]? = some (.node event.declaration.id down) ∧
      LiteralTraceRule judgment s (OriginalWhereRequest400 q ci entry)
        (.selected event.declaration.id event.kids) ⟨OriginalWhereRequest400 q ci entry,event⟩ ∧
      AddressedDictionaryForest (judgment := judgment) s event.kids down tail ∧
      ∀ i : Fin entry.demand.outputs.length,
        ∃ (out : EventLogicalOutput399 event i) (unique : (event.declaration.associated.map Equation.name).Nodup),
          logicalOutputOfEvent399 event atlas i unique = some out ∧
          out.equation.occurrence = q.occurrence ++ [ci] ∧ out.equation.ordinal = i.val ∧
          out.equation.requested = entry.demand.outputs[i] ∧
          CompoundSourceRhs394 s (writtenBodySlot392 event out.body) false
            (normalize (bodyPattern out.body)) out.equation.rhs := by
  obtain ⟨port,event,down,tail,stored,arg,center,loc,dict,guard,kids⟩ :=
    guarded_where_compound_uses_original_port_center400 f c prepared frameDecl framePlace
      checked atClause atArg compound forest
  exact ⟨port,event,down,tail,stored,arg,center,loc,dict,guard,kids,
    B6_logical_original_where_outputs400 f checked atClause event guard atlas b6⟩

end Yulang.GeneralDeclarativeI65
