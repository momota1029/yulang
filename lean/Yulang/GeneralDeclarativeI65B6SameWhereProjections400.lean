import Yulang.GeneralDeclarativeI65B6ExactProjections399
import Yulang.GeneralDeclarativeI65B6AddressedLogicalLedger399

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Clause Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body)

private theorem checked_key_source_positions399 {A : Type} (key : A → Nat) {list : List A}
    (unique : (list.map key).Nodup) {a b : A} {i j : Nat}
    (first : list[i]? = some a) (last : list[j]? = some b)
    (sameKey : key a = key b) :
    i = j ∧ a = b := by
  have f : (list.map key)[i]? = some (key a) := by rw [List.getElem?_map,first]; rfl
  have l : (list.map key)[j]? = some (key b) := by rw [List.getElem?_map,last]; rfl
  obtain ⟨hi,qi⟩ := List.getElem?_eq_some_iff.mp f
  obtain ⟨hj,qj⟩ := List.getElem?_eq_some_iff.mp l
  have atSame : i = j := (unique.getElem_inj (hi := hi) (hj := hj)).mp
    (qi.trans (sameKey.trans qj.symm))
  exact ⟨atSame,Option.some.inj (first.symm.trans (atSame ▸ last))⟩

theorem original_where_clause_position399 {s q f binder body}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body) :
    f.decl.requirements[origin.clauseOrdinal]? = some origin.entry.clause := by
  have seen := origin.atClause
  unfold AuthoredBodyFrame393.clauses at seen
  rw [List.getElem?_map] at seen
  cases actual : f.decl.requirements[origin.clauseOrdinal]? with
  | none => simp [actual] at seen
  | some cl =>
    simp only [actual,Option.map_some,Option.some.injEq] at seen
    exact congrArg (fun entry : LiteralWhereEntry => some entry.clause) seen

/-- The original binder owns one exact where clause and output ordinal
in a checked declaration. Different prepared captures or placements
cannot move the authored source equations to another position. -/
theorem original_where_identity_fixes_ordinals399 {s q f g binder body}
    (first : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (last : OriginalWhereBinder395 (s := s) (q := q) g binder body)
    (sameDecl : f.decl = g.decl)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current)) :
    first.clauseOrdinal = last.clauseOrdinal ∧ first.entry.clause = last.entry.clause ∧
      first.outputOrdinal = last.outputOrdinal ∧ first.equation = last.equation := by
  have check := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have firstClause := original_where_clause_position399 first
  have lastClause := original_where_clause_position399 last
  rw [← sameDecl] at lastClause
  obtain ⟨clOrd,cl⟩ := checked_key_source_positions399 Clause.id check.identified.1
    firstClause lastClause (first.clauseId.trans last.clauseId.symm)
  have eqKeys := check.identified.2.2.2.2 first.entry.clause (List.mem_of_getElem? firstClause)
  have lastEquation := last.atEquation
  rw [← cl] at lastEquation
  obtain ⟨ord,eq⟩ := checked_key_source_positions399 Equation.id eqKeys
    first.atEquation lastEquation (first.equationId.trans last.equationId.symm)
  exact ⟨clOrd,cl,ord,eq⟩

def LiteralEventTree.request399 {s : State} : LiteralEventTree (s := s) → Request
  | .node event _ => event.1

/-- If two authentic frames feed the same exact finite child ledger,
the original output binder reads the same point address. Its child is
identified by the shared retained event at the authored occurrence,
not by comparing only the child dictionary or using equivalent types. -/
theorem original_where_slots_agree_from_same_exact_ledger399 [judgment : ReplayJudgment]
    {s q f g binder body ds events}
    (first : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (last : OriginalWhereBinder395 (s := s) (q := q) g binder body)
    (sameDecl : f.decl = g.decl)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (firstForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (lastForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (g.clauses.map LiteralWhereEntry.demand)) ds events) :
    first.child = last.child ∧ first.output = last.output ∧
      f.slots (.explicit body) binder.name = g.slots (.explicit body) binder.name := by
  obtain ⟨clOrd,_,outOrd,_⟩ := original_where_identity_fixes_ordinals399 first last sameDecl checked
  obtain ⟨evF,_,kidsF,atF,_,_,_⟩ := original_where_selected_event399 first firstForest
  obtain ⟨evG,_,kidsG,atG,_,_,_⟩ := original_where_selected_event399 last lastForest
  rw [← clOrd] at atG
  have sameNode : LiteralEventTree.node ⟨first.child,evF⟩ kidsF =
      LiteralEventTree.node ⟨last.child,evG⟩ kidsG :=
    Option.some.inj (atF.symm.trans atG)
  have child : first.child = last.child := congrArg LiteralEventTree.request399 sameNode
  have fRead : first.child.demand.outputs[first.outputOrdinal]? = some first.output := first.outputAt
  have gRead : last.child.demand.outputs[last.outputOrdinal]? = some last.output := last.outputAt
  rw [← child,← outOrd] at gRead
  have sameOutput := Option.some.inj (fRead.symm.trans gRead)
  exact ⟨child,sameOutput,by rw [first.slot,last.slot,sameOutput]⟩

/-- Both center and span projections follow from the actual shared
producing where event, without assuming equality of the two full
lexical capture tables. -/
theorem original_where_projection_from_same_exact_ledger399 [judgment : ReplayJudgment]
    {s q f g binder body ds events}
    (first : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (last : OriginalWhereBinder395 (s := s) (q := q) g binder body)
    (sameDecl : f.decl = g.decl)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (firstForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (lastForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (g.clauses.map LiteralWhereEntry.demand)) ds events)
    (projection : B4Projection399) :
    observedB4Projection399 (f.slots (.explicit body)) binder.name projection =
      observedB4Projection399 (g.slots (.explicit body)) binder.name projection := by
  have agree := (original_where_slots_agree_from_same_exact_ledger399
    first last sameDecl checked firstForest lastForest).2.2
  cases projection <;> simp [observedB4Projection399,agree]

open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarations (OutputBinder)

/-- Of the projections used by B6's same source plan, the where
part is forced by the actual shared finite child ledger and the
declaration's production law. Default positions are the same actual
request by construction. Only the original head projections need an
independent readback; the proof does not ask for entire tables equal. -/
theorem B6_frame_projection_agreement_from_head_and_where399 [judgment : ReplayJudgment]
    {s q} (f g : AuthoredBodyFrame393 s q) (sameDecl : f.decl = g.decl)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ds events}
    (firstForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (lastForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (g.clauses.map LiteralWhereEntry.demand)) ds events)
    {name body} (supplied : Supplies (authoredRegistry s.current).roles f.decl name body)
    {context} (plan : B6ValuePlan398 s context (normalize (bodyPattern body)))
    (retainedHead : ∀ r ∈ plan.readShape399, r.1 ∈ f.decl.inputNames →
      observedB4Projection399 (f.slots body) r.1 r.2 =
        observedB4Projection399 (g.slots body) r.1 r.2) :
    AgreeB4Observations399 (f.slots body) (g.slots body) plan.readShape399 := by
  cases supplied with
  | default real _ _ =>
    intro r _
    cases r.2 <;> rfl
  | explicit eq attached named =>
    have checkedF := checked.2 f.decl (List.mem_of_getElem? f.authored)
    have checkedG := checked.2 g.decl (List.mem_of_getElem? g.authored)
    intro r uses
    have lexical : r.1 ∈ (normalize (bodyPattern (.explicit eq))).variables := by
      rw [← B6_read_names_are_original_syntax399 plan]
      exact List.mem_map.mpr ⟨r,uses,rfl⟩
    rcases checkedF.scope.2.1 eq attached r.1 lexical with fromHead|fromWhere
    · exact retainedHead r uses fromHead
    · obtain ⟨binder,member,key⟩ := List.mem_map.mp fromWhere
      have memberG : binder ∈ g.decl.outputBinders := sameDecl ▸ member
      obtain ⟨first⟩ := original_where_produces_lexical_slot395 f checkedF.produced eq member
      obtain ⟨last⟩ := original_where_produces_lexical_slot395 g checkedG.produced eq memberG
      rw [← key]
      exact original_where_projection_from_same_exact_ledger399 first last sameDecl checked
        firstForest lastForest r.2

/-- Compare a prepared source frame with the actual captured event.
Where positions are linked to the same finite dictionary occurrence.
One cannot replace the independent proof of original head centers
by the native interval typing witness alone. -/
theorem B6_actual_event_projection_agreement399 [judgment : ReplayJudgment]
    {s q} (actual : LiteralLocalEvent s q) (f g : AuthoredBodyFrame393 s q)
    (sameDecl : f.decl = g.decl) (sameRetained : SamePreoutputFrame399 actual g)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {ds events}
    (firstForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (f.clauses.map LiteralWhereEntry.demand)) ds events)
    (retainedForest : AddressedDictionaryForest (judgment := judgment) s actual.kids ds events)
    {name body} (supplied : Supplies (authoredRegistry s.current).roles f.decl name body)
    {context} (plan : B6ValuePlan398 s context (normalize (bodyPattern body)))
    (sameHead : ∀ r ∈ plan.readShape399, r.1 ∈ f.decl.inputNames →
      observedB4Projection399 (f.slots body) r.1 r.2 =
        observedB4Projection399 (writtenBodySlot392 actual body) r.1 r.2) :
    AgreeB4Observations399 (f.slots body) (writtenBodySlot392 actual body) plan.readShape399 := by
  have lastForest : AddressedDictionaryForest (judgment := judgment) s
      (children q (g.clauses.map LiteralWhereEntry.demand)) ds events :=
    (same_preoutput_children399 sameRetained) ▸ retainedForest
  rw [← same_preoutput_slots399 sameRetained body] at sameHead ⊢
  exact B6_frame_projection_agreement_from_head_and_where399 f g sameDecl checked
    firstForest lastForest supplied plan sameHead

end Yulang.GeneralDeclarativeI65
