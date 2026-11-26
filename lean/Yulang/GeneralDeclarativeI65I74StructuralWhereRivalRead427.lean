import Yulang.GeneralDeclarativeI65I74StructuralWhereRigid427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open I72.List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeInspect321 (Visit)

structure RivalWire427 where
  declarationOrdinal : Nat
  rootRow : Nat
  payloadRow : Nat
  rootEscape : ExactEscapeWire
  payloadEscape : ExactEscapeWire

structure ReadBoxRival427 (s : State) (q : Request) where
  decl : Declaration
  found : BoxRival427 s q decl
  originalRootSafe : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) found.root
  originalPayloadSafe : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) found.field

def readOpposite427 (s : State) (site row : Nat) (want : Expr) :
    Option (ExactOpposite427 s site want) :=
  match want with
  | .record _ _ _ =>
    match found : s.current.ordinary.equations[row]? with
    | some ⟨name,.primitive (.scalar .int) []⟩ =>
      if original : name = site then
        some (.intAgainstRecord (by simpa only [original] using found))
      else none
    | _ => none
  | .primitive (.scalar .int) [] =>
    match found : s.current.ordinary.equations[row]? with
    | some ⟨name,.record label (.variable field) (.primitive .emptyRecord [])⟩ =>
      if original : name = site then
        some (.recordAgainstInt (label:=label) (field:=field) (row:=row) (by simpa only [original] using found))
      else none
    | _ => none
  | _ => none

private theorem original_point427 (a : Capture) (n : Nat)
    (h : a.lower = n ∧ a.center = n ∧ a.upper = n) : a = point n := by
  cases a
  dsimp at h
  obtain ⟨rfl,rfl,rfl⟩ := h
  rfl

/-- No negative fallback: the real authored rival and original visited
raw field have to be readable and positively opposite. A missing
row, changed site/address, or raw cycle produces none, not rejection. -/
def readBoxRival427 (s : State) (q : Request) (w : RivalWire427) :
    Option (ReadBoxRival427 s q) := do
  match seenDecl : (authoredRegistry s.current).declarations[w.declarationOrdinal]? with
  | none => none
  | some decl =>
    if scope : decl ∈ visible s q then
      match actualArgs : q.demand.arguments with
      | [arg] =>
        match actualHead : decl.head with
        | [.record box pattern rem] =>
          match compiled : translateWhere427 s (.record box pattern rem) with
          | some (.record decoded want tail) =>
            match seenRoot : s.current.ordinary.equations[w.rootRow]? with
            | some ⟨root,.record recorded (.variable payload) (.primitive .emptyRecord [])⟩ =>
              if exactBox : decoded = box ∧ recorded = box then
                if atPoint : arg.lower = root ∧ arg.center = root ∧ arg.upper = root then
                  if rootSafe : checkExactEscape s.current.ordinary root w.rootEscape = true then
                    if fieldSafe : checkExactEscape s.current.ordinary payload w.payloadEscape = true then
                      let clash ← readOpposite427 s payload w.payloadRow want
                      have exactArgs : q.demand.arguments = [point root] :=
                        actualArgs.trans (congrArg (fun x => [x]) (original_point427 arg _ atPoint))
                      pure ⟨decl,⟨w.declarationOrdinal,seenDecl,scope,root,exactArgs,box,pattern,rem,
                        actualHead,want,tail,by simpa only [exactBox.1] using compiled,payload,w.rootRow,
                        by simpa only [exactBox.2] using seenRoot,clash⟩,
                        exact_escape_refutes_raw_root_K2410 rootSafe,exact_escape_refutes_raw_root_K2410 fieldSafe⟩
                    else none
                  else none
                else none
              else none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    else none

theorem actual_read_competing_box_candidate_has_original_visit_and_no_head427 {s q w r}
    (_ : readBoxRival427 s q w = some r) (m : Model) (fit : Fits s m) :
    Visit (structural s.current.ordinary) r.found.root
        (.record r.found.box r.found.want r.found.tail) r.found.field ∧
      (¬ AliasCycle s.current.ordinary (observed s.current.ordinary) r.found.field) ∧
      ¬Nonempty (SourceHead s q r.decl) :=
  ⟨real_rival_visits_original_mismatched_field427 r.found,r.originalPayloadSafe,
    model_excludes_source_head_with_actual_opposite_payload427 r.found m fit⟩

/-- Same-role two-candidate cut: use the whole exact visible list in
either authored order. The rival is ruled out by its real positive
mismatch observation, and the other has its own source head.
This theorem does not select merely because the first candidate read
succeeded, nor does it add an R15 rule. -/
theorem positive_box_cannot_be_displaced_by_its_checked_rival427
    {s q winner} (d : ReadBoxRival427 s q)
    (visibleExactly : visible s q = [winner,d.decl] ∨ visible s q = [d.decl,winner])
    (head : Nonempty (SourceHead s q winner)) (m : Model) (fit : Fits s m) :
    Nonempty (SourceHead s q winner) ∧
    ∀ row ∈ visible s q, Nonempty (SourceHead s q row) → row = winner := by
  refine ⟨head,fun row mem source => ?_⟩
  have either : row = winner ∨ row = d.decl := by
    rcases visibleExactly with original|reverse
    · simpa [original] using mem
    · exact Or.symm (by simpa [reverse] using mem : row = d.decl ∨ row = winner)
  rcases either with rfl|rfl
  · rfl
  · exact (model_excludes_source_head_with_actual_opposite_payload427 d.found m fit source).elim

end Yulang.GeneralDeclarativeI65.StructuralWhere427
