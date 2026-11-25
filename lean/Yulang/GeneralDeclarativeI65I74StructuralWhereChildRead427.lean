import Yulang.GeneralDeclarativeI65I74StructuralWherePositive427
import Yulang.GeneralDeclarativeI65I74RoleDefaultReplay420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open I72.List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open I72 (RootCycle)

structure LeafWire427 where
  declarationOrdinal : Nat
  escape : ExactEscapeWire

structure ReadClosedChild427 {s q f k}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0) (atlas : B6OccurrenceAtlas401 s) where
  source : ClosedChild427 a
  rawSafe : ¬ RootCycle ⟨s,atlas⟩ a.child

/-- The child is read at the exact demand generated before it. The
wire does not carry a declaration body, winning result, model,
reordered child path, or assumed source head. -/
def readClosedChild427 {s q f k}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0)
    (atlas : B6OccurrenceAtlas401 s) (w : LeafWire427) :
    Option (ReadClosedChild427 a atlas) := do
  let orig := s.current.environment.source
  let registry := authoredRegistry s.current
  if covered : GeneralSourceMetadataDeclarations291.explicitCheck
      registry (GeneralSourceMetadataRows291.interpretation orig.snapshot) = true then
    match onRow : registry.declarations[w.declarationOrdinal]? with
    | none => none
    | some d =>
      if scanned : GeneralDeclarativeWitnessHeader349.checksDecl orig d = true then
       if only : visible s a.child = [d] then
        match head : d.head with
        | [.record label (.var binder) (.app empty [])] =>
          if same : label = a.label then
            match compiled : translateWhere427 s (writtenRecord427 a.label binder empty) with
            | none => none
            | some code =>
              if verbatim : eqExpr code (recordCode427 a.label binder) = true then
                match inputArity : a.child.demand.arguments with
                | [arg] =>
                  if emptyOutputs : a.child.demand.outputs = [] then
                    if emptyWhere : d.requirements = [] then
                      if raw : checkExactEscape s.current.ordinary a.name w.escape = true then
                        let atFirst := structural_where_child_argument_is_placed_point427 a
                        have atPoint : arg = point a.name := by simpa only [inputArity,List.getElem?_cons_zero,Option.some.injEq] using atFirst
                        have args : a.child.demand.arguments = [point a.name] :=
                          inputArity.trans (congrArg (fun c => [c]) atPoint)
                        have rawSafe : ¬ RootCycle ⟨s,atlas⟩ a.child := by
                          rintro ⟨c,member,cycle⟩
                          change c ∈ a.child.demand.arguments at member
                          rw [args] at member
                          cases List.mem_singleton.mp member
                          exact exact_escape_refutes_raw_root_K2410 raw cycle
                        let covers :=
                          (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp covered
                        let declaration :=
                          GeneralDeclarativeWitnessHeader349.decl_checked
                            (covers d (List.mem_of_getElem? onRow)) scanned
                        pure ⟨⟨d,w.declarationOrdinal,onRow,only,declaration,binder,empty,
                          by simpa only [same,writtenRecord427] using head,
                          compiled.trans (congrArg some ((eq_expr ..).mp verbatim)),
                          args,emptyOutputs,emptyWhere⟩,rawSafe⟩
                      else none
                    else none
                  else none
                | _ => none
              else none
          else none
        | _ => none
       else none
      else none
  else none

/-- Successful reconstruction supplies actual positive dictionary
evidence at the genuine child in every fitting model, not a result
assertion about the parent or the canonical checker. -/
theorem checked_original_structural_child_has_same_model_dictionary427 {s q f k a atlas w d}
    (_ : readClosedChild427 (s:=s) (q:=q) (f:=f) (k:=k) a atlas w = some d)
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m a.child (.node d.source.decl.id []) :=
  original_compound_child_has_positive_same_model_dictionary427 d.source m fit

end Yulang.GeneralDeclarativeI65.StructuralWhere427
