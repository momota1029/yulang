import Yulang.GeneralDeclarativeI65I74StructuralWhereSupportLookup428

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open I72.Checker408 (Problem)

structure OriginalVariableRead428 {s q} (f : AuthoredBodyFrame393 s q) (k : Nat) where
  actual : LiteralVariableArgumentAt428 f k
  lexical : actual.binder ∈ f.decl.inputNames

/-- The ordinal and the *literal* variable come from the already
checked source frame. There is no witness field for a replacement
capture or child Request. -/
def readOriginalVariable428 {s q} (f : AuthoredBodyFrame393 s q) (k : Nat) :
    Option (OriginalVariableRead428 f k) :=
  match atSource : f.decl.requirements[k]? with
  | none => none
  | some clause =>
    match originalArgs : clause.arguments with
    | [.var n] =>
      if known : n ∈ f.decl.inputNames then
        if empty : clause.outputs = [] then
          some ⟨⟨clause,atSource,n,originalArgs,empty⟩,known⟩
        else none
      else none
    | _ => none

/-- Pure routing to the *unchanged* pre-R14 named leaf dispatch;
no new case is added to any Witness or check type. -/
def existingBareNameRoute428 (w : I72.Named409.NamedWire) : I72.RepeatedCenters421.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.previous (.bareName w))))))))))))

structure MixedBodyWire428 where
  originalRecordRow : Nat
  structuralChild : LeafWire427
  bareNameChild : I72.Named409.NamedWire

structure ReadActualMixedBody428 (s : I72.State) (q : Request)
    (f : AuthoredBodyFrame393 s.core q) where
  parentChecked : DeclarationChecked (authoredRegistry s.core.current).constructors
    (authoredRegistry s.core.current).roles f.decl
  exactlyTwo : f.decl.requirements.length = 2
  first : OriginalRecordArgument427 f 0 0
  structural : ReadClosedChild427 first s.b6
  second : OriginalVariableRead428 f 1
  namedDecl : Declaration
  allAtNamed : visible s.core second.actual.child = [namedDecl]
  legacyWire : I72.Named409.NamedWire
  legacyAccepted : I72.RepeatedCenters421.check ⟨s,second.actual.child⟩
    (I72.Check408.nullaryReport namedDecl) (existingBareNameRoute428 legacyWire) = true

/-- Isolated body readback. Scope is one structural argument and one
direct variable sibling at their original source positions. The
caller supplies an independently checked parent frame, retained
row addresses, and old finite witness data, not selected Events,
child Requests or a result dictionary. An unrecognized body is
unsupported here, never a language-level rejection. -/
def readActualMixedBody428 {s : I72.State} {q : Request}
    (f : AuthoredBodyFrame393 s.core q)
    (header : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles f.decl)
    (w : MixedBodyWire428) : Option (ReadActualMixedBody428 s q f) := do
  if two : f.decl.requirements.length = 2 then
    let original ← readOriginalRecordArgument427 f ⟨0,0,w.originalRecordRow⟩
    let structural ← readModeClosedChild428 original s.b6 w.structuralChild
    let literal ← readOriginalVariable428 f 1
    let problem : Problem := ⟨s,literal.actual.child⟩
    match allNamed : visible s.core literal.actual.child with
    | [d] =>
      if old : I72.RepeatedCenters421.check problem (I72.Check408.nullaryReport d)
          (existingBareNameRoute428 w.bareNameChild) = true then
        pure ⟨header,two,original,structural,literal,d,allNamed,w.bareNameChild,old⟩
      else none
    | _ => none
  else none

theorem mixed_body_reader_uses_the_exact_original_children428 {s q f w header data}
    (_ : readActualMixedBody428 (s:=s) (q:=q) f header w = some data) :
    frameWhereKids400 f = [data.first.child,data.second.actual.child] ∧
      data.first.child.occurrence = q.occurrence ++ [0] ∧
      data.second.actual.child.occurrence = q.occurrence ++ [1] ∧
      data.second.actual.child.demand.arguments = [f.input data.second.actual.binder] := by
  refine ⟨literal_mixed_where_order_has_original_distinct_children428 data.first data.second.actual
    data.exactlyTwo,rfl,rfl,?_⟩
  change [f.names.input data.second.actual.binder] = [f.input data.second.actual.binder]
  unfold AuthoredBodyFrame393.names GeneralDeclarativeFrameReadback325.sourceNames
  rw [GeneralDeclarativeProducedNames325.exact_input data.parentChecked data.second.lexical]

theorem mixed_body_reader_gets_official_legacy_classification428
    {s q f w header data}
    (_ : readActualMixedBody428 (s:=s) (q:=q) f header w = some data) :
    I72.RepeatedCenters421.ClassifiedAs s data.second.actual.child
      (I72.Check408.nullaryReport data.namedDecl) :=
  (I72.RepeatedCenters421.check_sound ⟨s,data.second.actual.child⟩
    (I72.Check408.nullaryReport data.namedDecl)
    (existingBareNameRoute428 data.legacyWire) data.legacyAccepted).1

/-- Semantic evidence for the actual ordered body only. It combines
the literal structural proof with the *installed existing checker*
on the literal variable sibling in the same State and Model. -/
theorem mixed_body_reader_has_one_exact_model_forest428
    {s q f w header data}
    (actual : readActualMixedBody428 (s:=s) (q:=q) f header w = some data)
    (m : I72.Model) (fit : I72.Fits s m) :
    I72.DictionaryEvidenceForest s m (frameWhereKids400 f)
      [.node data.structural.source.decl.id [],.node data.namedDecl.id []] := by
  rw [(mixed_body_reader_uses_the_exact_original_children428 actual).1]
  refine .cons (original_compound_child_has_positive_same_model_dictionary427
    (atlas:=s.b6) data.structural.source m fit) (.cons ?_ .nil)
  exact I72.RepeatedCenters421.dictionary_sound_R13 s data.second.actual.child _
    (I72.RepeatedCenters421.exact_report_is_R13_classification421
      (mixed_body_reader_gets_official_legacy_classification428 actual)) m fit

end Yulang.GeneralDeclarativeI65.StructuralWhere428
