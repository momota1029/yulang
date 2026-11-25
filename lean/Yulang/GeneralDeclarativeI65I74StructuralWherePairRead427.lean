import Yulang.GeneralDeclarativeI65I74StructuralWhereHeadRead427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeEmissionForest322 (Placement)

structure PositivePairWire427 where
  parent : PositiveHeadWire427
  originalWhereRow : Nat
  child : PositiveHeadWire427
  parentRival : RivalWire427
  childRival : RivalWire427

private def atRetainedPoint427 (n : Nat) : Placement :=
  ⟨fun _ _ => point n,fun _ _ => 0⟩

private def zeroPlacement427 : Placement := atRetainedPoint427 0

/-- Reuse the exact existing nested-record descent, not the sufficient
general shape approximation which does not recognize this source. -/
def checkedOriginalParent427 (s : State) (d : Declaration)
    (auth : d ∈ (authoredRegistry s.current).declarations) :
    Option (PLift (DeclarationChecked (authoredRegistry s.current).constructors
      (authoredRegistry s.current).roles d)) := do
  let env := s.current.environment
  if hasRoles : GeneralSourceMetadataRoles291.check env.source.roles = true then
    let roles := (GeneralSourceMetadataRoles291.check_exact _).mp hasRoles
    if modeScope : GeneralDeclarativeWitnessModeCoverage357.check env = true then
      let cov := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp modeScope
      match h : d.head, requirements : d.requirements with
      | [.record box (.record tick (.var binder) (.app inner [])) (.app outer [])], [cl] =>
        if empties : inner = outer then
          if args : cl.arguments = [I72.RecordK2412.closedWhere412 box outer binder] then
            if checked : I72.RecordK2412.header412 s.current d = true then
              if desc : I72.RecordK2412.recordDescent412 d.head cl.arguments = true then
                have exactHead : d.head = [I72.RecordK2412.closedHead412 box tick outer binder] :=
                  by simpa only [I72.RecordK2412.closedHead412,empties] using h
                pure ⟨I72.RecordK2412.checked_record_header412 (cov.1 d auth) checked
                  exactHead requirements args desc⟩
              else none
            else none
          else none
        else none
      | _,_ => none
    else none
  else none

structure ReadPositivePair427 (s : State) (q : Request) where
  root : ReadPositiveHead427 s q
  frame : AuthoredBodyFrame393 s q
  rootDecl : frame.decl = root.decl
  rootCapture : frame.input = root.capture
  original : OriginalRecordArgument427 frame 0 0
  child : ReadPositiveHead427 s original.child
  childFrame : AuthoredBodyFrame393 s original.child
  childDecl : childFrame.decl = child.decl
  childCapture : childFrame.input = child.capture
  parentRival : ReadBoxRival427 s q
  childRival : ReadBoxRival427 s original.child
  parentCandidates :
    visible s q = [root.decl,parentRival.decl] ∨ visible s q = [parentRival.decl,root.decl]
  originalChildCandidates :
    visible s original.child = [child.decl,childRival.decl] ∨
      visible s original.child = [childRival.decl,child.decl]
  rootHasOneWhere : frame.decl.requirements.length = 1
  childHasNoWhere : childFrame.decl.requirements = []
  rootNoOutput : q.demand.outputs = []
  childNoOutput : original.child.demand.outputs = []
  rootDeclarationChecked : DeclarationChecked (authoredRegistry s.current).constructors
    (authoredRegistry s.current).roles root.decl
  childDeclarationChecked : DeclarationChecked (authoredRegistry s.current).constructors
    (authoredRegistry s.current).roles child.decl

/-- Address-only witness, narrowed to a literal structural argument,
a two-candidate pair at each actual request, zero outputs and one
where child. Neither winning ID, role, capture, child coordinate,
local semantic proof nor a classification is included in the wire.
The checked placement here is only the single original source
position of the retained row, not a claim about an allocator. -/
def readOriginalPositivePair427 (s : State) (q : Request) (w : PositivePairWire427) :
    Option (ReadPositivePair427 s q) := do
  let orig := s.current.environment.source
  let registry := authoredRegistry s.current
  if covered : GeneralSourceMetadataDeclarations291.explicitCheck
      registry (GeneralSourceMetadataRows291.interpretation orig.snapshot) = true then
    let covers := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp covered
    let root ← readPositiveHead427 s q w.parent
    let rootDeclCheck ← checkedOriginalParent427 s root.decl (List.mem_of_getElem? root.fromRegistry)
    if one : root.decl.requirements.length = 1 then
      if rootNoOut : q.demand.outputs = [] then
        let row ← s.current.ordinary.equations[w.originalWhereRow]?
        let frame : AuthoredBodyFrame393 s q := ⟨root.ordinal,root.decl,
          root.fromRegistry,root.visibleDecl,atRetainedPoint427 row.left,root.capture⟩
        let original ← readOriginalRecordArgument427 frame ⟨0,0,w.originalWhereRow⟩
        let child ← readPositiveHead427 s original.child w.child
        if childDeclCheck : GeneralDeclarativeWitnessHeader349.checksDecl orig child.decl = true then
          if leaf : child.decl.requirements = [] then
            if childNoOut : original.child.demand.outputs = [] then
              let childFrame : AuthoredBodyFrame393 s original.child := ⟨child.ordinal,child.decl,
                child.fromRegistry,child.visibleDecl,zeroPlacement427,child.capture⟩
              let parentRival ← readBoxRival427 s q w.parentRival
              let childRival ← readBoxRival427 s original.child w.childRival
              if pv : visible s q = [root.decl,parentRival.decl] ∨
                  visible s q = [parentRival.decl,root.decl] then
                if cv : visible s original.child = [child.decl,childRival.decl] ∨
                    visible s original.child = [childRival.decl,child.decl] then
                  pure ⟨root,frame,rfl,rfl,original,child,childFrame,rfl,rfl,
                    parentRival,childRival,pv,cv,one,leaf,rootNoOut,childNoOut,
                    rootDeclCheck.down,
                    GeneralDeclarativeWitnessHeader349.decl_checked
                      (covers child.decl (List.mem_of_getElem? child.fromRegistry)) childDeclCheck⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem read_original_structural_pair_lexical_capture_from_same_source427 {s q w p}
    (_ : readOriginalPositivePair427 s q w = some p) :
    p.frame.names.input p.original.binder = p.root.capture p.original.binder := by
  have inside : p.original.binder ∈ p.root.decl.inputNames := by
    rw [← p.rootDecl]
    exact p.original.inHead
  unfold AuthoredBodyFrame393.names GeneralDeclarativeFrameReadback325.sourceNames
  rw [p.rootDecl,p.rootCapture]
  exact GeneralDeclarativeProducedNames325.exact_input p.rootDeclarationChecked inside

theorem read_original_structural_pair_exact_fixed_dictionary427 {s q w p}
    (_ : readOriginalPositivePair427 s q w = some p)
    (atlas : B6OccurrenceAtlas401 s) (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m q (.node p.frame.decl.id [.node p.childFrame.decl.id []]) :=
  same_state_structural_where_pair_has_fixed_dictionary427
    p.original p.childFrame (p.rootDecl.symm ▸ p.root.head)
    (p.childDecl.symm ▸ p.child.head) p.rootHasOneWhere p.rootNoOutput p.childNoOutput
    p.childHasNoWhere m fit

theorem read_original_structural_pair_excludes_rivals_at_both_actual_requests427 {s q w p}
    (_ : readOriginalPositivePair427 s q w = some p)
    (m : Model) (fit : Fits s m) :
    (∀ d ∈ visible s q, Nonempty (SourceHead s q d) → d = p.root.decl) ∧
    (∀ d ∈ visible s p.original.child, Nonempty (SourceHead s p.original.child d) → d = p.child.decl) :=
  ⟨(positive_box_cannot_be_displaced_by_its_checked_rival427
      p.parentRival p.parentCandidates ⟨p.root.head⟩ m fit).2,
    (positive_box_cannot_be_displaced_by_its_checked_rival427
      p.childRival p.originalChildCandidates ⟨p.child.head⟩ m fit).2⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere427
