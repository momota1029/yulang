import Yulang.GeneralNominalInspectionAlignment

/-! A simultaneous positional invariant for finite input labels, real
intervals, inherited origins, and occurrences in the full capture report. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalInspectionPositions
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality
open GeneralNominalGroundAccessibility GeneralNominalMatchedAssembly GeneralNominalHeadMatchMass
open GeneralNominalSharedCaptures GeneralNominalSaturationState

def Input (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (state : GeneralNominalState.State) (bounds : Bounds state) (origin : Option Origin) (term : Expr Nat) : Prop :=
  (∃ pattern, ClosedTerm context pattern term) ∧ Fits state model bounds (denote (fun _ => .bottom) term) ∧
    ∀ root, origin = some root → At model .actual root (denote (fun _ => .bottom) term)

def InputsAt (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (state : GeneralNominalState.State) (origins : Nat → Option Origin) :
    Nat → List (Bounds state) → List (Expr Nat) → Prop
  | _,[],[] => True
  | offset,bounds :: intervals,term :: terms => Input context model state bounds (origins offset) term ∧
      InputsAt context model state origins (offset+1) intervals terms
  | _,_,_ => False

theorem inputs_at (bounds : List (Bounds state)) (terms : List (Expr Nat)) (length : terms.length = bounds.length)
    (known : ∀ index : Fin bounds.length, Input context model state bounds[index] (origins (offset+index.val))
      (terms[index.val]'(by rw [length]; exact index.isLt))) : InputsAt context model state origins offset bounds terms := by
  induction bounds generalizing terms offset with
  | nil => have empty : terms = [] := List.eq_nil_of_length_eq_zero length; subst terms; trivial
  | cons head tail ih =>
    cases terms with
    | nil => cases length
    | cons term rest =>
      refine ⟨by simpa using known ⟨0,by simp⟩,?_⟩
      apply ih rest (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using length)
      intro index
      have next := known ⟨index.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using index.isLt⟩
      simpa [Nat.add_assoc,Nat.add_comm 1 index.val] using next

theorem closed_child (closed : ClosedTerm context pattern (.node test children)) (index : Fin (arity test)) :
    ∃ source, ClosedTerm context source (children index) := by
  have followed : Follows (.source 0) (.node test children) (project (.source 0) test index) (children index) :=
    .child test children index .root
  obtain ⟨source,_,_,reified⟩ := GeneralNominalClosedPatternNormal.closed_reification followed closed
  exact ⟨source,reified⟩

theorem retained_child (known : ∀ root, origin = some root → At model .actual root
      (denote (fun _ => .bottom) (.node test children)))
    (canonical : Canonical (.node test children)) (index : Fin (arity test)) :
    ∀ root, origin.map (fun parent => project parent test index) = some root →
      At model .actual root (denote (fun _ => .bottom) (children index)) := by
  intro root recorded
  obtain ⟨parent,present,equal⟩ := Option.map_eq_some_iff.mp recorded
  subst root
  exact project_value test canonical.1 _ (known parent present) index

theorem variable_match (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (branch : packet.Holds model) (generation : GenerationGuard tracked packet)
    {bounds : Bounds packet.context.state}
    (known : Input context model packet.context.state bounds origin term)
    (included : (inspect packet.context.state (.variables [name]) bounds origin).captures ⊆ (inheritedReport packet).captures) :
    Matches (CapturedPart context packet model) (.variables [name]) term := by
  obtain ⟨⟨pattern,closed⟩,_,retained⟩ := known
  have member : (⟨name,bounds,origin⟩ : Capture packet.context.state) ∈ (inheritedReport packet).captures :=
    included (by simp [inspect])
  apply Matches.capture
  cases origin with
  | some root => exact recorded_capture_part packet model branch generation _ member rfl closed (retained root rfl)
  | none =>
    apply Or.inl
    refine ⟨?_,closed.2.1⟩
    intro needed
    obtain ⟨root,usable⟩ := generation name needed
    obtain ⟨other,recorded,_⟩ := usable.1.2 _ member rfl
    cases recorded

theorem aligned_position {queries : List α} {terms : List β} (aligned : Aligned relation queries terms)
    (length : queries.length = terms.length) (index : Fin queries.length) :
    relation queries[index] (terms[index.val]'(by rw [← length]; exact index.isLt)) := by
  induction aligned with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
    cases index with
    | mk i bounded => cases i with
      | zero => exact first
      | succ i => exact ih (Nat.add_right_cancel length) ⟨i,Nat.lt_of_succ_lt_succ bounded⟩

theorem list_ofFn (values : List α) (length : values.length = count) :
    (List.ofFn (fun index : Fin count => values[index.val]'(by rw [length]; exact index.isLt))) = values := by
  apply List.ext_getElem
  · simp [length]
  · intro index one two; simp


theorem zip_reindex {first last shape : GeneralNormalizedObservation.Shape}
    (one : first = shape) (two : last = shape) (lower : Fin first.arity → α) (upper : Fin last.arity → β) :
    (List.ofFn lower).zip (List.ofFn upper) = List.ofFn (fun index : Fin shape.arity =>
      (GeneralNominalFiniteBracket.reindex one lower index,GeneralNominalFiniteBracket.reindex two upper index)) := by
  subst first; subst last
  apply List.ext_getElem
  · simp
  · intro index one two
    simp only [GeneralNominalFiniteBracket.reindex,List.getElem_zip,List.getElem_ofFn]

theorem structural_inputs (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (known : Input context model state bounds origin term) :
    ∃ children : Fin shape.arity → Expr Nat, term = .node (.structural shape) children ∧
      InputsAt context model state (fun index => origin.map fun parent => .structural parent shape index) 0
        ((List.ofFn lower).zip (List.ofFn upper)) (List.ofFn children) := by
  obtain ⟨⟨pattern,closed⟩,contained,retained⟩ := known
  obtain ⟨children,equal,fits⟩ := GeneralNominalFiniteBracket.structural_interval state model valid bounds
    lowerKind upperKind lower upper lowerAt upperAt lowerShape upperShape term closed.2.1 closed.2.2 contained
  refine ⟨children,equal,?_⟩
  rw [equal] at closed retained
  rw [zip_reindex lowerShape upperShape]
  apply inputs_at _ _ (by simp)
  intro index
  let position : Fin shape.arity := ⟨index.val,by simpa only [List.length_ofFn] using index.isLt⟩
  simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
  refine ⟨closed_child closed position,fits position,?_⟩
  exact retained_child retained closed.2.2 position

theorem nominal_inputs (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals bounds.1 = some descriptor)
    {intervals : List (Bounds state)} (found : typeArguments descriptor.arguments = some intervals)
    (known : Input context model state bounds origin term) :
    ∃ children : Fin intervals.length → Expr Nat, term = .node (.nominal descriptor.declaration.name intervals.length) children ∧
      InputsAt context model state
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) descriptor.declaration.name index)) 0
        intervals (List.ofFn children) := by
  obtain ⟨⟨pattern,closed⟩,contained,retained⟩ := known
  obtain ⟨children,equal,endpoint,fits⟩ := GeneralNominalInspectionFiniteValues.descriptor_finite state model valid bounds.1
    descriptor recorded found term closed.2.1 contained.1
  refine ⟨children,equal,?_⟩
  rw [equal] at closed retained endpoint
  have parent : At model .actual (origin.getD (.source (state.base.source bounds.1)))
      (denote (fun _ => .bottom) (.node (.nominal descriptor.declaration.name intervals.length) children)) := by
    cases origin with
    | none => exact endpoint
    | some root => exact retained root rfl
  apply inputs_at _ _ (List.length_ofFn ..)
  intro index
  simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
  refine ⟨closed_child closed index,fits index,?_⟩
  intro root recorded
  cases Option.some.inj recorded
  exact project_value (.nominal descriptor.declaration.name intervals.length) trivial _ parent index

theorem structural_matched {shape : GeneralNormalizedObservation.Shape}
    {children : Fin (arity (.structural shape)) → Expr Nat} {queries : List Query}
    (matched : Aligned (Matches relation) queries (List.ofFn children))
    (length : queries.length = shape.arity) :
    Matches relation (.node shape queries) (.node (.structural shape) children) := by
  have all : ∀ index : Fin shape.arity,
      Matches relation (queries[index.val]'(by rw [length]; exact index.isLt)) (children index) := by
    intro index
    have atIndex := aligned_position matched (by simp only [List.length_ofFn,length,arity]) ⟨index.val,by rw [length]; exact index.isLt⟩
    simpa only [Fin.getElem_fin,List.getElem_ofFn,GeneralNominalOriginTerms.arity] using atIndex
  have result := Matches.structural shape _ children all
  rw [list_ofFn queries length] at result
  exact result

theorem nominal_matched {children : Fin (arity (.nominal name count)) → Expr Nat} {queries : List Query}
    (matched : Aligned (Matches relation) queries (List.ofFn children))
    (length : queries.length = count) :
    Matches relation (.nominal name queries) (.node (.nominal name count) children) := by
  have all : ∀ index : Fin count,
      Matches relation (queries[index.val]'(by rw [length]; exact index.isLt)) (children index) := by
    intro index
    have atIndex := aligned_position matched (by simp only [List.length_ofFn,length,arity]) ⟨index.val,by rw [length]; exact index.isLt⟩
    simpa only [Fin.getElem_fin,List.getElem_ofFn,GeneralNominalOriginTerms.arity] using atIndex
  have result := Matches.nominal name count _ children all
  rw [list_ofFn queries length] at result
  exact result


theorem both_nominal_inputs (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (lower upper : GeneralNominalState.Descriptor state.base.slots)
    (lowerAt : state.nominals bounds.1 = some lower) (upperAt : state.nominals bounds.2 = some upper)
    {left right : List (Bounds state)}
    (leftAt : typeArguments lower.arguments = some left) (rightAt : typeArguments upper.arguments = some right)
    (known : Input context model state bounds origin term) :
    (∃ children : Fin left.length → Expr Nat, term = .node (.nominal lower.declaration.name left.length) children ∧
      InputsAt context model state
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) lower.declaration.name index)) 0
        left (List.ofFn children)) ∧
    (∃ children : Fin right.length → Expr Nat, term = .node (.nominal upper.declaration.name right.length) children ∧
      InputsAt context model state
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.2))) upper.declaration.name index)) 0
        right (List.ofFn children)) := by
  refine ⟨nominal_inputs state model valid bounds lower lowerAt leftAt known,?_⟩
  obtain ⟨xs,_,one⟩ := valid.2.1 bounds.1 lower lowerAt
  obtain ⟨ys,_,two⟩ := valid.2.1 bounds.2 upper upperAt
  have equal := GeneralNominalIntervalLaws.nominal_sandwich lower.declaration.name upper.declaration.name xs ys
    (denote (fun _ => .bottom) term)
    (CommonNominalFullCarrier.subtype_trans one.2 known.2.1.1)
    (CommonNominalFullCarrier.subtype_trans known.2.1.2 two.1)
  have upperKnown : Input context model state (bounds.2,bounds.2) origin term :=
    ⟨known.1,⟨CommonNominalFullCarrier.subtype_trans two.1 equal.2.2,known.2.1.2⟩,known.2.2⟩
  exact nominal_inputs state model valid (bounds.2,bounds.2) upper upperAt rightAt upperKnown

end Yulang.GeneralNominalInspectionPositions
