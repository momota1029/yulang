import Yulang.GeneralDeclarativeI65SelectedWhereBindings395

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Equation)
open CommonRecursiveNominalIntervals (Bounds Endpoint Argument childContext effectiveParameter)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)

-- Prototype only: symbolic source data, not an inference algorithm or
-- a rule for missing data. Semantic soundness of these annotations and
-- source coverage belong to B6. Mixed .declared wire is not chosen.
mutual
inductive B6ValuePlan398 (s : State) : Bool → Pattern → Type where
  | binder (n : Nat) : B6ValuePlan398 s context (.var n)
  | record (label : Nat) :
      B6ValuePlan398 s context payload → B6ValuePlan398 s context tail →
      B6ValuePlan398 s context (.record label payload tail)
  | variant (tag : Nat) : B6ValuePlan398 s context payload →
      B6ValuePlan398 s context (.variant tag payload)
  | join : B6ValuePlan398 s context first → B6ValuePlan398 s context last →
      B6ValuePlan398 s context (.join first last)
  | declaredApp (name : Nat) (use : Use s.current.environment name pats.length) :
      names use.mode pats.length = some parameters →
      s.modes[name]? = some parameters →
      B6ArgPlans398 s context parameters pats →
      B6ValuePlan398 s context (.app name pats)

inductive B6ArgPlan398 (s : State) : Bool → Parameter → Pattern → Type where
  | valuePoint (name : Nat) : param.kind = .value →
      (effectiveParameter context param).variance ≠ .invariant →
      B6ArgPlan398 s context param (.var name)
  | valueInterval (name : Nat) : param.kind = .value →
      (effectiveParameter context param).variance = .invariant →
      B6ArgPlan398 s context param (.var name)
  | rowPoint (name : Nat) : param.kind = .row →
      (effectiveParameter context param).variance ≠ .invariant →
      B6ArgPlan398 s context param (.var name)
  | rowInterval (name : Nat) : param.kind = .row →
      (effectiveParameter context param).variance = .invariant →
      B6ArgPlan398 s context param (.var name)
  | valueTree : param.kind = .value → (∀ n, p ≠ .var n) →
      B6ValuePlan398 s (childContext context param) p →
      B6ArgPlan398 s context param p

inductive B6ArgPlans398 (s : State) : Bool →
    List Parameter → List Pattern → Type where
  | nil : B6ArgPlans398 s context [] []
  | cons : B6ArgPlan398 s context p x → B6ArgPlans398 s context ps xs →
      B6ArgPlans398 s context (p::ps) (x::xs)
end

abbrev ExactRoleRhs398 (p : Pattern) := { code : SourceRhsCode394 // code.source = p }
abbrev ExactRoleArg398 (p : Pattern) := { code : SourceRhsArg394 // code.source = p }
abbrev ExactRoleArgs398 (ps : List Pattern) :=
  { codes : List SourceRhsArg394 // sourceArgList394 codes = ps }

mutual
/-- B4 substitutes named logical slots into the provided symbolic kind
structure. It does not ask a model, solve an expression type, or guess
whether a reference is a row. This does not define .declared wire. -/
def instantiateB6Value398 (slots : Nat → Option Capture) {s context p}
    (plan : B6ValuePlan398 s context p) : Option (ExactRoleRhs398 p) :=
  match plan with
  | .binder name => do
    let bound ← slots name
    pure ⟨.variable name bound.center,rfl⟩
  | .record label first last => do
    let a ← instantiateB6Value398 slots first
    let b ← instantiateB6Value398 slots last
    pure ⟨.record label a.val b.val,by simp only [SourceRhsCode394.source,a.2,b.2]⟩
  | .variant tag payload => do
    let a ← instantiateB6Value398 slots payload
    pure ⟨.variant tag a.val,by simp only [SourceRhsCode394.source,a.2]⟩
  | .join first last => do
    let a ← instantiateB6Value398 slots first
    let b ← instantiateB6Value398 slots last
    pure ⟨.join a.val b.val,by simp only [SourceRhsCode394.source,a.2,b.2]⟩
  | .declaredApp name _ _ _ args => do
    let a ← instantiateB6Args398 slots args
    pure ⟨.nominal name a.val,by simp only [SourceRhsCode394.source,a.2]⟩

def instantiateB6Arg398 (slots : Nat → Option Capture) {s context param p}
    (plan : B6ArgPlan398 s context param p) : Option (ExactRoleArg398 p) :=
  match plan with
  | .valuePoint name _ _ => do
    let c ← slots name
    pure ⟨.valueSlot name (.point (.ordinary (.var c.center))),rfl⟩
  | .valueInterval name _ _ => do
    let c ← slots name
    pure ⟨.valueSlot name (.interval (.ordinary (.var c.lower)) (.ordinary (.var c.upper))),rfl⟩
  | .rowPoint name _ _ => do
    let c ← slots name
    pure ⟨.rowSlot name (.point (.var c.center)),rfl⟩
  | .rowInterval name _ _ => do
    let c ← slots name
    pure ⟨.rowSlot name (.interval (.var c.lower) (.var c.upper)),rfl⟩
  | .valueTree _ _ child => do
    let p ← instantiateB6Value398 slots child
    pure ⟨.valueExpression p.val, p.2⟩

def instantiateB6Args398 (slots : Nat → Option Capture) {s context parameters ps}
    (plan : B6ArgPlans398 s context parameters ps) : Option (ExactRoleArgs398 ps) :=
  match plan with
  | .nil => some ⟨[],rfl⟩
  | .cons head tail => do
    let a ← instantiateB6Arg398 slots head
    let b ← instantiateB6Args398 slots tail
    pure ⟨a.val::b.val,by simp only [sourceArgList394,a.2,b.2]⟩
end

-- The atlas cannot see the selected request, a dictionary, an actual
-- generated output, or a prepared frame. The default key names the
-- *role's* original body, not an explicit selected declaration.
structure B6SymbolicAtlas398 (s : State) where
  explicit : (sourceOrdinal : Nat) → (eq : Equation) →
    Option (B6ValuePlan398 s false (normalize (bodyPattern (.explicit eq))))
  roleDefault : (role assocName : Nat) → (original : Roles.Term) →
    Option (B6ValuePlan398 s false (normalize (bodyPattern (.default role assocName original))))

def B6SymbolicAtlas398.read {s} (atlas : B6SymbolicAtlas398 s) (declarationOrdinal : Nat)
    (body : Body) : Option (B6ValuePlan398 s false (normalize (bodyPattern body))) :=
  match body with
  | .explicit eq => atlas.explicit declarationOrdinal eq
  | .default role name rhs => atlas.roleDefault role name rhs

structure LogicalRoleOutput398 {s q} (frame : AuthoredBodyFrame393 s q)
    (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles frame.decl q.demand.outputs[i].name body
  rhs : ExactRoleRhs398 (normalize (bodyPattern body))

def logicalOutputAt398 {s q} (frame : AuthoredBodyFrame393 s q)
    (atlas : B6SymbolicAtlas398 s) (i : Fin q.demand.outputs.length)
    (wf : (frame.decl.associated.map Equation.name).Nodup) :
    Option (LogicalRoleOutput398 frame i) :=
  let roles := (authoredRegistry s.current).roles
  let request := q.demand.outputs[i]
  match found : lookup roles frame.decl request.name with
  | none => none
  | some b => do
    let typed ← atlas.read frame.ordinal b
    let value ← instantiateB6Value398 (frame.slots b) typed
    pure ⟨b,(lookup_exact roles frame.decl wf request.name b).mp found,value⟩

def LogicalRoleOutput398.equation {s q frame i}
    (out : LogicalRoleOutput398 (s := s) (q := q) frame i) : CompoundEquation394 :=
  ⟨q.occurrence,i.val,q.demand.outputs[i],out.body,out.rhs.val⟩

theorem original_logical_output_scope398 {s q frame i}
    (out : LogicalRoleOutput398 (s := s) (q := q) frame i) :
    out.equation.occurrence = q.occurrence ∧
      out.equation.ordinal = i.val ∧
      q.demand.outputs[i.val]? = some out.equation.requested ∧
      out.equation.requested.target = q.demand.outputs[i].target ∧
      Supplies (authoredRegistry s.current).roles frame.decl
        out.equation.requested.name out.equation.originalBody ∧
      out.equation.rhs.source = normalize (bodyPattern out.equation.originalBody) :=
  ⟨rfl,rfl,List.getElem?_eq_getElem i.isLt,rfl,out.supplied,out.rhs.property⟩

/-- Never filter an unsupported cell out of the sequence: the
post-merge request's original output ordinal is authoritative. -/
def logicalOutputsInOrder398 {s q} (frame : AuthoredBodyFrame393 s q)
    (atlas : B6SymbolicAtlas398 s)
    (wf : (frame.decl.associated.map Equation.name).Nodup) :
    List (Option CompoundEquation394) :=
  List.ofFn fun i => (logicalOutputAt398 frame atlas i wf).map LogicalRoleOutput398.equation

theorem logical_output_length398 {s q} (f : AuthoredBodyFrame393 s q)
    (atlas : B6SymbolicAtlas398 s) (wf : (f.decl.associated.map Equation.name).Nodup) :
    (logicalOutputsInOrder398 f atlas wf).length = q.demand.outputs.length := by
  simp [logicalOutputsInOrder398]

theorem logical_output_at_original_position398 {s q} (f : AuthoredBodyFrame393 s q)
    (atlas : B6SymbolicAtlas398 s) (wf : (f.decl.associated.map Equation.name).Nodup)
    (i : Fin q.demand.outputs.length) :
    (logicalOutputsInOrder398 f atlas wf)[i.val]? =
      some ((logicalOutputAt398 f atlas i wf).map LogicalRoleOutput398.equation) := by
  simp [logicalOutputsInOrder398,i.isLt]

/-- The default b6 scheme's variable indexes the actual original
role argument and its centre, never the explicit binder at that number. -/
theorem positional_default_reads_original_center398 {s q} (f : AuthoredBodyFrame393 s q)
    (role name : Nat) (rhs : Roles.Term) (index : Nat) {actual : Capture}
    (named : q.demand.arguments[index]? = some actual) :
    (instantiateB6Value398 (f.slots (.default role name rhs))
        (B6ValuePlan398.binder (s := s) (context := false) index)).map Subtype.val =
      some (.variable index actual.center) := by
  simp [AuthoredBodyFrame393.slots,instantiateB6Value398,named]

/-- If the B6 source input at a where binder is an invariant value
argument, both literal bounds refer to the actual named child output.
Using a same-name point does not change the interval constructor. -/
theorem typed_where_interval_reads_actual_output398 {s q f binder body context param}
    (edge : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (kind : param.kind = .value)
    (invariant : (effectiveParameter context param).variance = .invariant) :
    (instantiateB6Arg398 (f.slots (.explicit body))
        (B6ArgPlan398.valueInterval (s := s) binder.name kind invariant)).map Subtype.val =
      some (.valueSlot binder.name
        (.interval (.ordinary (.var edge.output.target)) (.ordinary (.var edge.output.target)))) := by
  simp [instantiateB6Arg398,edge.slot]

/-- B6 annotations do not pick explicit versus default or the
ordered output site. Two successful atlas reads may carry different
annotations, but cannot change the original supplier or location. -/
theorem source_supplier_cannot_be_changed_by_typing_input398 {s q f i}
    (unique : (f.decl.associated.map Equation.name).Nodup)
    (first last : LogicalRoleOutput398 (s := s) (q := q) f i) :
    first.body = last.body ∧
      first.equation.occurrence = last.equation.occurrence ∧
      first.equation.ordinal = last.equation.ordinal ∧
      first.equation.requested = last.equation.requested := by
  refine ⟨?_,rfl,rfl,rfl⟩
  exact GeneralDictionaryAssociatedProvenance.supplies_unique _ _ unique _ _ _ first.supplied last.supplied

/-- If the actual explicit source is already selected, absent
typing metadata does not cause a retry on the role default.
The none here is an unrepresented source output, not rejection. -/
theorem failed_explicit_annotation_has_no_default_fallback398 {s q}
    (f : AuthoredBodyFrame393 s q) (atlas : B6SymbolicAtlas398 s)
    (i : Fin q.demand.outputs.length) (unique : (f.decl.associated.map Equation.name).Nodup)
    (eq : Equation) (attached : eq ∈ f.decl.associated)
    (declaredName : eq.name = (q.demand.outputs[i]).name)
    (unchecked : atlas.explicit f.ordinal eq = none) :
    logicalOutputAt398 f atlas i unique = none := by
  have requested : lookup (authoredRegistry s.current).roles f.decl
      (q.demand.outputs[i]).name = some (.explicit eq) :=
    (lookup_exact _ _ unique _ _).mpr (.explicit eq attached declaredName)
  unfold logicalOutputAt398
  dsimp only
  split
  · rfl
  next b found =>
    rw [requested] at found
    injection found with eqb
    subst b
    simp [B6SymbolicAtlas398.read,unchecked]

/-- Conservative comparison only: every old represented typed RHS
has an exactly replaying symbolic plan on the same real slots. This
does not implement B6 or lower a mixed RHS to the C386 wire. -/
theorem legacy_source_has_exact_symbolic_replay398 {s slots context p code}
    (old : CompoundSourceRhs394 s slots context p code) :
    ∃ plan : B6ValuePlan398 s context p,
      ∃ result, instantiateB6Value398 slots plan = some result ∧ result.val = code := by
  exact CompoundSourceRhs394.rec
    (motive_1 := fun c p out _ => ∃ plan : B6ValuePlan398 s c p,
      ∃ result, instantiateB6Value398 slots plan = some result ∧ result.val = out)
    (motive_2 := fun c ps pts out _ => ∃ plan : B6ArgPlans398 s c ps pts,
      ∃ result, instantiateB6Args398 slots plan = some result ∧ result.val = out)
    (motive_3 := fun c param p out _ => ∃ plan : B6ArgPlan398 s c param p,
      ∃ result, instantiateB6Arg398 slots plan = some result ∧ result.val = out)
    (fun atSlot _ => ⟨.binder _,_,by simp [instantiateB6Value398,atSlot] <;> rfl,rfl⟩)
    (fun _ _ left right => by
      obtain ⟨p,a,read,code⟩ := left
      obtain ⟨q,b,read',code'⟩ := right
      exact ⟨.record _ p q,_,by simp [instantiateB6Value398,read,read'] <;> rfl,by simp only [code,code']⟩)
    (fun _ body => by
      obtain ⟨p,a,read,code⟩ := body
      exact ⟨.variant _ p,_,by simp [instantiateB6Value398,read] <;> rfl,by simp only [code]⟩)
    (fun _ _ left right => by
      obtain ⟨p,a,read,code⟩ := left
      obtain ⟨q,b,read',code'⟩ := right
      exact ⟨.join p q,_,by simp [instantiateB6Value398,read,read'] <;> rfl,by simp only [code,code']⟩)
    (fun use written table _ body => by
      obtain ⟨p,a,read,code⟩ := body
      exact ⟨.declaredApp _ use written table p,_,by simp [instantiateB6Value398,read] <;> rfl,by simp only [code]⟩)
    ⟨.nil,_,rfl,rfl⟩
    (fun _ _ first rest => by
      obtain ⟨p,a,read,code⟩ := first
      obtain ⟨q,b,read',code'⟩ := rest
      exact ⟨.cons p q,_,by simp [instantiateB6Args398,read,read'] <;> rfl,by simp only [code,code']⟩)
    (fun kind mode atSlot _ =>
      ⟨.valuePoint _ kind mode,_,by simp [instantiateB6Arg398,atSlot] <;> rfl,rfl⟩)
    (fun kind mode atSlot _ =>
      ⟨.valueInterval _ kind mode,_,by simp [instantiateB6Arg398,atSlot] <;> rfl,rfl⟩)
    (fun kind mode atSlot _ =>
      ⟨.rowPoint _ kind mode,_,by simp [instantiateB6Arg398,atSlot] <;> rfl,rfl⟩)
    (fun kind mode atSlot _ =>
      ⟨.rowInterval _ kind mode,_,by simp [instantiateB6Arg398,atSlot] <;> rfl,rfl⟩)
    (fun kind nonvariable _ body => by
      obtain ⟨p,a,read,code⟩ := body
      exact ⟨.valueTree kind nonvariable p,_,by simp [instantiateB6Arg398,read] <;> rfl,by simp only [code]⟩)
    old

mutual
def B6ValuePlan398.needs {s c p} : B6ValuePlan398 s c p → List (Nat × CommonDeclaredNominalInspection.Kind)
  | .binder n => [(n,.value)]
  | .record _ a b => a.needs ++ b.needs
  | .variant _ a => a.needs
  | .join a b => a.needs ++ b.needs
  | .declaredApp _ _ _ _ a => a.needs

def B6ArgPlan398.needs {s c param p} :
    B6ArgPlan398 s c param p → List (Nat × CommonDeclaredNominalInspection.Kind)
  | .valuePoint n _ _ => [(n,.value)]
  | .valueInterval n _ _ => [(n,.value)]
  | .rowPoint n _ _ => [(n,.row)]
  | .rowInterval n _ _ => [(n,.row)]
  | .valueTree _ _ a => a.needs

def B6ArgPlans398.needs {s c params ps} :
    B6ArgPlans398 s c params ps → List (Nat × CommonDeclaredNominalInspection.Kind)
  | .nil => []
  | .cons a b => a.needs ++ b.needs
end

def B6UsesFit398 (s : State) (slots : Nat → Option Capture)
    (used : List (Nat × CommonDeclaredNominalInspection.Kind)) : Prop :=
  ∀ x ∈ used, ∃ a, slots x.1 = some a ∧ TypedBodyCapture392 s a x.2

private theorem left_B6UsesFit398 {s slots a b} (fit : B6UsesFit398 s slots (a ++ b)) :
    B6UsesFit398 s slots a := fun _ member => fit _ (List.mem_append.mpr (.inl member))

private theorem right_B6UsesFit398 {s slots a b} (fit : B6UsesFit398 s slots (a ++ b)) :
    B6UsesFit398 s slots b := fun _ member => fit _ (List.mem_append.mpr (.inr member))

/-- When independent kind compatibility holds at the exact slots,
the plan's logical evaluation is the preexisting C394 source relation.
Neither this premise nor this relation changes source eligibility. -/
theorem symbolic_replay_meaning_with_supplied_capture_kinds398 {s slots context p}
    (plan : B6ValuePlan398 s context p)
    (fit : B6UsesFit398 s slots plan.needs) :
    ∃ out, instantiateB6Value398 slots plan = some out ∧
      CompoundSourceRhs394 s slots context p out.val := by
  refine B6ValuePlan398.rec
    (motive_1 := fun c p a => B6UsesFit398 s slots a.needs →
      ∃ out, instantiateB6Value398 slots a = some out ∧ CompoundSourceRhs394 s slots c p out.val)
    (motive_2 := fun c param p a => B6UsesFit398 s slots a.needs →
      ∃ out, instantiateB6Arg398 slots a = some out ∧ CompoundSourceArg394 s slots c param p out.val)
    (motive_3 := fun c params ps a => B6UsesFit398 s slots a.needs →
      ∃ out, instantiateB6Args398 slots a = some out ∧ CompoundSourceArgs394 s slots c params ps out.val)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan fit
  · intro c j h
    obtain ⟨a,read,typed⟩ := h (j,.value) (by simp [B6ValuePlan398.needs])
    exact ⟨_,by simp [instantiateB6Value398,read] <;> rfl,.variable read typed⟩
  · intro c p q tag a b left right h
    obtain ⟨readA,okA,meaningA⟩ := left (left_B6UsesFit398 h)
    obtain ⟨readB,okB,meaningB⟩ := right (right_B6UsesFit398 h)
    exact ⟨_,by simp [instantiateB6Value398,okA,okB] <;> rfl,.record meaningA meaningB⟩
  · intro c p tag a ih h
    obtain ⟨out,read,meaning⟩ := ih h
    exact ⟨_,by simp [instantiateB6Value398,read] <;> rfl,.variant meaning⟩
  · intro c p q a b left right h
    obtain ⟨readA,okA,meaningA⟩ := left (left_B6UsesFit398 h)
    obtain ⟨readB,okB,meaningB⟩ := right (right_B6UsesFit398 h)
    exact ⟨_,by simp [instantiateB6Value398,okA,okB] <;> rfl,.join meaningA meaningB⟩
  · intro params c ps name use declared table a ih h
    obtain ⟨out,read,meaning⟩ := ih h
    exact ⟨_,by simp [instantiateB6Value398,read] <;> rfl,.nominal use declared table meaning⟩
  · intro c param j kind mode h
    obtain ⟨a,read,typed⟩ := h (j,.value) (by simp [B6ArgPlan398.needs])
    exact ⟨_,by simp [instantiateB6Arg398,read] <;> rfl,.pointValue kind mode read typed⟩
  · intro c param j kind mode h
    obtain ⟨a,read,typed⟩ := h (j,.value) (by simp [B6ArgPlan398.needs])
    exact ⟨_,by simp [instantiateB6Arg398,read] <;> rfl,.intervalValue kind mode read typed⟩
  · intro c param j kind mode h
    obtain ⟨a,read,typed⟩ := h (j,.row) (by simp [B6ArgPlan398.needs])
    exact ⟨_,by simp [instantiateB6Arg398,read] <;> rfl,.pointRow kind mode read typed⟩
  · intro c param j kind mode h
    obtain ⟨a,read,typed⟩ := h (j,.row) (by simp [B6ArgPlan398.needs])
    exact ⟨_,by simp [instantiateB6Arg398,read] <;> rfl,.intervalRow kind mode read typed⟩
  · intro p c param kind notVar a ih h
    obtain ⟨out,read,meaning⟩ := ih h
    exact ⟨_,by simp [instantiateB6Arg398,read] <;> rfl,.valueExpression kind notVar meaning⟩
  · intro c _
    exact ⟨_,rfl,.nil⟩
  · intro c param p params ps a b left right h
    obtain ⟨readA,okA,meaningA⟩ := left (left_B6UsesFit398 h)
    obtain ⟨readB,okB,meaningB⟩ := right (right_B6UsesFit398 h)
    exact ⟨_,by simp [instantiateB6Args398,okA,okB] <;> rfl,.cons meaningA meaningB⟩

/-- A covered source body already supplied by the original declaration
is substituted at the original output ordinal. The premises concern
that same B6 plan and the actual frame reads, not an inferred model.
This is a logical receipt; it does not choose a mixed literal wire. -/
theorem supplied_symbolic_body_produces_exact_logical_output398 {s q}
    (f : AuthoredBodyFrame393 s q) (atlas : B6SymbolicAtlas398 s)
    (i : Fin q.demand.outputs.length) (unique : (f.decl.associated.map Equation.name).Nodup)
    {b : Body}
    (origin : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name b)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern b))}
    (annotation : atlas.read f.ordinal b = some plan)
    (compatible : B6UsesFit398 s (f.slots b) plan.needs) :
    ∃ out : LogicalRoleOutput398 f i, logicalOutputAt398 f atlas i unique = some out ∧
      out.body = b ∧ out.equation.requested.target = q.demand.outputs[i].target ∧
      CompoundSourceRhs394 s (f.slots b) false (normalize (bodyPattern b)) out.equation.rhs := by
  obtain ⟨rhs,replayed,meaning⟩ := symbolic_replay_meaning_with_supplied_capture_kinds398 plan compatible
  let result : LogicalRoleOutput398 f i := ⟨b,origin,rhs⟩
  refine ⟨result,?_,rfl,rfl,meaning⟩
  have looked : lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some b :=
    (lookup_exact _ _ unique _ _).mpr origin
  unfold logicalOutputAt398
  dsimp only
  split
  next notFound => rw [looked] at notFound; contradiction
  next body hit =>
    rw [looked] at hit
    injection hit with same
    subst body
    simp [annotation,replayed,result]

end Yulang.GeneralDeclarativeI65
