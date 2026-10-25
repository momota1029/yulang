import YulangClosure.PaperTypeFormation

/-!
Raw objects for the paper's execution typing judgments.  This module is the
syntax layer only; the rule-to-constructor coverage and known omissions are
tracked in `tasks/agent-loop/inbox/paper-typing-subst.md`.
-/
namespace YulangClosure.PaperTypes

abbrev TermName := Nat
abbrev OwnerName := Nat
abbrev DeclarationId := Nat
abbrev Label := Nat

inductive EntryMode where
  | value | computation

inductive Literal where
  | unit
  | boolean (value : Bool)
  | integer (value : Int)
  | floatBits (bits : Nat)
  | string (value : String)
  | bytes (value : List Nat)
  | path (value : String)
  | character (grapheme : String)

inductive Failure where
  | matchFailure | divideByZero | boundsError | unimplemented

inductive ViewMetadata where
  | mk (identity : Nat) (sourceType targetType : Ty) (typeArguments : List Ty)

inductive AdapterMetadata where
  | mk (identity : Nat) (sourceType targetType : Ty)

mutual
  inductive Value where
    | variable (index : Nat)
    | graphReference (identity : Nat)
    | literal (literal : Literal)
    | tuple (elements : List Value)
    | sequence (elements : List Value)
    | record (fields : List (Label × Presence × Value))
    | variant (constructor : DeclarationId) (typeArguments : List Ty)
        (payload : List Value)
    | nominal (constructor : DeclarationId) (typeArguments : List Ty)
        (payload : List Value)
    | lambda (mode : EntryMode) (profile : AdapterMetadata) (parameter : TermName)
        (body : Computation)
    | delay (body : Computation)
    | wrap (function : Value) (argumentAdapter resultAdapter : Computation)
    | typeAbstraction (body : Value)
    | typeApplication (function : Value) (typeArgument : Ty)
    | injectLeft (value : Value)
    | injectRight (value : Value)
    | both (value : Value)
    | roll (value : Value)
    | topView (value : Value)
    | view (metadata : ViewMetadata) (value : Value)
    | continuation (ownerBinders : List OwnerName) (responseBinder : TermName)
        (body : Computation)

  inductive Computation where
    | ret (value : Value)
    | letE (first : Computation) (body : Computation)
    | force (thunk : Value)
    | call (function thunk : Value)
    | resume (continuation response : Value)
    | split (tuple : Value) (binders : List TermName) (body : Computation)
    | field (record : Value) (label : Label)
    | lookup (record : Value) (label : Label)
    | switch (value : Value) (branches : List ConstructorBranch)
    | unroll (value : Value)
    | choose (value : Value) (side : Bool)
    | unionCase (value : Value) (leftBinder : TermName) (left : Computation)
        (rightBinder : TermName) (right : Computation)
    | absurd (value : Value)
    | primitive (identity : Nat) (arguments : List Value)
    | perform (operation : DeclarationId) (typeArguments : List Ty) (payload : Value)
    | handle (body : Computation) (handler : HandlerPlan)
    | mapOperation (body : Computation) (mapper : MapperPlan)
    | recursive (bindings : List (TermName × Value)) (body : Computation)
    | template (identity : Nat) (typeArguments : List Ty) (arguments : List Value)
    | fail (reason : Failure)
    | request (opInstance : OperationInstance) (payload : Value) (continuation : Value)
    | scope (owner : OwnerName) (body : Computation)
    | expose (metadata : ViewMetadata) (body : Computation)
    | enter (owner : OwnerName) (function thunk : Value)
    | tryArms (handler : HandlerPlan) (opInstance : OperationInstance)
        (payload continuation : Value) (arms : List OperationArm)
    | waitArm (handler : HandlerPlan) (opInstance : OperationInstance)
        (payload continuation : Value) (arm : OperationArm)
        (remaining : List OperationArm) (attempt : Computation)

  inductive PatternPlan where
    | wild
    | variable (binder : TermName)
    | literal (literal : Literal)
    | tuple (children : List PatternPlan)
    | list (prefixPatterns : List PatternPlan) (restBinder : Option TermName)
        (suffix : List PatternPlan)
    | record (fields : List (Label × PatternPlan × Option Computation))
        (spreadBinder : Option TermName)
    | polyVariant (tag : DeclarationId) (payload : List PatternPlan)
    | constructor (identity : DeclarationId) (typeArguments : List Ty)
        (payload : List PatternPlan)
    | reference (definition : Value) (equality : Computation)
    | asPattern (child : PatternPlan) (binder : TermName)
    | orPattern (left right : PatternPlan) (mergeBinders : List TermName)

  inductive ConstructorBranch where
    | mk (identity : DeclarationId) (binders : List TermName) (body : Computation)

  inductive GuardedBranch where
    | mk (pattern : PatternPlan) (guard : Option Computation) (body : Computation)

  inductive ValueArm where
    | mk (branch : GuardedBranch)

  inductive OperationArm where
    | mk (operation : DeclarationId) (rigidTypeBinders : Nat)
        (payloadPattern : PatternPlan) (continuationBinder : TermName)
        (guard : Option Computation) (body : Computation)

  inductive HandlerPlan where
    | mk (inputType outputType : Ty) (valueArms : List ValueArm)
        (operationArms : List OperationArm)

  inductive MapperPlan where
    | mk (source target : OperationInstance) (payloadAdapter responseAdapter : Computation)

  inductive TemplateBody where
    | mk (identity : Nat) (typeArity : Nat) (formals : List Ty)
        (result : Ty) (body : Computation)
end

def mapTypeArguments (σ : Nat → Ty) (arguments : List Ty) : List Ty :=
  arguments.map (subst σ)

def mapViewMetadata (σ : Nat → Ty) : ViewMetadata → ViewMetadata
  | .mk identity source target arguments =>
      .mk identity (subst σ source) (subst σ target) (mapTypeArguments σ arguments)

def mapAdapterMetadata (σ : Nat → Ty) : AdapterMetadata → AdapterMetadata
  | .mk identity source target => .mk identity (subst σ source) (subst σ target)

private theorem sizeOfRecordValue_le (field : Label × Presence × Value) :
    sizeOf field.2.2 ≤ sizeOf field := by
  rcases field with ⟨label, presence, value⟩
  simp +arith

private theorem sizeOfBindingValue_le (binding : TermName × Value) :
    sizeOf binding.2 ≤ sizeOf binding := by
  rcases binding with ⟨name, value⟩
  simp +arith

private theorem sizeOfPatternField_le (field : Label × PatternPlan × Option Computation) :
    sizeOf field.2.1 ≤ sizeOf field := by
  rcases field with ⟨label, pattern, default⟩
  simp +arith

private theorem sizeOfPatternDefault_le (field : Label × PatternPlan × Option Computation)
    (body : Computation) (h : field.2.2 = some body) :
    sizeOf body ≤ sizeOf field := by
  rcases field with ⟨label, pattern, default⟩
  simp_all +arith

mutual
  def mapPaperValue (σ : Nat → Ty) : Value → Value
    | .variable index => .variable index
    | .graphReference identity => .graphReference identity
    | .literal literal => .literal literal
    | .tuple values => .tuple (values.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .sequence values => .sequence (values.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .record fields => .record (fields.attach.map fun ⟨field, hmem⟩ =>
        (field.1, field.2.1, mapPaperValue σ field.2.2))
    | .variant constructor arguments payload =>
        .variant constructor (mapTypeArguments σ arguments)
          (payload.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .nominal constructor arguments payload =>
        .nominal constructor (mapTypeArguments σ arguments)
          (payload.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .lambda mode profile parameter body =>
        .lambda mode (mapAdapterMetadata σ profile) parameter (mapPaperComputation σ body)
    | .delay body => .delay (mapPaperComputation σ body)
    | .wrap function argumentAdapter resultAdapter =>
        .wrap (mapPaperValue σ function) (mapPaperComputation σ argumentAdapter)
          (mapPaperComputation σ resultAdapter)
    | .typeAbstraction body => .typeAbstraction (mapPaperValue (liftSub σ) body)
    | .typeApplication function argument => .typeApplication (mapPaperValue σ function) (subst σ argument)
    | .injectLeft value => .injectLeft (mapPaperValue σ value)
    | .injectRight value => .injectRight (mapPaperValue σ value)
    | .both value => .both (mapPaperValue σ value)
    | .roll value => .roll (mapPaperValue σ value)
    | .topView value => .topView (mapPaperValue σ value)
    | .view metadata value => .view (mapViewMetadata σ metadata) (mapPaperValue σ value)
    | .continuation owners binder body =>
        .continuation owners binder (mapPaperComputation σ body)
  termination_by value => sizeOf value
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapPaperComputation (σ : Nat → Ty) : Computation → Computation
    | .ret value => .ret (mapPaperValue σ value)
    | .letE first body => .letE (mapPaperComputation σ first) (mapPaperComputation σ body)
    | .force thunk => .force (mapPaperValue σ thunk)
    | .call function thunk => .call (mapPaperValue σ function) (mapPaperValue σ thunk)
    | .resume continuation response => .resume (mapPaperValue σ continuation) (mapPaperValue σ response)
    | .split tuple binders body => .split (mapPaperValue σ tuple) binders (mapPaperComputation σ body)
    | .field record label => .field (mapPaperValue σ record) label
    | .lookup record label => .lookup (mapPaperValue σ record) label
    | .switch value branches => .switch (mapPaperValue σ value)
        (branches.attach.map fun ⟨branch, hmem⟩ => mapConstructorBranch σ branch)
    | .unroll value => .unroll (mapPaperValue σ value)
    | .choose value side => .choose (mapPaperValue σ value) side
    | .unionCase value leftBinder left rightBinder right =>
        .unionCase (mapPaperValue σ value) leftBinder (mapPaperComputation σ left)
          rightBinder (mapPaperComputation σ right)
    | .absurd value => .absurd (mapPaperValue σ value)
    | .primitive identity arguments => .primitive identity
        (arguments.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .perform operation arguments payload =>
        .perform operation (mapTypeArguments σ arguments) (mapPaperValue σ payload)
    | .handle body handler => .handle (mapPaperComputation σ body) (mapHandlerPlan σ handler)
    | .mapOperation body mapper => .mapOperation (mapPaperComputation σ body) (mapMapperPlan σ mapper)
    | .recursive bindings body =>
        .recursive (bindings.attach.map fun ⟨binding, hmem⟩ =>
          (binding.1, mapPaperValue σ binding.2))
          (mapPaperComputation σ body)
    | .template identity arguments values =>
        .template identity (mapTypeArguments σ arguments)
          (values.attach.map fun ⟨value, hmem⟩ => mapPaperValue σ value)
    | .fail reason => .fail reason
    | .request opInstance payload continuation =>
        .request (opInstance.subst σ) (mapPaperValue σ payload) (mapPaperValue σ continuation)
    | .scope owner body => .scope owner (mapPaperComputation σ body)
    | .expose metadata body => .expose (mapViewMetadata σ metadata) (mapPaperComputation σ body)
    | .enter owner function thunk =>
        .enter owner (mapPaperValue σ function) (mapPaperValue σ thunk)
    | .tryArms handler opInstance payload continuation arms =>
        .tryArms (mapHandlerPlan σ handler) (opInstance.subst σ) (mapPaperValue σ payload)
          (mapPaperValue σ continuation)
          (arms.attach.map fun ⟨arm, hmem⟩ => mapOperationArm σ arm)
    | .waitArm handler opInstance payload continuation arm remaining attempt =>
        .waitArm (mapHandlerPlan σ handler) (opInstance.subst σ) (mapPaperValue σ payload)
          (mapPaperValue σ continuation) (mapOperationArm σ arm)
          (remaining.attach.map fun ⟨arm, hmem⟩ => mapOperationArm σ arm)
          (mapPaperComputation σ attempt)
  termination_by computation => sizeOf computation
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapPaperPattern (σ : Nat → Ty) : PatternPlan → PatternPlan
    | .wild => .wild
    | .variable binder => .variable binder
    | .literal literal => .literal literal
    | .tuple children => .tuple (children.attach.map fun ⟨child, hmem⟩ => mapPaperPattern σ child)
    | .list prefixPatterns rest suffix =>
        .list (prefixPatterns.attach.map fun ⟨pattern, hmem⟩ => mapPaperPattern σ pattern) rest
          (suffix.attach.map fun ⟨pattern, hmem⟩ => mapPaperPattern σ pattern)
    | .record fields spread => .record (fields.attach.map fun ⟨field, hmem⟩ =>
        (field.1, mapPaperPattern σ field.2.1,
          match hdefault : field.2.2 with
          | none => none
          | some default => some (mapPaperComputation σ default))) spread
    | .polyVariant tag payload =>
        .polyVariant tag (payload.attach.map fun ⟨pattern, hmem⟩ => mapPaperPattern σ pattern)
    | .constructor identity arguments payload =>
        .constructor identity (mapTypeArguments σ arguments)
          (payload.attach.map fun ⟨pattern, hmem⟩ => mapPaperPattern σ pattern)
    | .reference definition equality =>
        .reference (mapPaperValue σ definition) (mapPaperComputation σ equality)
    | .asPattern child binder => .asPattern (mapPaperPattern σ child) binder
    | .orPattern left right binders =>
        .orPattern (mapPaperPattern σ left) (mapPaperPattern σ right) binders
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapConstructorBranch (σ : Nat → Ty) : ConstructorBranch → ConstructorBranch
    | .mk identity binders body => .mk identity binders (mapPaperComputation σ body)
  termination_by branch => sizeOf branch
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapGuardedBranch (σ : Nat → Ty) : GuardedBranch → GuardedBranch
    | .mk pattern guard body => .mk (mapPaperPattern σ pattern)
        (match guard with
          | none => none
          | some guard => some (mapPaperComputation σ guard))
        (mapPaperComputation σ body)
  termination_by branch => sizeOf branch
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapValueArm (σ : Nat → Ty) : ValueArm → ValueArm
    | .mk branch => .mk (mapGuardedBranch σ branch)
  termination_by arm => sizeOf arm
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapOperationArm (σ : Nat → Ty) : OperationArm → OperationArm
    | .mk operation rigidBinders pattern continuationBinder guard body =>
        let lifted := liftSubN rigidBinders σ
        .mk operation rigidBinders (mapPaperPattern lifted pattern) continuationBinder
          (match guard with
            | none => none
            | some guard => some (mapPaperComputation lifted guard))
          (mapPaperComputation lifted body)
  termination_by arm => sizeOf arm
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapHandlerPlan (σ : Nat → Ty) : HandlerPlan → HandlerPlan
    | .mk input output valueArms operationArms =>
        .mk (subst σ input) (subst σ output)
          (valueArms.attach.map fun ⟨arm, hmem⟩ => mapValueArm σ arm)
          (operationArms.attach.map fun ⟨arm, hmem⟩ => mapOperationArm σ arm)
  termination_by handler => sizeOf handler
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial

  def mapMapperPlan (σ : Nat → Ty) : MapperPlan → MapperPlan
    | .mk source target payload response =>
        .mk (source.subst σ) (target.subst σ) (mapPaperComputation σ payload)
          (mapPaperComputation σ response)
  termination_by mapper => sizeOf mapper
  decreasing_by all_goals
    all_goals
      first
      | exact (List.sizeOf_lt_of_mem hmem).le
      | have hsmall := List.sizeOf_lt_of_mem hmem
        simp +arith at hsmall ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfRecordValue_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfBindingValue_le binding
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternField_le field
        simp +arith at hsmall hproj ⊢ <;> omega
      | have hsmall := List.sizeOf_lt_of_mem hmem
        have hproj := sizeOfPatternDefault_le field default hdefault
        simp +arith at hsmall hproj ⊢ <;> omega
      | with_reducible decreasing_trivial
end

def mapTemplateBody (σ : Nat → Ty) : TemplateBody → TemplateBody
  | .mk identity arity formals result body =>
      let lifted := liftSubN arity σ
      .mk identity arity (formals.map (subst lifted)) (subst lifted result)
        (mapPaperComputation lifted body)

structure NominalConstructor where
  identity : DeclarationId
  typeArity : Nat
  payloadTemplate : List Ty

structure PrimitiveSignature where
  identity : Nat
  typeArity : Nat
  arguments : List Ty
  result : Ty

structure DeclarationTable where
  operations : List OperationDeclaration
  nominalConstructors : List NominalConstructor
  primitives : List PrimitiveSignature
  templates : List TemplateBody
  nativeListIdentity : DeclarationId

structure ValueGraph where
  nodes : List (Nat × Value)
  guarded : Prop

abbrev TypeEnvironment := List Ty
abbrev GraphEnvironment := List (Nat × Ty)

inductive Subject where
  | value (value : Value)
  | computation (computation : Computation)

def mapNominalConstructor (σ : Nat → Ty) (entry : NominalConstructor) : NominalConstructor :=
  let lifted := liftSubN entry.typeArity σ
  { entry with payloadTemplate := entry.payloadTemplate.map (subst lifted) }

def mapPrimitiveSignature (σ : Nat → Ty) (signature : PrimitiveSignature) : PrimitiveSignature :=
  let lifted := liftSubN signature.typeArity σ
  { identity := signature.identity
    typeArity := signature.typeArity
    arguments := signature.arguments.map (subst lifted)
    result := subst lifted signature.result }

def mapDeclarationTable (σ : Nat → Ty) (declarations : DeclarationTable) : DeclarationTable :=
  { declarations with
    operations := declarations.operations.map (OperationDeclaration.substAmbient σ),
    nominalConstructors := declarations.nominalConstructors.map (mapNominalConstructor σ),
    primitives := declarations.primitives.map (mapPrimitiveSignature σ),
    templates := declarations.templates.map (mapTemplateBody σ) }

def mapTypeEnvironment (σ : Nat → Ty) (environment : TypeEnvironment) : TypeEnvironment :=
  environment.map (subst σ)

def mapGraphEnvironment (σ : Nat → Ty) (environment : GraphEnvironment) : GraphEnvironment :=
  environment.map fun (identity, ty) => (identity, subst σ ty)

def mapValueGraph (σ : Nat → Ty) (graph : ValueGraph) : ValueGraph :=
  { nodes := graph.nodes.map fun (identity, value) => (identity, mapPaperValue σ value),
    guarded := graph.guarded }

def mapSubject (σ : Nat → Ty) : Subject → Subject
  | .value value => .value (mapPaperValue σ value)
  | .computation computation => .computation (mapPaperComputation σ computation)

/-!
The remaining declarations in this module will encode the mutually
inductive syntactic judgments from paper §types and §machine.  In particular,
`Bad` is deliberately not a `Computation` constructor.
-/

end YulangClosure.PaperTypes
