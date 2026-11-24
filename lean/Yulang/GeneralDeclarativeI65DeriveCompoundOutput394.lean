import Yulang.GeneralDeclarativeI65CompoundSourceRhs394

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (normalize)
open CommonDeclaredNominalInspection (Parameter)

open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open CommonRecursiveNominalIntervals (childContext effectiveParameter)
open GeneralDictionaryAssociatedProvenance (Body lookup lookup_exact)
open GeneralDeclarativeOutputs320 (bodyPattern)

abbrev BindingTicket394 (s : State) (slots : Nat → Option Capture)
    (n : Nat) (kind : CommonDeclaredNominalInspection.Kind) :=
  { c : Capture // slots n = some c ∧ TypedBodyCapture392 s c kind }

/-- Input is actual independent binders, not an already evaluated
body, a model, or a table of root output proofs. -/
structure SourceBindingReads394 (s : State) (slots : Nat → Option Capture) where
  value : (n : Nat) → Option (BindingTicket394 s slots n .value)
  row : (n : Nat) → Option (BindingTicket394 s slots n .row)

abbrev DerivedRhs394 (s : State) (slots : Nat → Option Capture) (context : Bool) (p : Pattern) :=
  { c : SourceRhsCode394 // CompoundSourceRhs394 s slots context p c }

abbrev DerivedArgs394 (s : State) (slots : Nat → Option Capture) (context : Bool)
    (ps : List Parameter) (pats : List Pattern) :=
  { as : List SourceRhsArg394 // CompoundSourceArgs394 s slots context ps pats as }

abbrev DerivedArg394 (s : State) (slots : Nat → Option Capture) (context : Bool)
    (parameter : Parameter) (p : Pattern) :=
  { a : SourceRhsArg394 // CompoundSourceArg394 s slots context parameter p a }

/-- Derive a captured variable with the declaration kind and inherited
variance; no absent-value fallback. -/
def emitBindingArg394 {s : State} {slots : Nat → Option Capture}
    (bound : SourceBindingReads394 s slots) (context : Bool) (p : Parameter)
    (n : Nat) : Option (DerivedArg394 s slots context p (.var n)) :=
  match h : p.kind with
  | .value => do
      let ⟨_c,found,proof⟩ ← bound.value n
      if mode : (effectiveParameter context p).variance = .invariant then
        pure ⟨_,.intervalValue h mode found proof⟩
      else pure ⟨_,.pointValue h mode found proof⟩
  | .row => do
      let ⟨_c,found,proof⟩ ← bound.row n
      if mode : (effectiveParameter context p).variance = .invariant then
        pure ⟨_,.intervalRow h mode found proof⟩
      else pure ⟨_,.pointRow h mode found proof⟩

private def liftCompoundValueArgument394 {s : State} {slots : Nat → Option Capture} {context p pat}
    (kind : p.kind = .value) (notVariable : ∀ n, pat ≠ .var n)
    (code : Option (DerivedRhs394 s slots (childContext context p) pat)) :
    Option (DerivedArg394 s slots context p pat) := do
  let ⟨term,proof⟩ ← code
  pure ⟨.valueExpression term,.valueExpression kind notVariable proof⟩

mutual
/-- Syntax-directed source elaboration, returning its actual local
derivation. An unrepresented case is not supplied to the resolver
as a rejection or candidate verdict. -/
def emitCompoundSource394 {s : State} {slots : Nat → Option Capture}
    (bound : SourceBindingReads394 s slots) (context : Bool) (p : Pattern) :
    Option (DerivedRhs394 s slots context p) :=
  match p with
  | .var n => do
      let ⟨c,found,proof⟩ ← bound.value n
      pure ⟨.variable n c.center,.variable found proof⟩
  | .record label payload tail => do
      let ⟨head,a⟩ ← emitCompoundSource394 bound context payload
      let ⟨rest,b⟩ ← emitCompoundSource394 bound context tail
      pure ⟨.record label head rest,.record a b⟩
  | .variant tag payload => do
      let ⟨code,proof⟩ ← emitCompoundSource394 bound context payload
      pure ⟨.variant tag code,.variant proof⟩
  | .join first last => do
      let ⟨left,a⟩ ← emitCompoundSource394 bound context first
      let ⟨right,b⟩ ← emitCompoundSource394 bound context last
      pure ⟨.join left right,.join a b⟩
  | .app ctor pats => do
      let use ← readUse s.current.environment ctor pats.length
      match wrote : names use.mode pats.length with
      | none => none
      | some ps =>
        if table : s.modes[ctor]? = some ps then do
          let ⟨args,built⟩ ← emitCompoundArgs394 bound context ps pats
          pure ⟨.nominal ctor args,.nominal use wrote table built⟩
        else none
termination_by (sizeOf p,0)
decreasing_by all_goals simp_wf; all_goals omega

def emitCompoundArgs394 {s : State} {slots : Nat → Option Capture}
    (bound : SourceBindingReads394 s slots) (context : Bool) (ps : List Parameter)
    (pats : List Pattern) : Option (DerivedArgs394 s slots context ps pats) :=
  match ps,pats with
  | [],[] => some ⟨[],.nil⟩
  | parameter::params,p::rest => do
      let ⟨head,a⟩ ← emitCompoundArg394 bound context parameter p
      let ⟨tail,b⟩ ← emitCompoundArgs394 bound context params rest
      pure ⟨head::tail,.cons a b⟩
  | _,_ => none
termination_by (sizeOf pats,0)
decreasing_by all_goals simp_wf; all_goals omega

def emitCompoundArg394 {s : State} {slots : Nat → Option Capture}
    (bound : SourceBindingReads394 s slots) (context : Bool) (parameter : Parameter)
    (p : Pattern) : Option (DerivedArg394 s slots context parameter p) :=
  match p with
  | .var n => emitBindingArg394 bound context parameter n
  | .record label payload tail =>
      if hk : parameter.kind = .value then
        liftCompoundValueArgument394 hk (fun _ bad => by cases bad)
          (emitCompoundSource394 bound (childContext context parameter) (.record label payload tail))
      else none
  | .variant tag payload =>
      if hk : parameter.kind = .value then
        liftCompoundValueArgument394 hk (fun _ bad => by cases bad)
          (emitCompoundSource394 bound (childContext context parameter) (.variant tag payload))
      else none
  | .join first last =>
      if hk : parameter.kind = .value then
        liftCompoundValueArgument394 hk (fun _ bad => by cases bad)
          (emitCompoundSource394 bound (childContext context parameter) (.join first last))
      else none
  | .app ctor args =>
      if hk : parameter.kind = .value then
        liftCompoundValueArgument394 hk (fun _ bad => by cases bad)
          (emitCompoundSource394 bound (childContext context parameter) (.app ctor args))
      else none
termination_by (sizeOf p,1)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.right
  all_goals omega
end

/-- Look up the actual authored body at the original output position
and derive its code. The per-body inputs are real source bindings,
not evidence for the desired compound output. -/
def deriveOriginalCompoundOutput394 {s q} (f : AuthoredBodyFrame393 s q)
    (i : Fin q.demand.outputs.length) (unique : (f.decl.associated.map Equation.name).Nodup)
    (binders : (body : Body) → SourceBindingReads394 s (f.slots body)) :
    Option (OriginalCompoundOutput394 f i) :=
  let roles := (authoredRegistry s.current).roles
  let output := q.demand.outputs[i]
  match available : lookup roles f.decl output.name with
  | none => none
  | some body => do
    let ⟨code,source⟩ ← emitCompoundSource394 (binders body) false (normalize (bodyPattern body))
    let supplied := (lookup_exact roles f.decl unique output.name body).mp available
    pure ⟨body,supplied,code,source⟩

theorem derive_record_from_independent_native_parts394
    {s : State} {slots : Nat → Option Capture} (bound : SourceBindingReads394 s slots)
    {context : Bool} {label : Nat} {first last : Pattern}
    {a : DerivedRhs394 s slots context first} {b : DerivedRhs394 s slots context last}
    (head : emitCompoundSource394 bound context first = some a)
    (tail : emitCompoundSource394 bound context last = some b) :
    ∃ result, emitCompoundSource394 bound context (.record label first last) = some result ∧
      result.val = .record label a.val b.val := by
  exact ⟨⟨.record label a.val b.val,.record a.2 b.2⟩,by simp [emitCompoundSource394,head,tail],rfl⟩

theorem derive_join_from_independent_native_parts394
    {s : State} {slots : Nat → Option Capture} (bound : SourceBindingReads394 s slots)
    {context : Bool} {first last : Pattern}
    {a : DerivedRhs394 s slots context first} {b : DerivedRhs394 s slots context last}
    (head : emitCompoundSource394 bound context first = some a)
    (tail : emitCompoundSource394 bound context last = some b) :
    ∃ result, emitCompoundSource394 bound context (.join first last) = some result ∧
      result.val = .join a.val b.val := by
  exact ⟨⟨.join a.val b.val,.join a.2 b.2⟩,by simp [emitCompoundSource394,head,tail],rfl⟩

end Yulang.GeneralDeclarativeI65
