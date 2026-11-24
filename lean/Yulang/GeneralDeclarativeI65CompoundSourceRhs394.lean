import Yulang.GeneralDeclarativeI65OriginalBodyEvent393

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonDeclaredNominalInspection (Parameter)
open CommonRecursiveNominalIntervals (Endpoint Bounds Argument childContext effectiveParameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open Core.PresenceGeneration (RowTerm)

mutual
/-- A logical RHS tree, distinct from the C386 wire for a root app.
Structural nodes retain their full ordered children, including declared
native subterms. Original variables retain their lexical binder. -/
inductive SourceRhsCode394 where
  | variable (binder logicalCenter : Nat)
  | record (label : Nat) (payload tail : SourceRhsCode394)
  | variant (tag : Nat) (payload : SourceRhsCode394)
  | join (first last : SourceRhsCode394)
  | nominal (constructor : Nat) (arguments : List SourceRhsArg394)

inductive SourceRhsArg394 where
  | valueSlot (binder : Nat) (bounds : Bounds (Endpoint Nat))
  | rowSlot (binder : Nat) (bounds : Bounds (RowTerm Nat))
  | valueExpression (child : SourceRhsCode394)
end

mutual
def SourceRhsCode394.source : SourceRhsCode394 → Pattern
  | .variable binder _ => .var binder
  | .record label payload tail => .record label payload.source tail.source
  | .variant tag payload => .variant tag payload.source
  | .join first last => .join first.source last.source
  | .nominal ctor args => .app ctor (sourceArgList394 args)

def SourceRhsArg394.source : SourceRhsArg394 → Pattern
  | .valueSlot binder _ => .var binder
  | .rowSlot binder _ => .var binder
  | .valueExpression child => child.source

def sourceArgList394 : List SourceRhsArg394 → List Pattern
  | [] => []
  | head :: tail => head.source :: sourceArgList394 tail
end

mutual
/-- Independent source derivation. Existing declaration-mode use and
kinded captures are retained at every operation. Structural wrappers
neither merge branches nor switch inherited mode. Primitive forms
outside this native-and-structural representation are not denied. -/
inductive CompoundSourceRhs394 (s : State) (slots : Nat → Option Capture) :
    Bool → Pattern → SourceRhsCode394 → Prop where
  | variable {context n c} :
      slots n = some c → TypedBodyCapture392 s c .value →
      CompoundSourceRhs394 s slots context (.var n) (.variable n c.center)
  | record {context label head tail first last} :
      CompoundSourceRhs394 s slots context head first →
      CompoundSourceRhs394 s slots context tail last →
      CompoundSourceRhs394 s slots context (.record label head tail) (.record label first last)
  | variant {context tag payload code} :
      CompoundSourceRhs394 s slots context payload code →
      CompoundSourceRhs394 s slots context (.variant tag payload) (.variant tag code)
  | join {context first last a b} :
      CompoundSourceRhs394 s slots context first a →
      CompoundSourceRhs394 s slots context last b →
      CompoundSourceRhs394 s slots context (.join first last) (.join a b)
  | nominal {context ctor pats params args} (use : Use s.current.environment ctor pats.length) :
      names use.mode pats.length = some params →
      s.modes[ctor]? = some params →
      CompoundSourceArgs394 s slots context params pats args →
      CompoundSourceRhs394 s slots context (.app ctor pats) (.nominal ctor args)

inductive CompoundSourceArgs394 (s : State) (slots : Nat → Option Capture) :
    Bool → List Parameter → List Pattern → List SourceRhsArg394 → Prop where
  | nil : CompoundSourceArgs394 s slots context [] [] []
  | cons :
      CompoundSourceArg394 s slots context param p arg →
      CompoundSourceArgs394 s slots context params patterns args →
      CompoundSourceArgs394 s slots context (param :: params) (p :: patterns) (arg :: args)

inductive CompoundSourceArg394 (s : State) (slots : Nat → Option Capture) :
    Bool → Parameter → Pattern → SourceRhsArg394 → Prop where
  | pointValue {context p binder c} :
      p.kind = .value → (effectiveParameter context p).variance ≠ .invariant →
      slots binder = some c → TypedBodyCapture392 s c .value →
      CompoundSourceArg394 s slots context p (.var binder)
        (.valueSlot binder (.point (.ordinary (.var c.center))))
  | intervalValue {context p binder c} :
      p.kind = .value → (effectiveParameter context p).variance = .invariant →
      slots binder = some c → TypedBodyCapture392 s c .value →
      CompoundSourceArg394 s slots context p (.var binder)
        (.valueSlot binder (.interval (.ordinary (.var c.lower)) (.ordinary (.var c.upper))))
  | pointRow {context p binder c} :
      p.kind = .row → (effectiveParameter context p).variance ≠ .invariant →
      slots binder = some c → TypedBodyCapture392 s c .row →
      CompoundSourceArg394 s slots context p (.var binder)
        (.rowSlot binder (.point (.var c.center)))
  | intervalRow {context p binder c} :
      p.kind = .row → (effectiveParameter context p).variance = .invariant →
      slots binder = some c → TypedBodyCapture392 s c .row →
      CompoundSourceArg394 s slots context p (.var binder)
        (.rowSlot binder (.interval (.var c.lower) (.var c.upper)))
  | valueExpression {context p input code} :
      p.kind = .value → (∀ n, input ≠ .var n) →
      CompoundSourceRhs394 s slots (childContext context p) input code →
      CompoundSourceArg394 s slots context p input (.valueExpression code)
end

theorem compound_source_preserves_syntax394 {s : State} {slots : Nat → Option Capture}
    {context : Bool} {p : Pattern} {code : SourceRhsCode394}
    (proof : CompoundSourceRhs394 s slots context p code) :
    code.source = p := by
  exact CompoundSourceRhs394.rec
    (motive_1 := fun _ p code _ => code.source = p)
    (motive_2 := fun _ _ ps codes _ => sourceArgList394 codes = ps)
    (motive_3 := fun _ _ p code _ => code.source = p)
    (fun _ _ => rfl)
    (fun _ _ head tail => by simp only [SourceRhsCode394.source,head,tail])
    (fun _ payload => by simp only [SourceRhsCode394.source,payload])
    (fun _ _ first last => by simp only [SourceRhsCode394.source,first,last])
    (fun _ _ _ _ args => by simp only [SourceRhsCode394.source,args])
    rfl
    (fun _ _ first tail => by simp only [sourceArgList394,first,tail])
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ child => child)
    proof

/-- A represented source body has a unique code. In particular,
structural operations keep both ordered operands, while type/row and
point/interval choices follow the actual inherited declaration mode. -/
theorem compound_source_rhs_functional394 {s : State} {slots : Nat → Option Capture}
    {context : Bool} {p : Pattern} {first : SourceRhsCode394}
    (made : CompoundSourceRhs394 s slots context p first) :
    ∀ second, CompoundSourceRhs394 s slots context p second → first = second := by
  exact CompoundSourceRhs394.rec
    (motive_1 := fun c p a _ => ∀ b, CompoundSourceRhs394 s slots c p b → a = b)
    (motive_2 := fun c ps pts as _ => ∀ bs, CompoundSourceArgs394 s slots c ps pts bs → as = bs)
    (motive_3 := fun c p pt a _ => ∀ b, CompoundSourceArg394 s slots c p pt b → a = b)
    (fun firstSlot _ _ second => by
      cases second with
      | «variable» secondSlot _ =>
        cases Option.some.inj (firstSlot.symm.trans secondSlot)
        rfl)
    (fun _ _ first last _ second => by
      cases second with
      | record a b => rw [first _ a,last _ b])
    (fun _ first _ second => by
      cases second with
      | variant inner => rw [first _ inner])
    (fun _ _ first last _ second => by
      cases second with
      | join a b => rw [first _ a,last _ b])
    (fun _ _ table _ proveArgs _ second => by
      cases second with
      | nominal _ _ table' args =>
        cases Option.some.inj (table.symm.trans table')
        exact congrArg (SourceRhsCode394.nominal _) (proveArgs _ args))
    (fun _ second => by cases second; rfl)
    (fun _ _ first rest _ second => by
      cases second with
      | cons h t => rw [first _ h,rest _ t])
    (fun firstKind firstMode firstSlot _ _ second => by
      cases second <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ second => by
      cases second <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ second => by
      cases second <;> simp_all)
    (fun firstKind firstMode firstSlot _ _ second => by
      cases second <;> simp_all)
    (fun kind notVariable _ inner _ second => by
      cases second with
      | valueExpression _ _ other => rw [inner _ other]
      | pointValue _ _ _ _ => exact False.elim (notVariable _ rfl)
      | intervalValue _ _ _ _ => exact False.elim (notVariable _ rfl)
      | pointRow _ _ _ _ => exact False.elim (notVariable _ rfl)
      | intervalRow _ _ _ _ => exact False.elim (notVariable _ rfl))
    made

mutual
/-- A projection to the fragment already represented by C386 and
C392. Failure here is only absence of that encoding, never rejection
or a choice to treat mixed structural and native types as ordinary. -/
def plainEndpoint394 : SourceRhsCode394 → Option (Endpoint Nat)
  | .variable _ center => some (.ordinary (.var center))
  | .nominal ctor args => (plainArgs394 args).map (.nominal ctor)
  | .record .. | .variant .. | .join .. => none

def plainArg394 : SourceRhsArg394 → Option (Argument Nat)
  | .valueSlot _ bounds => some (.inl bounds)
  | .rowSlot _ bounds => some (.inr bounds)
  | .valueExpression child => (plainEndpoint394 child).map (fun e => .inl (.point e))

def plainArgs394 : List SourceRhsArg394 → Option (List (Argument Nat))
  | [] => some []
  | a::as => do return (← plainArg394 a) :: (← plainArgs394 as)
end

theorem native_rhs_embeds_in_original_compound394
    {s : State} {slots : Nat → Option Capture} {context : Bool} {p : Pattern}
    {endpoint : Endpoint Nat} (built : NativeBodyRhs392 s slots context p endpoint) :
    ∃ code, CompoundSourceRhs394 s slots context p code ∧
      plainEndpoint394 code = some endpoint := by
  exact NativeBodyRhs392.rec
    (motive_1 := fun c p e _ => ∃ code, CompoundSourceRhs394 s slots c p code ∧
      plainEndpoint394 code = some e)
    (motive_2 := fun c ps pts args _ => ∃ codes, CompoundSourceArgs394 s slots c ps pts codes ∧
      plainArgs394 codes = some args)
    (motive_3 := fun c p pt arg _ => ∃ code, CompoundSourceArg394 s slots c p pt code ∧
      plainArg394 code = some arg)
    (fun found typed => ⟨_,.variable found typed,rfl⟩)
    (fun use fromUse table _ inductionArgs => by
      obtain ⟨args,source,projected⟩ := inductionArgs
      exact ⟨_,.nominal use fromUse table source,by simp only [plainEndpoint394,projected,Option.map_some]⟩)
    ⟨[],.nil,rfl⟩
    (fun _ _ proveHead proveTail => by
      obtain ⟨first,head,a⟩ := proveHead
      obtain ⟨rest,tail,b⟩ := proveTail
      exact ⟨_,.cons head tail,by simp [plainArgs394,a,b]⟩)
    (fun mode effective read captured => ⟨_,.pointValue mode effective read captured,rfl⟩)
    (fun mode effective read captured => ⟨_,.intervalValue mode effective read captured,rfl⟩)
    (fun mode effective read captured => ⟨_,.pointRow mode effective read captured,rfl⟩)
    (fun mode effective read captured => ⟨_,.intervalRow mode effective read captured,rfl⟩)
    (fun mode _ nested => by
      obtain ⟨code,source,projected⟩ := nested
      exact ⟨_,.valueExpression mode (fun _ impossible => by cases impossible) source,
        by simp only [plainArg394,projected,Option.map_some]⟩)
    built

/-- A real source output has the original authored Body, original role
output ordinal and the original target. It is not a reinterpretation
of an already supplied C386 receipt. -/
structure OriginalCompoundOutput394 {s : State} {q : Request}
    (f : AuthoredBodyFrame393 s q) (ordinal : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles f.decl
    (q.demand.outputs[ordinal]).name body
  code : SourceRhsCode394
  derived : CompoundSourceRhs394 s (f.slots body) false (normalize (bodyPattern body)) code

structure CompoundEquation394 where
  occurrence : List Nat
  ordinal : Nat
  requested : GeneralSourceState.Output
  originalBody : Body
  rhs : SourceRhsCode394

def OriginalCompoundOutput394.emit {s q f ordinal}
    (out : OriginalCompoundOutput394 (s := s) (q := q) f ordinal) : CompoundEquation394 :=
  ⟨q.occurrence,ordinal.val,q.demand.outputs[ordinal],out.body,out.code⟩

theorem compound_emit_is_original_source394 {s q f ordinal}
    (out : OriginalCompoundOutput394 (s := s) (q := q) f ordinal) :
    out.emit.occurrence = q.occurrence ∧ out.emit.ordinal = ordinal.val ∧
      q.demand.outputs[ordinal.val]? = some out.emit.requested ∧
      Supplies (authoredRegistry s.current).roles f.decl
        out.emit.requested.name out.emit.originalBody ∧
      out.emit.rhs.source = normalize (bodyPattern out.emit.originalBody) := by
  exact ⟨rfl,rfl,List.getElem?_eq_getElem ordinal.isLt,out.supplied,
    compound_source_preserves_syntax394 out.derived⟩

/-- No new wire shape is synthesized here. This is the pre-existing
bare/tagged native encoding, and keeps exactly its original ordered
argument vector when it is available. -/
def projectOldNativeLiteral394 (target : Nat) : SourceRhsCode394 → Option LiteralWriteSyntax
  | code@(.nominal _ args) =>
      (plainArgs394 args).map fun xs => .declared target code.source xs
  | code@(.variant _ (.nominal _ args)) =>
      (plainArgs394 args).map fun xs => .declared target code.source xs
  | _ => none

private theorem native_app_code394 {s : State} {slots : Nat → Option Capture}
    {context : Bool} {ctor : Nat} {pats : List Pattern} {args : List (Argument Nat)}
    (old : NativeBodyRhs392 s slots context (.app ctor pats) (.nominal ctor args)) :
    ∃ as, CompoundSourceRhs394 s slots context (.app ctor pats) (.nominal ctor as) ∧
      plainArgs394 as = some args := by
  obtain ⟨code,derived,projection⟩ := native_rhs_embeds_in_original_compound394 old
  cases derived with
  | nominal use fromUse table packed =>
    exact ⟨_,.nominal use fromUse table packed,by simpa [plainEndpoint394] using projection⟩

/-- The actual original producer's existing typed branches lift to
the new structural carrier without changing the literal wire output,
source supplier, ordinal, or target. This says nothing about making
new structural compounds fit the old wire. -/
theorem existing_native_output_has_same_wire394 {s q f ordinal}
    (old : AuthoredOutput393 (s := s) (q := q) f ordinal)
    (typed : ∃ target source arguments, old.write = .declared target source arguments) :
    ∃ (out : OriginalCompoundOutput394 f ordinal),
      out.body = old.body ∧ out.emit.requested = old.receipt.requested ∧
      projectOldNativeLiteral394 out.emit.requested.target out.emit.rhs = some old.write := by
  cases old with
  | mk body supplied write built =>
    cases built with
    | ordinary _ _ =>
      obtain ⟨_,_,_,impossible⟩ := typed
      cases impossible
    | native authored formula =>
      obtain ⟨code,actual,projected⟩ := native_app_code394 formula
      let out : OriginalCompoundOutput394 f ordinal :=
        ⟨body,supplied,.nominal _ code,authored.symm ▸ actual⟩
      have source := compound_source_preserves_syntax394 actual
      exact ⟨out,rfl,rfl,by simp only [out,OriginalCompoundOutput394.emit,projectOldNativeLiteral394,
        projected,Option.map_some,source]⟩
    | @tagged tag ctor pats args authored formula =>
      obtain ⟨code,actual,projected⟩ := native_app_code394 formula
      let out : OriginalCompoundOutput394 f ordinal :=
        ⟨body,supplied,.variant tag (.nominal ctor code),by
          rw [authored]
          exact .variant actual⟩
      have source := compound_source_preserves_syntax394
        (CompoundSourceRhs394.variant (tag := tag) actual)
      exact ⟨out,rfl,rfl,by simp only [out,OriginalCompoundOutput394.emit,projectOldNativeLiteral394,
        projected,Option.map_some,source]⟩

end Yulang.GeneralDeclarativeI65
