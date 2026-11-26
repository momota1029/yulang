import Yulang.GeneralDeclarativeI65I74RefPositionSource441
import Yulang.GeneralNominalCenteredHeadMatExpressions
import Yulang.GeneralDeclarativeWitnessSparseVariance357
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open CommonRecursiveNominalIntervals
open CommonDeclaredNominalInspection (Registry Parameter)
open Core.PresenceGeneration (RowTerm TyTerm)
open PresenceNormalForm (Atom)

abbrev modes : List Parameter := RefPositions441.layout
def args (e : RowTerm Nat) (l u : TyTerm Nat) : List (Argument Nat) :=
  [.inr (.point e),.inl (.interval (.ordinary l) (.ordinary u))]

/-- The actual context compiler emits one signed row atom then four value
atoms, in source positional order, uniformly over terms and name. -/
theorem source_positions_forward {reg : Registry} {name : Nat} (atName : reg[name]? = some modes)
    (e₁ e₂ : RowTerm Nat) (l₁ u₁ l₂ u₂ : TyTerm Nat) :
    compileContext reg (.nominal name (args e₁ l₁ u₁)) (.nominal name (args e₂ l₂ u₂)) =
      some [.rowLe e₁ e₂,.tyLe l₁ u₁,.tyLe l₁ u₂,.tyLe l₂ u₁,.tyLe l₂ u₂] := by
  have adm : ∀ e l u, admitContext reg false (.nominal name (args e l u)) = true := by
    intro e l u
    apply (admit_context_exact ..).mpr
    exact .nominal atName (.cons (.rowPoint _ _ _) (.cons
      (.valueInterval (.ordinary true l) (.ordinary true u)) (.nil false)))
  rw [compileContext,compileInContext,adm,adm]
  simp only [Bool.and_self, ↓reduceIte]
  rw [inspect_context_nominal reg false name _ _ modes
    [(false,.row e₁ e₂),(true,.value (.ordinary l₁) (.ordinary u₁)),
     (true,.value (.ordinary l₁) (.ordinary u₂)),(true,.value (.ordinary l₂) (.ordinary u₁)),
     (true,.value (.ordinary l₂) (.ordinary u₂))] atName (by rfl)]
  simp [inspectContextObligation, concatenate, append, inspectContext]

theorem wrong_position_has_no_comparison {reg : Registry} {name : Nat}
    (atName : reg[name]? = some modes) (e : RowTerm Nat) (l u : TyTerm Nat) :
    compileContext reg (.nominal name [.inl (.interval (.ordinary l) (.ordinary u)),.inr (.point e)])
      (.nominal name (args e l u)) = none := by
  have reject : admitContext reg false
      (.nominal name [.inl (.interval (.ordinary l) (.ordinary u)),.inr (.point e)]) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have wf := (admit_context_exact ..).mp yes
    cases wf with
    | nominal selected shape =>
      have same := Option.some.inj (selected.symm.trans atName)
      rw [same] at shape
      cases shape with
      | cons first _ => cases first
  simp [compileContext,compileInContext,reject]

/-- No existing DeepRead production consumes a rigid nullary application
when either endpoint is the ordinary authored scalar representation. -/
theorem no_deep_literal_ordinary {s : GeneralDeclarativeI65.State} {capture : Nat → Capture}
    {ctx : Bool} {name : Nat} {l u : TyTerm Nat} {bs : List Binding} :
    ¬ Nonempty (DeepRead s capture ctx (.app name []) (.ordinary l) (.ordinary u) bs) := by
  rintro ⟨hyp⟩
  cases hyp

theorem no_deep_rigid_int_value {s : GeneralDeclarativeI65.State} {capture : Nat → Capture}
    {name : Nat} {bs : List Binding} :
    ¬ Nonempty (DeepArgument s capture true valueInv (.app name [])
      (.inl (.point (.ordinary (.base .int)))) (.inl (.point (.ordinary (.base .int)))) bs) := by
  rintro ⟨hyp⟩
  cases hyp with
  | invariantValue left _ => exact no_deep_literal_ordinary ⟨left⟩

open GeneralDeclarationPatterns (Constructors Constructor Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralNominalInspection (Interpretation)
open GeneralCandidateInspection (Primitive)

theorem centered_compiler_cannot_translate_row_value_app {ctors : Constructors}
    {interp : Interpretation} {ctor : Constructor} {name binder rigid : Nat}
    (layout : ctor.parameters = [.row,.type]) (read : ctors name = some ctor) :
    translate ctors interp (.app name [.var binder,.app rigid []]) = none := by
  simp only [translate,translateMany,← Option.pure_def,pure_bind]
  cases rest : application ctors interp rigid [] with
  | none => simp
  | some exp =>
    simp only [← Option.pure_def,pure_bind]
    cases hint : interp.primitives name with
    | none => simp [application,read,layout,hint]
    | some p => cases p <;> simp [application,read,layout,hint,Primitive.parameters]

def written (ref binder int : Nat) : Pattern := .app ref [.var binder,.app int []]
def readArgs (e : RowTerm Nat) : List (Argument Nat) :=
  [.inr (.point e),.inl (.point (.ordinary (.base .int)))]

theorem row_value_deep_replay_cannot_consume_rigid_int
    {s : GeneralDeclarativeI65.State} {capture : Nat → Capture} {ref binder int : Nat}
    (table : s.modes[ref]? = some modes) (e f : RowTerm Nat) {out : List Binding} :
    ¬ Nonempty (DeepRead s capture false (written ref binder int)
      (.nominal ref (readArgs e)) (.nominal ref (readArgs f)) out) := by
  rintro ⟨deep⟩
  unfold written at deep
  cases deep with
  | nominal cited read located parts =>
    have same := Option.some.inj (located.symm.trans table)
    rw [same] at parts
    cases parts with
    | cons _ tail =>
      cases tail with
      | cons value _ => exact no_deep_rigid_int_value ⟨value⟩

theorem fixed_ordered_head_for_rigid_ref_has_no_current_constructor
    {s : GeneralDeclarativeI65.State} {capture : Nat → Capture} {arg : Capture} {ref binder int : Nat}
    {ctor : Constructor}
    (layout : ctor.parameters = [.row,.type])
    (catalogue : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).constructors ref
      = some ctor)
    (table : s.modes[ref]? = some modes)
    (real : ∀ o ∈ s.origins, OriginRoute s o arg.lower ∨ OriginRoute s o arg.upper →
      ∃ e, o.endpoint = .nominal ref (readArgs e)) :
    ¬ DeepHead s capture arg (written ref binder int) := by
  intro old
  cases old with
  | ordinary head =>
    obtain ⟨_,_,compiled,_⟩ := head
    have nope := centered_compiler_cannot_translate_row_value_app (binder := binder) (rigid := int)
      (interp := GeneralSourceMetadataRows291.interpretation s.current.environment.source.snapshot) layout catalogue
    change translate _ _ (written ref binder int) = none at nope
    rw [nope] at compiled
    cases compiled
  | declared route deep =>
    obtain ⟨e,lo⟩ := real _ route.lowerAuthored (.inl route.lo)
    obtain ⟨f,hi⟩ := real _ route.upperAuthored (.inr route.hi)
    have normalized : GeneralDeclarationPatterns.normalize (written ref binder int) = written ref binder int := rfl
    rw [lo,hi,normalized] at deep
    exact row_value_deep_replay_cannot_consume_rigid_int table e f ⟨deep⟩


open CommonRoleOutermostResolver (All₂)
open GeneralDeclarations (Declaration)

theorem fixed_named_source_head_replay_gap
    {s : GeneralDeclarativeI65.State} {q : Request} {d : Declaration} {arg : Capture} {ref binder int : Nat}
    {ctor : Constructor}
    (asked : q.demand.arguments = [arg]) (literal : d.head = [written ref binder int])
    (layout : ctor.parameters = [.row,.type])
    (catalogue : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.current).constructors ref
      = some ctor)
    (table : s.modes[ref]? = some modes)
    (real : ∀ o ∈ s.origins, OriginRoute s o arg.lower ∨ OriginRoute s o arg.upper →
      ∃ e, o.endpoint = .nominal ref (readArgs e)) :
    ¬ Nonempty (SourceHead s q d) := by
  rintro ⟨head⟩
  cases head with
  | ordered capture roots =>
    have matched : All₂ (DeepHead s capture) [arg] [written ref binder int] := by
      simpa only [asked,literal] using roots
    cases matched with
    | cons front _ =>
      exact fixed_ordered_head_for_rigid_ref_has_no_current_constructor layout catalogue table real front
  | joined already =>
    have same := List.cons.inj (already.head.symm.trans literal) |>.1
    have bad := already.normalized
    rw [same] at bad
    change Pattern.app ref _ = Pattern.variant _ _ at bad
    cases bad


/-- In explicitly inherited invariant context, the used covariant row is
also interval-valued. Its four checks precede the four value checks, with
no flattening of the row into a value. -/
theorem both_typed_positions_inherited
    {reg : Registry} {name : Nat} (atName : reg[name]? = some modes)
    (eL eU fL fU : RowTerm Nat) (vL vU wL wU : TyTerm Nat) :
    let extended := fun e f (l u : TyTerm Nat) => .nominal name
      [.inr (.interval e f),.inl (.interval (.ordinary l) (.ordinary u))]
    compileInContext reg true (extended eL eU vL vU) (extended fL fU wL wU) =
      some [.rowLe eL eU,.rowLe eL fU,.rowLe fL eU,.rowLe fL fU,
        .tyLe vL vU,.tyLe vL wU,.tyLe wL vU,.tyLe wL wU] := by
  dsimp
  have adm : ∀ e f (l u : TyTerm Nat), admitContext reg true (.nominal name
      [.inr (.interval e f),.inl (.interval (.ordinary l) (.ordinary u))]) = true := by
    intro e f l u
    apply (admit_context_exact ..).mpr
    exact .nominal atName (.cons (.rowInterval true e f) (.cons
      (.valueInterval (.ordinary true l) (.ordinary true u)) (.nil true)))
  rw [compileInContext,adm,adm]
  simp only [Bool.and_self, ↓reduceIte]
  rw [inspect_context_nominal reg true name _ _ modes
    [(true,.row eL eU),(true,.row eL fU),(true,.row fL eU),(true,.row fL fU),
     (true,.value (.ordinary vL) (.ordinary vU)),(true,.value (.ordinary vL) (.ordinary wU)),
     (true,.value (.ordinary wL) (.ordinary vU)),(true,.value (.ordinary wL) (.ordinary wU))]
    atName (by rfl)]
  simp [inspectContextObligation, concatenate, append, inspectContext]

/-- Same scalar term at the value position; the row atom has genuinely
different truth values in the two directions in the same real model. -/
theorem forward_row_is_not_reverse :
    let assignment : Nat → Core.PresenceGeneration.Comp Common.model :=
      fun n => (.base .int, fun o => n = 1 ∧ o = (37,[-1,2]))
    (Atom.rowLe (.var 0) (.var 1) : Atom Nat).Holds Common.model assignment ∧
      ¬ (Atom.rowLe (.var 1) (.var 0) : Atom Nat).Holds Common.model assignment := by
  change (∀ o : Common.Occurrence, 0 = 1 ∧ o = (37,[-1,2]) → 1 = 1 ∧ o = (37,[-1,2])) ∧
    ¬ (∀ o : Common.Occurrence, 1 = 1 ∧ o = (37,[-1,2]) → 0 = 1 ∧ o = (37,[-1,2]))
  exact ⟨fun o h => False.elim (Nat.zero_ne_one h.1),
    fun wrong => Nat.zero_ne_one (wrong (37,[-1,2]) ⟨rfl,rfl⟩).1⟩

theorem every_accepted_source_use_has_original_formal_positions441
    {s : I72.State} {q : I72.Request} {d : Declaration} (a : Original s q d) :
    let e := s.core.current.environment
    ∃ h ∈ e.bodies.headers, h.name = a.key ∧
      CommonRoleOutermostResolver.All₂
        (GeneralDeclarativeWitnessVariancePositions357.sourced e.graph.program) h.written modes := by
  have authorized : GeneralDeclarativeWitnessConstructorModes357.SourceMode
      s.core.current.environment a.key (.declared modes) := a.fromBody ▸ a.use.sourced
  exact GeneralDeclarativeWitnessConstructorModes357.declared_mode_from_bodies authorized

/-- These are the same two actual source positions in both mode comparisons.
A nonempty signed row is allowed forward but not conversely; the literal
value type stays the same. This is a comparator test, not a literal matcher. -/
theorem typed_ref_forward_context_distinguishes_signed_rows441
    {reg : Registry} {name : Nat} (atName : reg[name]? = some modes) :
    let full : GeneralNominalCommonBridge.Assignment :=
      fun n => (.base .int,fun o => n = 1 ∧ o = (37,[-1,2]))
    let input := fun n => Endpoint.nominal name (args (.var n) (.base .int) (.base .int))
    GeneralDeclarativeWitnessFullIntervals357.ContextDerives reg full false (input 0) (input 1) ∧
      ¬GeneralDeclarativeWitnessFullIntervals357.ContextDerives reg full false (input 1) (input 0) := by
  intro full input
  have rowsExact (e f : Nat) : compileInContext reg false (input e) (input f) =
      some [.rowLe (.var e) (.var f),.tyLe (.base .int) (.base .int),
        .tyLe (.base .int) (.base .int),.tyLe (.base .int) (.base .int),.tyLe (.base .int) (.base .int)] :=
    source_positions_forward atName (.var e) (.var f) (.base .int) (.base .int) (.base .int) (.base .int)
  have well (e : Nat) : ContextWellFormed reg false (input e) :=
    .nominal atName (.cons (.rowPoint _ _ _) (.cons
      (.valueInterval (.ordinary true _) (.ordinary true _)) (.nil false)))
  refine ⟨?_,?_⟩
  · have okay := (GeneralDeclarativeWitnessFullIntervals357.compiled_full_exact reg full false (input 0) (input 1)).mp
        (by
          rw [rowsExact,result_some]
          intro atom member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl|rfl|rfl
          · exact forward_row_is_not_reverse.1
          all_goals exact CommonNominalFullCarrier.subtype_refl _)
    exact okay.2.2
  · intro reversed
    have bad := (GeneralDeclarativeWitnessFullIntervals357.compiled_full_exact reg full false (input 1) (input 0)).mpr
      ⟨well 1,well 0,reversed⟩
    rw [rowsExact,result_some] at bad
    exact forward_row_is_not_reverse.2 (bad _ List.mem_cons_self)

end Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary
