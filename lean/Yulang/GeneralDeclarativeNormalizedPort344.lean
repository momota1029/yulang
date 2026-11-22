import Yulang.GeneralDeclarativePolarCompiler344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizedPort344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralWhereVersionCompiler317 (child schema emit)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCenteredHeadMatSchemas (generated materialize emissionRequests)
open GeneralNominalMaterialization (Request Mode)
open GeneralWhereOriginSchema318 (input)
open GeneralDeclarativeCommitModes344 (emitted_mem endpoint_request all_modes)
open GeneralDeclarativeCommitPort344 (OperandMatch literal_mode)
open GeneralDeclarativePolarCompiler344 (normalized_codes)
open GeneralDeclarativeModeCongruence344 (expression)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeClauseBatch327 (Input Port)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralStoppedOrdinarySite335 (argument)
open GeneralStoppedPlacement335 (Meaning)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleOutermostResolver (All₂)

theorem translate_at {c : Constructors} {interp : Interpretation} {qs : List Request}
    (complete : (generated c interp qs).unknown = false) {req : Request} (there : req ∈ qs) :
    ∃ e, translate c interp req.pattern = some e := by
  induction qs with
  | nil => cases there
  | cons hd tl ih =>
    have steps := Bool.or_eq_false_iff.mp complete
    rcases List.mem_cons.mp there with same|later
    · subst hd
      cases written : translate c interp req.pattern with
      | some e => exact ⟨e,rfl⟩
      | none =>
        have impossible : (materialize c interp req).unknown = false := steps.1
        simp [materialize,written] at impossible
    · exact ih steps.2 later

theorem genuine_code (p : Plan rs) (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (idx : Fin (rs cl.role).arity) (m : Assignment) (typed : Holds p m) :
    ∃ e, translate p.packet.registry.constructors p.packet.context.interpretation
      (cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt)) = some e := by
  have listed : input p cl sig idx .lower ∈
      GeneralNominalMaterialization.rootRequests p.packet.declaration p.packet.site.occurrence ++
        (GeneralWhereVersionCompiler317.emissions p).flatMap emissionRequests :=
    List.mem_append_right _
      (List.mem_flatMap.mpr ⟨emit p cl sig,emitted_mem p cl inside sig,endpoint_request p cl sig idx .lower⟩)
  exact translate_at typed.materialized listed

theorem on_right {rel : α → β → Prop} {xs : List α} {ys : List β} (aligned : All₂ rel xs ys)
    {idx : Nat} {a : α} (there : xs[idx]? = some a) :
    ∃ b, ys[idx]? = some b ∧ rel a b := by
  induction aligned generalizing idx with
  | nil => cases there
  | @cons x y xs ys here later ih =>
    cases idx with
    | zero =>
      have eq : x = a := Option.some.inj there
      subst x
      exact ⟨y,rfl,here⟩
    | succ n => exact ih there

theorem prepared_code {s : State} {c : Constructors} {interp : Interpretation} {cap : Nat → Capture}
    {cl : Clause} {port : Port} (compiled : Input s c interp cap cl port)
    {idx : Nat} {pat : Pattern} (there : cl.arguments[idx]? = some pat) :
    ∃ code, port.code[idx]? = some code ∧ translate c interp (normalize pat) = some code :=
  on_right (GeneralDeclarativeClauseOrigins325.normalized_order compiled.1) there

/-- The raw code is obtained from the complete genuine packet; the
ordinary code is obtained from the actual prepared compiler port. The
codes need not coincide. Matching only the normalized operand reads
is enough, including under nested invariant nominal applications. -/
theorem compound (p : Plan rs) (cl : Clause) (inside : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (idx : Fin (rs cl.role).arity) (m : Assignment)
    (typed : Holds p m) {s : State} (fit : Models s m) (cap : Nat → Capture) (port : Port)
    (prepared : Input s p.packet.registry.constructors p.packet.context.interpretation cap cl port)
    (pat : Pattern) (located : cl.arguments[idx.val]? = some pat) (shape : Compound pat)
    (agree : ∀ code, port.code[idx.val]? = some code → ∀ mode, OperandMatch p m cap mode code) :
    Meaning m (argument (child p cl sig) idx) (port.input idx.val) := by
  obtain ⟨rawCode,rawPrinted⟩ := genuine_code p cl inside sig idx m typed
  obtain ⟨code,written,canon⟩ := prepared_code prepared located
  have actualPat : cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt) = pat :=
    (List.getElem?_eq_some_iff.mp located).2
  have byPat : translate p.packet.registry.constructors p.packet.context.interpretation pat = some rawCode :=
    actualPat ▸ rawPrinted
  have modes := all_modes p cl inside sig idx m typed rawCode rawPrinted
  have normalized (mode : Mode) :
      Equivalent (value (variables p m) mode rawCode)
        (value (GeneralDeclarativeWhere319.variables cap m) mode code) :=
    eqv_trans (normalized_codes (variables := variables p m) byPat canon mode)
      (expression _ _ mode code (agree code written mode))
  have origin := (prepared.2 idx.val pat code located written shape).2
  exact ⟨eqv_trans modes.1 (eqv_trans (normalized .lower) (eqv_symm (literal_mode cap origin.1 m fit))),
    eqv_trans modes.2.1 (eqv_trans (normalized .actual) (eqv_symm (literal_mode cap origin.2.1 m fit))),
    eqv_trans modes.2.2 (eqv_trans (normalized .upper) (eqv_symm (literal_mode cap origin.2.2 m fit)))⟩

end Yulang.GeneralDeclarativeNormalizedPort344
