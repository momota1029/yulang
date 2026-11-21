import Yulang.GeneralDeclarativeExactWalk323
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlainCapture323
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralCandidateInspection (plainNames)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (union_congr eqv_trans eqv_symm)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl common_union_is_join)
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeExactWalk323 (variant_exact)
open GeneralNominalCommonBridge (Assignment)

/-- The existing approved inspection compiler asks for *one* whole
payload when the normalized tag has a plain variable list. -/
theorem actual_probe (found : plainNames payload = some names) :
    GeneralNominalInspection.translate c interp (.variant tag payload) =
      .node (.variant tag) [.variables names] := by
  simp [GeneralNominalInspection.translate,found]

theorem union_same (x : Ty) : Equivalent (.union x x) x :=
  ⟨(common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩,
    (common_union_is_join ..).mp (subtype_refl (.union x x)) |>.1⟩

theorem whole {m : Assignment} {cap : Nat → Capture} {p : Pattern}
    (plain : plainNames p = some names)
    (compiled : translate c interp p = some code)
    (samePayload : ∀ name ∈ names, Equivalent (m (cap name).center).1 entire) :
    Equivalent (value (variables cap m) .actual code) entire := by
  cases p with
  | var n =>
    have real : [n] = names := Option.some.inj plain
    have written : Expr.variable n = code := Option.some.inj compiled
    cases real
    cases written
    simpa only [value,GeneralDeclarativeHead320.variables_eq,GeneralDeclarativeHead320.byMode] using
      samePayload n List.mem_cons_self
  | join first last =>
    cases x : plainNames first with
    | none => simp [plainNames,x] at plain
    | some a =>
      cases y : plainNames last with
      | none => simp [plainNames,x,y] at plain
      | some b =>
        have exactNames : a ++ b = names := by simpa [plainNames,x,y] using plain
        subst names
        cases c1 : translate c interp first with
        | none => simp [translate,c1] at compiled
        | some e =>
          cases c2 : translate c interp last with
          | none => simp [translate,c1,c2] at compiled
          | some f =>
            have exactCode : Expr.join e f = code := by simpa [translate,c1,c2] using compiled
            subst code
            have f1 := whole (p := first) x c1 (fun name shown => samePayload name (List.mem_append_left _ shown))
            have f2 := whole (p := last) y c2 (fun name shown => samePayload name (List.mem_append_right _ shown))
            exact eqv_trans (union_congr f1 f2) (union_same entire)
  | app | record | variant => cases plain
termination_by sizeOf p

def WholeNames (s : State) (cap : Nat → Capture) (payload : Expr) (names : List Nat) : Prop :=
  ∀ name ∈ names, Entails s ⟨(cap name).center,payload⟩

/-- Arbitrary nesting of the source's plain-variable payload join.
The whole actual payload supplies all occurrences. It would be wrong
to recover its allocation among names from equality of a union. -/
theorem tag_head {s : State} {p : Pattern}
    (normal : normalize p = .variant tag merged)
    (names : plainNames merged = some which)
    (payloadSyntax : translate catalogue interp merged = some code)
    (original : translate catalogue interp p = some raw)
    (actual : Entails s ⟨arg.center,.variant tag sourcePayload⟩)
    (same : WholeNames s cap sourcePayload which) :
    Result s (headFact catalogue interp cap arg p) := by
  refine ⟨[⟨arg.center,logical cap .actual raw⟩],by simp [headFact,original],?_⟩
  intro row listed m valid
  cases List.mem_singleton.mp listed
  have normCode : translate catalogue interp (normalize p) = some (.variant tag code) := by
    simp [normal,translate,payloadSyntax]
  have lowered := translate_value (normalize p) (variables := variables cap m) normCode
  have payload := whole (m := m) (cap := cap) (entire := value (environment m) .actual sourcePayload) names payloadSyntax
    (fun name used => same name used m valid)
  have branch := (variant_exact tag _ _).mpr (eqv_symm payload)
  simp only [Holds,logical_value]
  have reflected := compiled_normalized (variables := variables cap m) original
  rw [← lowered] at reflected
  exact eqv_trans (actual m valid)
    (eqv_trans branch (eqv_symm reflected))

end Yulang.GeneralDeclarativePlainCapture323
