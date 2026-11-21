import Yulang.GeneralDeclarativeNominalTrace323
import Yulang.GeneralDeclarativeNamedTree320
import Yulang.GeneralDeclarativeEndpointProbe321
import Yulang.GeneralDeclarativePriority321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalClash324
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs Local Visible)
open GeneralDeclarativeNamedTree320 (position)
open GeneralDeclarativeNominalTrace323 (lower_nominal_sits)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open CommonNominalFullCarrier (nominal_regular_invariant_exact subtype_trans)
open GeneralDeclarations (Declaration Registry)

def Clash (s : State) (c : Constructors) (interp : Interpretation)
    (arg : GeneralDeclarativeWhere319.Capture) (p : Pattern) : Prop :=
  ∃ observed proposed expression query,
    Derives s (.variable arg.lower) (.nominal observed expression) ∧
    translate c interp (normalize p) = some (.nominal proposed query) ∧ observed ≠ proposed

theorem clashes {s : State} (valid : Models s m) (conflict : Clash s c interp arg p) :
    ¬Matches s c interp arg p := by
  rintro ⟨bounds,code,low,high,printed,trace,upper⟩
  obtain ⟨owner,proposal,xs,ps,origin,translated,different⟩ := conflict
  have codeEq := Option.some.inj (printed.symm.trans translated)
  subst code
  obtain ⟨_,seen⟩ := lower_nominal_sits trace
  have first := entails origin m valid
  have second := entails seen m valid
  have exactly := (nominal_regular_invariant_exact ..).mp (subtype_trans first.2 second.1)
  exact different exactly.1

def AtHead (s : State) (c : Constructors) (interp : Interpretation)
    (d : Demand) (decl : Declaration) : Prop :=
  ∃ (index : Nat), ∃ arg p, d.arguments[index]? = some arg ∧ decl.head[index]? = some p ∧ Clash s c interp arg p

theorem eliminates {s : State} (valid : Models s m) (conflict : AtHead s c interp d decl) :
    ¬HeadMatches s c interp d decl := by
  intro all
  obtain ⟨i,arg,p,first,second,incompatible⟩ := conflict
  exact clashes valid incompatible (position all first second)

def tests (s : State) (c : Constructors) (interp : Interpretation) : Candidates :=
  ⟨HeadMatches s c interp,fun d decl => ¬HeadMatches s c interp d decl ∧ ¬AtHead s c interp d decl⟩

/-- A known nominal clash is elimination, not an unresolved probe.
Uncovered negative cases still do not claim a general classifier. -/
theorem genuine_selected {s : State} (p : Supported s completed)
    (valid : Models (restriction p) m) (known : Ready p d)
    (safe : ¬Recurs s r interp (tests (restriction p) r.constructors interp) d)
    (winner : Visible r d impl)
    (matched : HeadMatches (restriction p) r.constructors interp d impl)
    (others : ∀ rival, Visible r d rival → rival ≠ impl →
      AtHead (restriction p) r.constructors interp d rival)
    (emitted : generates d impl kids) :
    Local s r interp p (tests (restriction p) r.constructors interp) generates d (.selected impl.id kids) := by
  refine .selected known safe ?_ ⟨winner,matched⟩ ?_ emitted
  · rintro ⟨other,view,notPossible,notClash⟩
    classical
    by_cases same : other = impl
    · subst other
      exact notPossible matched
    · exact notClash (others _ view same)
  · rintro other ⟨view,matchOther⟩
    classical
    by_cases same : other = impl
    · cases same
      rfl
    · exact False.elim (eliminates valid (others _ view same) matchOther)

end Yulang.GeneralDeclarativeNominalClash324
