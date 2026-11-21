import Yulang.GeneralDeclarativeInlineTrace331
import Yulang.GeneralDeclarativeEndpointProbe321
import Yulang.GeneralDeclarativeRecordInline330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineEndpoint331
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeInlineTrace331 (Read Fields realize)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeTermOccurrences322 (Positions positions)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

/-- Probe the actual endpoints independently. These witnesses neither
take a current centre as an input to matching nor require a proposed
child list or any shared capture. Readiness is a separate guard. -/
def Matches (s : State) (c : Constructors) (i : Interpretation)
    (a : GeneralDeclarativeWhere319.Capture) (pat : Pattern) : Prop :=
  Bounds s a ∧ ∃ code lo hi, translate c i (normalize pat) = some code ∧
    Read s .lower (.variable a.lower) code lo ∧ Read s .upper (.variable a.upper) code hi

def Heads (s : State) (c : Constructors) (i : Interpretation)
    (d : Demand) (impl : GeneralDeclarations.Declaration) : Prop :=
  All₂ (Matches s c i) d.arguments impl.head

/-- Positive covered cases only. Failure of an inline read is not by
definition an actual stable clash or a pending verdict. -/
def candidates (p : Supported s done) (r : GeneralDeclarations.Registry) (i : Interpretation)
    (waiting : Demand → GeneralDeclarations.Declaration → Prop) : Candidates :=
  ⟨fun d impl => HeadMatches (restriction p) r.constructors i d impl ∨
    Heads (restriction p) r.constructors i d impl,waiting⟩

theorem observed {s : State} {p : Supported s done}
    (hit : Matches (restriction p) c i a pat) :
    ∃ code l u lo hi, translate c i (normalize pat) = some code ∧
      Walk .lower lo code l ∧ Walk .upper hi code u ∧
      (∀ m, Models s m → eqAt m (.variable a.lower) lo ∧ eqAt m (.variable a.upper) hi) ∧
      Positions .lower l (GeneralDeclarativeTraceNames321.names code) ∧
      Positions .upper u (GeneralDeclarativeTraceNames321.names code) := by
  obtain ⟨_,code,l,u,written,low,high⟩ := hit
  obtain ⟨lo,fromLo,loWalk⟩ := realize low
  obtain ⟨hi,fromHi,hiWalk⟩ := realize high
  exact ⟨code,l,u,lo,hi,written,loWalk,hiWalk,fun m valid => ⟨fromLo m valid,fromHi m valid⟩,
    positions loWalk,positions hiWalk⟩

open GeneralDeclarativeRecordInline330 (payload fields taken written pat terminal rawRow initial
  remain support original actually_closed lower_ready endpoint_gap)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)

def seen (mode : GeneralNominalMaterialization.Mode) : List Occurrence :=
  [⟨0,mode,payload⟩,⟨1,mode,.variable 4⟩,⟨2,mode,remain⟩]

theorem raw_source (done : Nat → Prop) (mode) :
    Read (restriction (support done)) mode (.variable 0) (withTail written (.variable 2)) (seen mode) := by
  exact .record (.name (actually_closed done)) (keys := [7,8]) (selected := taken) (by decide)
    (by decide) rfl (.cons .capture (.cons .capture .nil)) .binder .capture

theorem actual_inline_endpoints (done : Nat → Prop) :
    Matches (restriction (support done)) catalogue interpretation (point 0) pat :=
  ⟨point_bounded _ _,_,_,_,rfl,raw_source done .lower,raw_source done .upper⟩

/-- The concrete C330 obstruction is resolved by a normalized source
view, not by appending a made-up supported constructor row. -/
theorem restores_positive_read (done : Nat → Prop) :
    Matches (restriction (support done)) catalogue interpretation (point 0) pat ∧
      ¬GeneralDeclarativeEndpointProbe321.Matches (restriction (support done)) catalogue interpretation (point 0) pat := by
  refine ⟨actual_inline_endpoints _,?_⟩
  rintro ⟨_,code,lo,_,shown,old,_⟩
  change some (withTail written (.variable 2)) = some code at shown
  cases Option.some.inj shown
  exact endpoint_gap done .lower ⟨lo,old⟩

end Yulang.GeneralDeclarativeInlineEndpoint331
