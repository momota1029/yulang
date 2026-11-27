import Yulang.GeneralDeclarativeI65I74SameBooleanFieldStamp461
import Yulang.GeneralDeclarativeI65I74EarlierHomogeneousScope461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open RoutedNominalMixed456 (actualQueryDecoder)
open EligibleFieldStart461
open RoutedReadyMixed457 (ReportAtField)
open WrittenPattern460

def fromProjected {p : Problem} {d : Declaration}
    (h : ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d) :
    EligibleStart p :=
  ⟨d,h.written,h.clause,h.arg,h.query,h.only,h.head,h.requirement,h.argv,h.atCenter,
    h.noGoalOutputs,h.noWhereOutputs,h.authoredRole,h.rolesValid,
    ProjectedReadyHeader459.exact_projected_header_supplies_original_ready459 h,h.translated⟩

def alreadyProjected (p : Problem) : OriginalHeaderProtocol p where
  Header := ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core)
  toStart := fun _ => fromProjected
  read := ProjectedReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core)
  singleton := fun a => a.only
  ticket := fun a => a.emptyKey
  replay := ProjectedReadyHeader459.actual_original_projected_header_replays459

inductive Provider where
  | plain | projected | homogeneous
  deriving DecidableEq

def provider (p : Problem) : Provider → OriginalHeaderProtocol p
  | .plain => alreadyReady p
  | .projected => alreadyProjected p
  | .homogeneous => alreadyHomogeneous p

structure Ticket where
  author : Provider
  key : Nat

def anyInstalled {p : Problem} (a : EligibleStart p) : Prop :=
  ∃ i : Provider, actualHeaderAuthority (provider p i) a

def pickHeader (p : Problem) (t : Ticket) : Option (EligibleStart p) :=
  readActualHeader (provider p t.author) t.key

theorem exact_pick_header_iff_independent_author {p : Problem} {a : EligibleStart p} :
    (∃ t, pickHeader p t = some a) ↔ anyInstalled a := by
  constructor
  · rintro ⟨⟨i,k⟩,ok⟩
    exact ⟨i,(genuine_independent_start_iff_finite_header_ticket _ _).mp ⟨k,ok⟩⟩
  · rintro ⟨i,auth⟩
    obtain ⟨k,ok⟩ := (genuine_independent_start_iff_finite_header_ticket _ _).mpr auth
    exact ⟨⟨i,k⟩,ok⟩

def installedRead (p : Problem) : ReadyRead p :=
  ⟨Ticket,anyInstalled,pickHeader p,fun _ => exact_pick_header_iff_independent_author⟩

abbrev InstalledWire (p : Problem) := EligibleWire (installedRead p)

def dispatchReport {p : Problem} (w : InstalledWire p) : Option (ReportAtField × Bool) :=
  readSourceAndFieldStamp (installedRead p) w

theorem same_program_for_each_chosen_author {p : Problem} (i : Provider)
    (w : EligibleWire (exactHeaderReader (provider p i))) :
    dispatchReport (⟨⟨i,w.start⟩,w.along⟩ : InstalledWire p) =
      readSourceAndFieldStamp (exactHeaderReader (provider p i)) w := rfl

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
