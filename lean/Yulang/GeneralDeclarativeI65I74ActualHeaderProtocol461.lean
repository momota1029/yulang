import Yulang.GeneralDeclarativeI65I74EligibleFieldReader461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open RoutedNominalMixed456 (actualQueryDecoder)
open Checker408 (Problem)

/-- Readiness is supplied by a genuine, reflected source producer.
Changing the producer does not specialize, replace or duplicate the structural reader. -/
structure OriginalHeaderProtocol (p : Problem) where
  Header : Declaration → Type
  toStart : (d : Declaration) → Header d → EligibleStart p
  read : (d : Declaration) → visible p.state.core p.root = [d] → Nat → Option (Header d)
  singleton : ∀ {d}, Header d → visible p.state.core p.root = [d]
  ticket : ∀ {d}, Header d → Nat
  replay : ∀ {d} (a : Header d), read d (singleton a) (ticket a) = some a

def readActualHeader {p : Problem} (h : OriginalHeaderProtocol p) (key : Nat) :
    Option (EligibleStart p) :=
  match atSource : visible p.state.core p.root with
  | [d] => (h.read d atSource key).map (h.toStart d)
  | _ => none

def actualHeaderAuthority {p : Problem} (h : OriginalHeaderProtocol p)
    (a : EligibleStart p) : Prop :=
  ∃ (d : Declaration) (source : h.Header d), h.toStart d source = a

theorem genuine_start_replays_at_its_own_header_ticket {p : Problem}
    (h : OriginalHeaderProtocol p) {d : Declaration} (a : h.Header d) :
    readActualHeader h (h.ticket a) = some (h.toStart d a) := by
  unfold readActualHeader
  split
  · rename_i chosen seen
    have same := List.singleton_inj.mp (seen.symm.trans (h.singleton a))
    subst chosen
    rw [h.replay a]
    rfl
  · rename_i missed
    exact (missed _ (h.singleton a)).elim

theorem genuine_independent_start_iff_finite_header_ticket {p : Problem}
    (h : OriginalHeaderProtocol p) (a : EligibleStart p) :
    (∃ t, readActualHeader h t = some a) ↔ actualHeaderAuthority h a := by
  constructor
  · rintro ⟨key,accepted⟩
    unfold readActualHeader at accepted
    split at accepted
    · rename_i d seen
      obtain ⟨source,_,eq⟩ := Option.map_eq_some_iff.mp accepted
      exact ⟨d,source,eq⟩
    · cases accepted
  · rintro ⟨d,e,rfl⟩
    exact ⟨h.ticket e,genuine_start_replays_at_its_own_header_ticket h e⟩

def exactHeaderReader {p : Problem} (h : OriginalHeaderProtocol p) : ReadyRead p :=
  ⟨Nat,actualHeaderAuthority h,readActualHeader h,genuine_independent_start_iff_finite_header_ticket h⟩

def alreadyReady (p : Problem) : OriginalHeaderProtocol p where
  Header := RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core)
  toStart := fun _ => fromReady
  read := RoutedReadyHeader457.readReadyHeader p (actualQueryDecoder p.state.core)
  singleton := fun a => a.only
  ticket := fun a => a.emptyKey
  replay := RoutedReadyHeader457.exact_same_written_local_ready_header_replays457

def alreadyHomogeneous (p : Problem) : OriginalHeaderProtocol p where
  Header := HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core)
  toStart := fun _ => fromHomogeneous
  read := HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core)
  singleton := fun a => a.only
  ticket := fun a => a.emptyKey
  replay := HomogeneousReadyHeader459.actual_original_homogeneous_header_replays459

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
