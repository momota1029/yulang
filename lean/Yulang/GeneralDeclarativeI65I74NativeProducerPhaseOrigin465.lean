import Yulang.GeneralDeclarativeI65I74NativeProducerNodeCheck465
import Yulang.GeneralDeclarativeI65NativePrefix369
import Yulang.GeneralDeclarativeI65I74IssuedProjection464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeInstall360 (World Board interpreted)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority Released ExactRelease openWrite checkExactRelease)
open RecordTrail455 (checkOriginalRoute original_route_iff_data455)

/-- A separately supplied existing native world with exact ordinary
identity. This does not create a board, a grant, a native origin or an edge. -/
structure CheckedPhase (s : GeneralDeclarativeI65.State) where
  world : World
  atCurrent : world.ordinary = s.current.ordinary
  gate : ReleaseAuthority

theorem each_independent_active_address_replays {b : Board} {gate : ReleaseAuthority}
    {q : GeneralDeclarativeWitnessNativeValue360.Address} (h : Released b gate q) :
    openWrite b gate q = some h := by
  rcases h with ⟨stored,loc,eq,active,unique,grant⟩
  unfold openWrite
  split
  · rename_i absent
    rw [loc] at absent
    cases absent
  · rename_i actual seen
    have same := Option.some.inj (seen.symm.trans loc)
    subst actual
    simp [eq,active,unique,grant]

theorem checked_exact_release_iff_independent_address
    (b : Board) (gate : ReleaseAuthority) (w : Write) :
    (checkExactRelease b gate w).isSome = true ↔ Nonempty (ExactRelease b gate w) := by
  constructor
  · intro h
    cases it : checkExactRelease b gate w with
    | some found => exact ⟨found⟩
    | none => simp [it] at h
  · rintro ⟨⟨h,same⟩⟩
    simp [checkExactRelease,each_independent_active_address_replays h,Option.bind,same]

def checksOriginValue (w : Write) (o : Origin) : Bool :=
  decide (o.slot = w.address.target ∧ o.issuer = w.address.owner.path) && matchesNode w.code o.endpoint

theorem checks_origin_value_exactly (w : Write) (o : Origin) :
    checksOriginValue w o = true ↔ o = originalOfWrite w := by
  rcases o with ⟨slot,issuer,term⟩
  simp only [checksOriginValue,originalOfWrite,Bool.and_eq_true,decide_eq_true_eq,
    checked_compiler_node_recovers_exact_endpoint,Origin.mk.injEq]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2.symm⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2.symm⟩⟩

def checkPhaseOrigin {s : GeneralDeclarativeI65.State} (p : CheckedPhase s)
    (w : Write) (logical ordinal : Nat) : Bool :=
  match s.origins[ordinal]? with
  | none => false
  | some o => checksOriginValue w o && checkOriginalRoute s o logical &&
    (checkExactRelease p.world.board p.gate w).isSome

def PhaseOriginAt {s : GeneralDeclarativeI65.State} (p : CheckedPhase s)
    (w : Write) (logical ordinal : Nat) : Prop :=
  s.origins[ordinal]? = some (originalOfWrite w) ∧
    OriginRoute s (originalOfWrite w) logical ∧
    Nonempty (ExactRelease p.world.board p.gate w)

theorem finite_phase_origin_check_iff_literal_placed_active_row {s : GeneralDeclarativeI65.State}
    (p : CheckedPhase s) (w : Write) (logical ordinal : Nat) :
    checkPhaseOrigin p w logical ordinal = true ↔ PhaseOriginAt p w logical ordinal := by
  constructor
  · intro yes
    cases got : s.origins[ordinal]? with
    | none => simp [checkPhaseOrigin,got] at yes
    | some o =>
      have actual : (o = originalOfWrite w ∧ OriginRoute s o logical) ∧
          Nonempty (ExactRelease p.world.board p.gate w) := by
        simpa only [checkPhaseOrigin,got,Bool.and_eq_true,checks_origin_value_exactly,
          original_route_iff_data455,checked_exact_release_iff_independent_address] using yes
      exact ⟨actual.1.1 ▸ got,actual.1.1 ▸ actual.1.2,actual.2⟩
  · rintro ⟨hit,route,released⟩
    simp only [checkPhaseOrigin,hit,Bool.and_eq_true,checks_origin_value_exactly,
      original_route_iff_data455,checked_exact_release_iff_independent_address]
    exact ⟨⟨True.intro,route⟩,released⟩

theorem checked_phase_read_reaches_the_existing_native_authorization {s : GeneralDeclarativeI65.State}
    {p : CheckedPhase s} {w : Write} {logical ordinal : Nat}
    (checks : checkPhaseOrigin p w logical ordinal = true) :
    Nonempty (AuthorizedEndpoint s (fun o => Nonempty (CurrentReleasedOrigin s o)) logical) := by
  obtain ⟨i,route,⟨active⟩⟩ := (finite_phase_origin_check_iff_literal_placed_active_row ..).mp checks
  exact ⟨endpointFromCurrentRelease ⟨p.world,p.atCurrent,p.gate,w,active,rfl,rfl,rfl⟩
    (List.mem_of_getElem? i) route⟩

theorem actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    {s : GeneralDeclarativeI65.State} {p : CheckedPhase s} {w : Write} {logical ordinal : Nat}
    (checks : checkPhaseOrigin p w logical ordinal = true)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    m.nativeSyntax w.address.target = some (node w.code) ∧
    interpreted p.world.board m.assignment w.address.target = some (w.code.eval m.assignment) := by
  obtain ⟨literal,route,⟨released⟩⟩ := (finite_phase_origin_check_iff_literal_placed_active_row ..).mp checks
  refine ⟨fit.2 (originalOfWrite w) (List.mem_of_getElem? literal),?_⟩
  apply GeneralDeclarativeWitnessNativeRelease360.checked_exact_written_value released
  exact ⟨p.atCurrent ▸ fit.1.1,fun _ => rfl⟩

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
