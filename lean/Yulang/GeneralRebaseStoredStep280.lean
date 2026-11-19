import Yulang.GeneralRebaseArchiveReplay280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseStoredStep280
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseArchiveReplay280 (strip restore source_roundtrip)

def StoredStep (r : Registry) (root : Occurrence roles) (memory next : State roles) : Prop :=
  ∃ raw, (boundary roles).Step r root (restore memory) raw ∧ next = strip raw

theorem same_strip {r : Registry} {root : Occurrence roles} {start a b : State roles}
    (init : (boundary roles).Initial r root start)
    (first : B4Target.Steps ((boundary roles).Step r root) start a)
    (second : B4Target.Steps ((boundary roles).Step r root) start b) :
    strip a = strip b ↔ a = b := by
  constructor
  · intro equal
    have decoded := congrArg restore equal
    rwa [source_roundtrip init first,source_roundtrip init second] at decoded
  · rintro rfl
    rfl

theorem step {r : Registry} {root : Occurrence roles} {start a : State roles}
    (init : (boundary roles).Initial r root start)
    (first : B4Target.Steps ((boundary roles).Step r root) start a) (mem : State roles) :
    StoredStep r root (strip a) mem ↔
      ∃ raw, (boundary roles).Step r root a raw ∧ mem = strip raw := by
  unfold StoredStep
  rw [source_roundtrip init first]

theorem match_state {r : Registry} {root : Occurrence roles} {start a b : State roles}
    (init : (boundary roles).Initial r root start)
    (first : B4Target.Steps ((boundary roles).Step r root) start a)
    (second : B4Target.Steps ((boundary roles).Step r root) start b) :
    StoredStep r root (strip a) (strip b) ↔ (boundary roles).Step r root a b := by
  rw [step init first]
  constructor
  · rintro ⟨raw,go,h⟩
    have eq := (same_strip init second (.tail first go)).mp h
    exact eq.symm ▸ go
  · intro go
    exact ⟨b,go,rfl⟩

theorem stored_path {r : Registry} {root : Occurrence roles} {start finish : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start finish) :
    B4Target.Steps (StoredStep r root) (strip start) (strip finish) := by
  induction path with
  | refl => exact .refl
  | tail earlier transition ih =>
    exact .tail ih ((step init earlier _).mpr ⟨_,transition,rfl⟩)

theorem original_path {r : Registry} {root : Occurrence roles} {start finish : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps (StoredStep r root) (strip start) finish) :
    ∃ raw, B4Target.Steps ((boundary roles).Step r root) start raw ∧ strip raw = finish := by
  induction path with
  | refl => exact ⟨start,.refl,rfl⟩
  | tail earlier transition ih =>
    obtain ⟨raw,trace,rfl⟩ := ih
    obtain ⟨out,go,rfl⟩ := (step init trace _).mp transition
    exact ⟨out,.tail trace go,rfl⟩

theorem acc_forward {r : Registry} {root : Occurrence roles} {start a : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start a)
    (terminates : Acc (fun after before => (boundary roles).Step r root before after) a) :
    Acc (fun after before => StoredStep r root before after) (strip a) := by
  induction terminates with
  | intro a _ ih =>
    refine Acc.intro (strip a) ?_
    intro next transition
    obtain ⟨out,actual,rfl⟩ := (step init path _).mp transition
    exact ih out actual (.tail path actual)

theorem acc_backward {r : Registry} {root : Occurrence roles} {start a mem : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start a)
    (packed : strip a = mem)
    (terminates : Acc (fun after before => StoredStep r root before after) mem) :
    Acc (fun after before => (boundary roles).Step r root before after) a := by
  induction terminates generalizing a with
  | intro mem _ ih =>
    subst mem
    refine Acc.intro a ?_
    intro out go
    exact ih (strip out) ((step init path _).mpr ⟨out,go,rfl⟩) (.tail path go) rfl

theorem acc_exact {r : Registry} {root : Occurrence roles} {start a : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start a) :
    Acc (fun after before => (boundary roles).Step r root before after) a ↔
      Acc (fun after before => StoredStep r root before after) (strip a) :=
  ⟨acc_forward init path,acc_backward init path rfl⟩

theorem terminal_exact {r : Registry} {root : Occurrence roles} {start a : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start a) :
    (¬ ∃ out, StoredStep r root (strip a) out) ↔ (boundary roles).Stable r a root := by
  change (¬ ∃ out, StoredStep r root (strip a) out) ↔
    GeneralNominalVersionedMixedKernel234.Stable _ a root
  rw [GeneralRebaseCompactAvailability279.stable_iff_not_step]
  apply not_congr
  constructor
  · rintro ⟨mem,has⟩
    obtain ⟨raw,edge,_⟩ := (step init path _).mp has
    exact ⟨raw,edge⟩
  · rintro ⟨out,edge⟩
    exact ⟨strip out,(step init path _).mpr ⟨out,edge,rfl⟩⟩

end Yulang.GeneralRebaseStoredStep280
