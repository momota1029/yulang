import Yulang.GeneralRebaseWeakExit298

namespace Yulang.GeneralRebaseWeakWindow298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseRevisitedTrace298 (Family)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseWeakProgress268 (Lull Weak)
open GeneralSourceState (Output)
open GeneralRebaseWeakExit298 (View fromState exits)
open GeneralRebaseFiniteSublists298 (choices choices_exact choices_count samples_sourced)
open GeneralRebaseFiniteWitnessTable297 (samples)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {checked : (Boundary roles).Checked r}

def realizes (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (query : List Fact) (mid : State roles) : Prop :=
  Lull (Encoded r) root owners pool s mid ∧
    ∃ target ∈ fromState codes owners pool s mid, target.remaining = query

noncomputable def window (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) : List (State roles) :=
  samples (realizes codes owners pool s) (choices (project owners pool s).remaining)

theorem window_size (codes : Family r root checked) (owners : List Nat) (pool : List Output) (s : State roles) :
    (window codes owners pool s).length ≤ 2 ^ (project owners pool s).remaining.length := by
  rw [←choices_count]
  exact GeneralRebaseFiniteWitnessTable297.length_le _ _

theorem genuine (codes : Family r root checked) (owners : List Nat) (pool : List Output) (s m : State roles)
    (listed : m ∈ window codes owners pool s) : Lull (Encoded r) root owners pool s m := by
  obtain ⟨_,_,use⟩ := samples_sourced (realizes codes owners pool s) _ m listed
  exact use.1

theorem enough (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s m : State roles) (target : View owners pool)
    (silent : Lull (Encoded r) root owners pool s m) (found : target ∈ fromState codes owners pool s m) :
    target ∈ exits codes owners pool s (window codes owners pool s) := by
  let q := target.remaining
  have admissible : q ∈ choices (project owners pool s).remaining :=
    (choices_exact ..).mpr (GeneralRebaseWeakExit298.target_sublist codes owners pool s m target found)
  obtain ⟨representative,listed,_,witness,emitted,same⟩ :=
    GeneralRebaseFiniteWitnessTable297.covers (realizes codes owners pool s)
      (choices (project owners pool s).remaining) q admissible ⟨m,silent,target,found,rfl⟩
  have equal : witness = target := GeneralRebaseStep258.state_ext _ _ same
  exact List.mem_flatMap.mpr ⟨representative,listed,equal ▸ emitted⟩

theorem exact (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) (target : View owners pool) :
    target ∈ exits codes owners pool s (window codes owners pool s) ↔
    ∃ after, Weak (Encoded r) root owners pool s after ∧ project owners pool after = target := by
  refine ⟨GeneralRebaseWeakExit298.sound_window seen owners pool _ (genuine codes owners pool s) target,?_⟩
  rintro ⟨after,weak,rfl⟩
  obtain ⟨m,silent,found⟩ := GeneralRebaseWeakExit298.completeness (codes := codes) seen owners pool weak
  exact enough codes owners pool s m _ silent found

/-- List indexing over the supplied window is executable; the fallback
model universe and the raw prefix search are not enumerated here. -/
def targetCodes (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (representatives : List (State roles)) : List (List Fact) :=
  ((exits codes owners pool s representatives).map (·.remaining)).eraseDups

theorem target_codes_exact (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) (result : List Fact) :
    result ∈ targetCodes codes owners pool s (window codes owners pool s) ↔
    ∃ after, Weak (Encoded r) root owners pool s after ∧ (project owners pool after).remaining = result := by
  unfold targetCodes
  rw [List.mem_eraseDups,List.mem_map]
  constructor
  · rintro ⟨t,listed,rfl⟩
    obtain ⟨after,weak,eq⟩ := (exact codes owners pool s seen t).mp listed
    exact ⟨after,weak,congrArg GeneralRebaseStep258.State.remaining eq⟩
  · rintro ⟨after,weak,eq⟩
    exact ⟨project owners pool after,
      (exact codes owners pool s seen _).mpr ⟨after,weak,rfl⟩,eq⟩

theorem no_weak_iff (codes : Family r root checked) (owners : List Nat) (pool : List Output)
    (s : State roles) (seen : B4TargetV8.Reachable (Boundary roles) r root s) :
    targetCodes codes owners pool s (window codes owners pool s) = [] ↔
    ∀ after, ¬ Weak (Encoded r) root owners pool s after := by
  constructor
  · intro empty after weak
    have found := (target_codes_exact codes owners pool s seen _).mpr ⟨after,weak,rfl⟩
    rw [empty] at found
    cases found
  · intro never
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro result found
    obtain ⟨after,w,_⟩ := (target_codes_exact codes owners pool s seen result).mp found
    exact never after w

end Yulang.GeneralRebaseWeakWindow298
