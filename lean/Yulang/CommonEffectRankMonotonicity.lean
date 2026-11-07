import Yulang.CommonEffectLatticeUniversals

/-! Finite negative-rank comparisons and their environment footprint.
The rank decrease is proved by reconstructing arbitrary negative tests from
the finite list of domains, rather than assuming pointwise monotonicity of
individual probes. This is groundwork for finite constructor saturation. -/
namespace Yulang.CommonEffectRankMonotonicity
open Common (Row)
open CommonFinite (Ty Environment Observation ProbeAt MaskedProbeStep)

abbrev Compare (rank : Nat) (source target : Ty Row) : Prop :=
  ∀ env obs, ProbeAt Common.rowLe rank env target obs → ProbeAt Common.rowLe rank env source obs

def domains : Ty Row → List (Ty Row)
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => domains first ++ domains last
  | .variant _ body | .mask _ body => domains body
  | .arrow arg _ result _ => arg :: (domains arg ++ domains result)
  | _ => []

theorem step_environment (before after : Environment Row) (oldOrder newOrder : Ty Row → Ty Row → Prop)
    (roles : before.roles = after.roles) (type : Ty Row) (hidden : List Nat) (obs : Observation Row)
    (arguments : ∀ name domain, domain ∈ domains type →
      (oldOrder (before.types name) domain ↔ newOrder (after.types name) domain)) :
    MaskedProbeStep Common.rowLe before oldOrder hidden type obs ↔
      MaskedProbeStep Common.rowLe after newOrder hidden type obs := by
  induction type generalizing hidden obs with
  | union a b iha ihb =>
    have ah := fun name domain member => arguments name domain (List.mem_append_left _ member)
    have bh := fun name domain member => arguments name domain (List.mem_append_right _ member)
    rw [CommonFinite.maskedProbeStep_union, CommonFinite.maskedProbeStep_union]
    exact and_congr (iha hidden obs ah) (ihb hidden obs bh)
  | inter a b iha ihb =>
    have ah := fun name domain member => arguments name domain (List.mem_append_left _ member)
    have bh := fun name domain member => arguments name domain (List.mem_append_right _ member)
    rw [CommonFinite.maskedProbeStep_inter, CommonFinite.maskedProbeStep_inter]
    exact or_congr (iha hidden obs ah) (ihb hidden obs bh)
  | pair a b iha ihb | record label a b iha ihb | recordDefault label a b iha ihb =>
    have ah := fun name domain member => arguments name domain (List.mem_append_left _ member)
    have bh := fun name domain member => arguments name domain (List.mem_append_right _ member)
    have firstExact := fun hidden obs => iha hidden obs ah
    have lastExact := fun hidden obs => ihb hidden obs bh
    cases obs <;> simp_all only [MaskedProbeStep]
  | variant label body ih =>
    have bodyExact := fun hidden obs => ih hidden obs arguments
    cases obs <;> simp_all only [MaskedProbeStep, domains]
  | mask more body ih =>
    rw [CommonFinite.maskedProbeStep_mask, CommonFinite.maskedProbeStep_mask]
    exact ih (hidden ++ more) obs arguments
  | arrow arg incoming result outgoing _ ihr =>
    have outputArguments := fun name domain member => arguments name domain
      (List.mem_cons_of_mem _ (List.mem_append_right _ member))
    have outputExact := fun hidden obs => ihr hidden obs outputArguments
    cases obs <;> simp_all only [MaskedProbeStep]
    exact arguments _ arg List.mem_cons_self
  | _ => cases obs <;> simp_all only [MaskedProbeStep]

theorem compare_refl (rank : Nat) (type : Ty Row) : Compare rank type type := fun _ _ => id

theorem compare_trans (rank : Nat) {first middle last : Ty Row}
    (before : Compare rank first middle) (after : Compare rank middle last) : Compare rank first last :=
  fun env obs accepted => before env obs (after env obs accepted)

theorem bottom_compare (rank : Nat) (type : Ty Row) : Compare rank .bottom type :=
  fun _ obs _ => CommonFinite.probeAt_bottom rank obs

theorem compare_top (rank : Nat) (type : Ty Row) : Compare rank type .top := by
  intro env obs accepted
  have trivial : obs = .trivial := by
    cases rank <;> cases obs <;> simp_all [ProbeAt, CommonFinite.ProbeStep, MaskedProbeStep]
  rw [trivial]
  exact CommonFinite.probeAt_trivial rank type

def meet : List (Ty Row) → Ty Row
  | [] => .top
  | type :: rest => .inter type (meet rest)

theorem meet_below (rank : Nat) (types : List (Ty Row)) (type : Ty Row) (member : type ∈ types) :
    Compare rank (meet types) type := by
  induction types with
  | nil => cases member
  | cons first rest ih =>
    intro env obs accepted
    apply (CommonFinite.probeAt_inter rank first (meet rest) obs).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl accepted
    · exact Or.inr (ih present env obs accepted)

theorem below_meet (rank : Nat) (types : List (Ty Row)) (type : Ty Row)
    (bounded : ∀ target ∈ types, Compare rank type target) : Compare rank type (meet types) := by
  induction types with
  | nil => exact compare_top rank type
  | cons first rest ih =>
    intro env obs accepted
    have both := (CommonFinite.probeAt_inter rank first (meet rest) obs).mp accepted
    exact both.elim (bounded first List.mem_cons_self env obs)
      (ih (fun target member => bounded target (List.mem_cons_of_mem _ member)) env obs)

theorem compare_rank_drop (rank : Nat) (source target : Ty Row) (higher : Compare (rank + 1) source target) : Compare rank source target := by
  classical
  induction rank generalizing source target with
  | zero =>
    intro env obs accepted
    let moved : Environment Row := ⟨fun _ => .bottom, env.roles⟩
    have aligned (type : Ty Row) := step_environment env moved (fun _ _ => True) (Compare 0) rfl type [] obs
      (fun _ domain _ => iff_of_true trivial (bottom_compare 0 domain))
    exact (aligned source).mpr (higher moved obs ((aligned target).mp accepted))
  | succ rank ih =>
    intro env obs accepted
    let tests := domains source ++ domains target
    let selected (name : Nat) := tests.filter (fun type => decide (Compare rank (env.types name) type))
    let moved : Environment Row := ⟨fun name => meet (selected name), env.roles⟩
    have parameterBelow (name : Nat) : Compare rank (env.types name) (moved.types name) :=
      below_meet rank (selected name) (env.types name) (fun domain member => of_decide_eq_true (List.mem_filter.mp member).2)
    have alignedArgument (name : Nat) (domain : Ty Row) (member : domain ∈ tests) :
        Compare rank (env.types name) domain ↔ Compare (rank + 1) (moved.types name) domain := by
      constructor
      · intro bounded
        exact meet_below (rank + 1) (selected name) domain (List.mem_filter.mpr ⟨member, by simpa using bounded⟩)
      · intro bounded
        exact compare_trans rank (parameterBelow name) (ih _ _ bounded)
    have sourceAligned := step_environment env moved (Compare rank) (Compare (rank + 1)) rfl source [] obs
      (fun name domain member => alignedArgument name domain (List.mem_append_left _ member))
    have targetAligned := step_environment env moved (Compare rank) (Compare (rank + 1)) rfl target [] obs
      (fun name domain member => alignedArgument name domain (List.mem_append_right _ member))
    exact sourceAligned.mpr (higher moved obs (targetAligned.mp accepted))

theorem compare_rank_add_drop (rank extra : Nat) (source target : Ty Row) (higher : Compare (rank + extra) source target) : Compare rank source target := by
  induction extra with
  | zero => exact higher
  | succ extra ih => exact ih (compare_rank_drop (rank + extra) source target higher)

end Yulang.CommonEffectRankMonotonicity
