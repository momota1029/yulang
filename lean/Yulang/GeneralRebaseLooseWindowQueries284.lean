import Yulang.GeneralRebasePortComparisons284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLooseWindowQueries284
open GeneralDictionaryLooseLoopSource240 (roles registry root snapshot)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryInitialFill258 (complete public_agrees)
open GeneralRebaseLooseMicro278 (raw exact_public complete_all)
open GeneralRebaseLoosePortRead284 (correct)
open GeneralRebaseEpochWindow284 (view)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseWindowPorts284 (Port rawAddr root_bound)
open GeneralRebaseWindowQueries284 (resolve Invariant)
open GeneralRebasePortComparisons284 (pair invariant_eq invariant_le)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype)

theorem restriction (t : Tick) (m : Assignment) (valid : Models (raw t) m) :
    GeneralNominalState.Models snapshot m :=
  (exact_public t m).mp ⟨m,⟨fun _ _ => rfl,fun _ => rfl⟩,valid⟩

theorem visible_names (t : Tick) (ports : List Port) (names : List Nat)
    (resolved : resolve 4 (view t) ports = some names) (k : Nat) (member : k ∈ names) : k ≤ 4 := by
  obtain ⟨p,_,read⟩ := GeneralRebaseWindowQueries284.names_used resolved k member
  have small := root_bound 4 (view t) p k read
  simp only [List.mem_cons,List.not_mem_nil,or_false] at small
  rcases small with rfl|rfl <;> decide

theorem completes (t : Tick) (ports : List Port) (names : List Nat)
    (resolved : resolve 4 (view t) ports = some names) (m : Assignment)
    (valid : GeneralNominalState.Models snapshot m) :
    ∃ new, Models (raw t) new ∧ ∀ k ∈ names, new k = m k :=
  ⟨complete m,complete_all t m valid,fun k within => (public_agrees m).1 k (visible_names t ports names resolved k within)⟩

theorem query_some (t : Tick) (ports : List Port) (names : List Nat)
    (resolved : resolve 4 (view t) ports = some names) (goal : List Ty → Prop) (safe : Invariant goal) :
    (∃ a, Models (raw t) a ∧ goal (ports.map (fun p => (a (rawAddr lower upper t p)).1))) ↔
      ∃ base, GeneralNominalState.Models snapshot base ∧ goal (names.map (fun k => (base k).1)) :=
  GeneralRebaseWindowQueries284.query_exists resolved (restriction t) (completes t ports names resolved)
    (fun a valid p k probe => correct t p a valid k probe) goal safe

theorem query_every (t : Tick) (ports : List Port) (names : List Nat)
    (resolved : resolve 4 (view t) ports = some names) (goal : List Ty → Prop) (safe : Invariant goal) :
    (∀ a, Models (raw t) a → goal (ports.map (fun p => (a (rawAddr lower upper t p)).1))) ↔
      ∀ base, GeneralNominalState.Models snapshot base → goal (names.map (fun k => (base k).1)) :=
  GeneralRebaseWindowQueries284.query_all resolved (restriction t) (completes t ports names resolved)
    (fun a valid p k probe => correct t p a valid k probe) goal safe

theorem equal (t : Tick) (first last : Port) (a b : Nat)
    (resolved : resolve 4 (view t) [first,last] = some [a,b]) :
    GeneralNominalVersionedMixedKernel234.Equal (raw t)
      (rawAddr lower upper t first) (rawAddr lower upper t last) ↔
      ∀ m, GeneralNominalState.Models snapshot m → Equivalent (m a).1 (m b).1 :=
  query_every t [first,last] [a,b] resolved (pair Equivalent) invariant_eq

theorem generated (t : Tick) (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalSaturationState.Generated (raw t).core.erased.current root focus ↔ focus = root :=
  ⟨GeneralRebaseTerminalAbsorb278.generated_root (GeneralRebaseLooseAbsorb278.terminal t),
    fun same => same ▸ .root⟩

end Yulang.GeneralRebaseLooseWindowQueries284
