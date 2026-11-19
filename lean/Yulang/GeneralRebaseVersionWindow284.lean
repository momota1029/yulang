import Yulang.GeneralRebaseWindowNoFinite284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 10800000
namespace Yulang.GeneralRebaseVersionWindow284
open GeneralDictionaryVersionLoopSource237 (roles registry root snapshot)
open GeneralDictionaryVersionLoopNames238 (lower)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)
open GeneralVersionBoundaryCompletion259 (complete agrees)
open GeneralRebaseVersionMicro278 (actual raw exact_public complete_all)
open GeneralRebaseVersionEvidence278 (enter_exact installed_shape same_witness_leaves)
open GeneralRebaseVersionRefreshLeaf278 (refreshed_shape)
open GeneralRebaseVersionAbsorb278 (enter_install installed_absorbs refreshed_absorbs)
open GeneralRebaseVersionKnown278 (prefix_known)
open GeneralRebaseInstallTimeline278.Version (patch_exact)
open GeneralRebaseRoundMicro278 (Tick Phase next)
open GeneralRebaseEpochWindow284 (Window view canInstall latestKnown previousKnown)
open GeneralRebaseWindowPaths284 (RawEdge QuotEdge roundFuture compactFuture)
open GeneralRebaseWindowNoFinite284 (Faithful)
open GeneralRebaseWholeRow282 (Keeps Projection initialNames)
open GeneralRebasePrivateStore282 (Joint)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalState (Known)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseTerminalAbsorb278 (InstallTransition)

def Observe (_ : Window) (base : Assignment) (data : Payload) : Prop :=
  GeneralNominalState.Models snapshot base ∧ data = .node 0 []

theorem payload_shape (t : Tick) (m : Assignment) (data : Payload)
    (valid : Models (raw t) m) (seen : Evidence registry (raw t).core m root data) :
    data = .node 0 [] := by
  rcases t with ⟨n,p⟩
  cases p
  · exact ((enter_exact n m data).mp seen).1
  · exact (installed_shape n m valid data).mp seen
  · exact (refreshed_shape n m valid data).mp seen

theorem shared_future (base : Assignment) (initial : GeneralNominalState.Models snapshot base)
    (t : Tick) : Joint (raw t) registry root (.node 0 []) (complete base) := by
  have holds := complete_all t base initial
  refine ⟨holds,?_⟩
  rcases t with ⟨n,p⟩
  cases p
  · exact (same_witness_leaves base initial n).1
  · exact (same_witness_leaves base initial n).2.1
  · exact (refreshed_shape n (complete base) holds _).mpr rfl

theorem exact_joint (t : Tick) (base : Assignment) (data : Payload) :
    Projection (initialNames 3) (Joint (raw t) registry root data) base ↔
      Observe (view t) base data := by
  constructor
  · rintro ⟨a,keeps,holds,evidence⟩
    exact ⟨(exact_public t base).mp ⟨a,(GeneralRebaseLoopView282.Version.agreement_exact _ _).mp keeps,holds⟩,
      payload_shape t a data holds evidence⟩
  · rintro ⟨initial,rfl⟩
    exact ⟨complete base,(GeneralRebaseLoopView282.Version.agreement_exact _ _).mpr (agrees base),
      shared_future base initial t⟩

theorem exact_unbounded_future (t : Tick) (base : Assignment) (data : Payload) :
    (∃ a, Keeps (initialNames 3) a base ∧
      ∀ n, Joint (raw (roundFuture t n)) registry root data a) ↔ Observe (view t) base data := by
  constructor
  · rintro ⟨a,keeps,all⟩
    exact (exact_joint t base data).mp ⟨a,keeps,all 0⟩
  · rintro ⟨initial,rfl⟩
    exact ⟨complete base,(GeneralRebaseLoopView282.Version.agreement_exact _ _).mpr (agrees base),
      fun n => shared_future base initial (roundFuture t n)⟩

theorem fresh (t : Tick) :
    latestKnown (view t) = true ↔ Known (raw t).core.erased.current.context.state (lower (t.round+1)) :=
  (GeneralRebaseEpochWindow284.fresh_observed t).trans (prefix_known t t.round).symm

theorem previous (t : Tick) :
    previousKnown (view t) = true ↔ ∃ i, i+1 = t.round ∧
      Known (raw t).core.erased.current.context.state (lower (i+1)) := by
  rw [GeneralRebaseEpochWindow284.prior_observed]
  exact exists_congr (fun i => and_congr_right (fun _ => (prefix_known t i).symm))

theorem readiness (t : Tick) :
    canInstall (view t) = true ↔ ∃ s : State roles, InstallTransition registry root (raw t) s := by
  rw [GeneralRebaseEpochWindow284.ready_iff]
  rcases t with ⟨n,p⟩
  cases p with
  | enter =>
    exact ⟨fun _ => ⟨_,(enter_install n _).mpr rfl⟩,fun _ => rfl⟩
  | installed =>
    constructor
    · intro bad; cases bad
    · rintro ⟨_,proof⟩; exact False.elim (installed_absorbs n _ proof)
  | refreshed =>
    constructor
    · intro bad; cases bad
    · rintro ⟨_,proof⟩; exact False.elim (refreshed_absorbs n _ proof)

theorem future_sound (t : Tick) (w : Window) (path : B4Target.Steps QuotEdge (view t) w) :
    ∃ nextTick, view nextTick = w ∧
      B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) (raw t) (raw nextTick) := by
  obtain ⟨u,route,same⟩ := GeneralRebaseWindowPaths284.lift_routes path
  exact ⟨u,same,GeneralRebaseWindowPaths284.actual_routes raw actual route⟩

theorem obstruction {Q : Type} (encode : Tick → Q) (pool : List Q)
    (m : Q → Nat → Prop) (k : Q → Nat → Prop) (ready : Q → Prop)
    (models : ∀ t i, m (encode t) i ↔ Models (raw t) (bad i))
    (known : ∀ t i, k (encode t) i ↔ Known (raw t).core.erased.current.context.state (lower (i+1)))
    (install : ∀ t, ready (encode t) ↔ ∃ s : State roles, InstallTransition registry root (raw t) s) :
    ¬ ∀ t, encode t ∈ pool :=
  GeneralRebaseWindowNoFinite284.not_finite
    ⟨m,k,ready,fun t i => (models t i).trans (patch_exact t i),
     fun t i => (known t i).trans (prefix_known t i),fun t => (install t).trans
       ((readiness t).symm.trans (GeneralRebaseEpochWindow284.ready_iff t))⟩ pool

end Yulang.GeneralRebaseVersionWindow284
