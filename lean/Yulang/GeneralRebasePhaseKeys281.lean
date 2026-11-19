import Yulang.GeneralRebaseChartPointService281
import Yulang.GeneralNominalSourceOwnerCandidates252

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebasePhaseKeys281
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalSourceOwnerCandidates252 (mixed_finite_owners)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split administrative_plans)

abbrev Key (Q : Type) := (Nat × Nat) × Q

structure Codec (roles : Roles.RoleDecls) (Q : Type) where
  labels : List Q
  classify : Plan roles → Option Q
  finite : ∀ p q, classify p = some q → q ∈ labels

def owner (p : Plan roles) : Nat × Nat :=
  (p.packet.site.occurrence.identity,p.packet.declaration.id)

def Seen (codec : Codec roles Q) (s : State roles) (key : Key Q) : Prop :=
  ∃ p ∈ s.plans, owner p = key.1 ∧ codec.classify p = some key.2

def Added (codec : Codec roles Q) (before after : State roles) : Prop :=
  ∃ key, ¬ Seen codec before key ∧ Seen codec after key

def pool (owners : List (Nat × Nat)) (labels : List Q) : List (Key Q) :=
  owners.flatMap fun o => labels.map (fun q => (o,q))

theorem pool_exact (owners : List (Nat × Nat)) (labels : List Q) (key : Key Q) :
    key ∈ pool owners labels ↔ key.1 ∈ owners ∧ key.2 ∈ labels := by
  constructor
  · intro member
    obtain ⟨o,inO,more⟩ := List.mem_flatMap.mp member
    obtain ⟨tag,inQ,rfl⟩ := List.mem_map.mp more
    exact ⟨inO,inQ⟩
  · rintro ⟨inO,inQ⟩
    exact List.mem_flatMap.mpr ⟨key.1,inO,List.mem_map.mpr ⟨key.2,inQ,by cases key; rfl⟩⟩

theorem source_plans {r : Registry} {root : Occurrence roles} {start finish : State roles}
    (init : (boundary roles).Initial r root start)
    {owners : List (Nat × Nat)}
    (covers : ∀ s, B4Target.Steps (Actual r root) start s → ∀ effect,
      GeneralNominalSaturationState.Generated s.core.erased.current root effect.plan.packet.site.occurrence →
      GeneralNominalVersionedMixedKernel234.Installable
        (GeneralNominalCenteredHeadAllocEncoding.registry r) s effect →
      ¬ GeneralNominalVersionedMixedKernel234.Committed s effect.plan → owner effect.plan ∈ owners)
    (walk : B4Target.Steps (Actual r root) start finish) :
    ∀ p ∈ finish.plans, owner p ∈ owners := by
  induction walk with
  | refl =>
    intro p recorded
    obtain ⟨legacy,_,rfl⟩ := init
    cases recorded
  | @tail old _ path step ih =>
    obtain ⟨focus,generated,chosen⟩ := step
    cases chosen with
    | administrative a => cases a <;> exact ih
    | refresh | merge => exact ih
    | install eff ready novel =>
      intro p member
      rcases List.mem_cons.mp member with rfl|seen
      · exact covers old path eff generated ready novel
      · exact ih p seen

theorem finite_seen {r : Registry} {root : Occurrence roles} {start : State roles}
    (init : (boundary roles).Initial r root start) (codec : Codec roles Q) :
    ∃ bound : List (Key Q), ∀ s, B4Target.Steps (Actual r root) start s →
      ∀ k, Seen codec s k → k ∈ bound := by
  obtain ⟨owners,covers⟩ := mixed_finite_owners r root start init
  refine ⟨pool owners codec.labels,?_⟩
  intro s path k known
  obtain ⟨plan,member,eq,tag⟩ := known
  exact (pool_exact ..).mpr ⟨eq ▸ source_plans init covers path plan member,codec.finite _ _ tag⟩

theorem monotone {r : Registry} {root : Occurrence roles} {before after : State roles}
    (codec : Codec roles Q) (step : Actual r root before after) :
    ∀ key, Seen codec before key → Seen codec after key := by
  rintro key ⟨p,recorded,one,two⟩
  refine ⟨p,?_,one,two⟩
  obtain ⟨_,_,step⟩ := step
  cases step with
  | administrative a => cases a <;> exact recorded
  | refresh | merge => exact recorded
  | install => exact List.mem_cons_of_mem _ recorded

theorem fresh_iff {before : State roles} {effect : GeneralNominalVersionedJournal232.Effect roles}
    (codec : Codec roles Q) :
    Added codec before (GeneralNominalVersionedInstall232.install before effect) ↔
      ∃ tag, codec.classify effect.plan = some tag ∧ ¬ Seen codec before (owner effect.plan,tag) := by
  constructor
  · rintro ⟨⟨ownerK,tag⟩,old,p,new,ownerEq,classified⟩
    rcases List.mem_cons.mp new with rfl|older
    · change owner effect.plan = ownerK at ownerEq
      subst ownerK
      exact ⟨tag,classified,old⟩
    · exact False.elim (old ⟨p,older,ownerEq,classified⟩)
  · rintro ⟨tag,yes,no⟩
    exact ⟨_,no,effect.plan,List.mem_cons_self,rfl,yes⟩

end Yulang.GeneralRebasePhaseKeys281
