import Yulang.GeneralRebaseEffectSnapshot280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseArchiveTrust280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedSupport233 (Fact Trusted SliceModels Readback ClassReadback Discharged PacketSettled)
open GeneralNominalVersionedMixedObservations233 (Justified CacheSound)
open GeneralRebaseEffectSnapshot280 (EffectRelated ArchiveRelated core_alias)
open CommonRoleOutermostResolver (All₂)

def changeEffects (state : State roles) (new : List (Effect roles)) : State roles :=
  {state with effects := new}

def Correspond (first last : List (Effect roles)) : Prop :=
  (∀ e ∈ first, ∃ other ∈ last, EffectRelated e other) ∧
  (∀ other ∈ last, ∃ e ∈ first, EffectRelated e other)

theorem Correspond.symm (pair : Correspond a b) : Correspond b a := by
  constructor
  · intro e present
    obtain ⟨other,member,related⟩ := pair.2 e present
    exact ⟨other,member,related.symm⟩
  · intro e present
    obtain ⟨other,member,related⟩ := pair.1 e present
    exact ⟨other,member,related.symm⟩

theorem Correspond.cons (pair : Correspond a b) (effect : EffectRelated e f) :
    Correspond (e :: a) (f :: b) := by
  constructor
  · intro x known
    rcases List.mem_cons.mp known with rfl | tail
    · exact ⟨f,List.mem_cons_self,effect⟩
    · obtain ⟨y,recorded,related⟩ := pair.1 x tail
      exact ⟨y,List.mem_cons_of_mem _ recorded,related⟩
  · intro y known
    rcases List.mem_cons.mp known with rfl | tail
    · exact ⟨e,List.mem_cons_self,effect⟩
    · obtain ⟨x,recorded,related⟩ := pair.2 y tail
      exact ⟨x,List.mem_cons_of_mem _ recorded,related⟩

theorem archive (s : State roles) (pair : Correspond s.effects ys) :
    ArchiveRelated s (changeEffects s ys) :=
  ⟨rfl,rfl,pair.1,pair.2⟩

inductive FactMatch : Fact roles → Fact roles → Prop
  | input (p : Plan roles) : FactMatch (.input p) (.input p)
  | output (h : EffectRelated a b) : FactMatch (.output a) (.output b)
  | merge (a b : Site roles) : FactMatch (.merge a b) (.merge a b)

theorem FactMatch.holds (same : FactMatch a b) (m : Assignment) :
    a.Holds m ↔ b.Holds m := by
  cases same with
  | input | merge => exact Iff.rfl
  | output relation => exact and_congr (by rw [relation.plan]) (relation.holds m)

theorem fact_forward (sequence : All₂ (@FactMatch roles) first last) (member : fact ∈ first) :
    ∃ copy ∈ last, FactMatch fact copy := by
  induction sequence with
  | nil => cases member
  | cons related _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_,List.mem_cons_self,related⟩
    · obtain ⟨copy,stored,same⟩ := ih tail
      exact ⟨copy,List.mem_cons_of_mem _ stored,same⟩

theorem fact_back (sequence : All₂ (@FactMatch roles) first last) (member : fact ∈ last) :
    ∃ copy ∈ first, FactMatch copy fact := by
  induction sequence with
  | nil => cases member
  | cons related _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_,List.mem_cons_self,related⟩
    · obtain ⟨copy,stored,same⟩ := ih tail
      exact ⟨copy,List.mem_cons_of_mem _ stored,same⟩

theorem input_forward (sequence : All₂ (@FactMatch roles) first last) (member : Fact.input p ∈ first) :
    Fact.input p ∈ last := by
  obtain ⟨copy,stored,same⟩ := fact_forward sequence member
  cases same
  exact stored

theorem slice_models (s : State roles) (sequence : All₂ (@FactMatch roles) first last) (m : Assignment) :
    SliceModels s first m ↔ SliceModels (changeEffects s ys) last m := by
  constructor
  · rintro ⟨raw,centers,old⟩
    refine ⟨raw,centers,?_⟩
    intro fact stored
    obtain ⟨copy,recorded,same⟩ := fact_back sequence stored
    exact (same.holds m).mp (old copy recorded)
  · rintro ⟨raw,centers,new⟩
    refine ⟨raw,centers,?_⟩
    intro fact stored
    obtain ⟨copy,recorded,same⟩ := fact_forward sequence stored
    exact (same.holds m).mpr (new copy recorded)

theorem discharged {s : State roles} (done : Discharged s focus) :
    Discharged (changeEffects s ys) focus := by
  induction done with
  | packet p member _ ih => exact .packet p member ih
  | alias first last a b edge _ ih => exact .alias first last a b edge ih

theorem settled {s : State roles} (done : PacketSettled s p) :
    PacketSettled (changeEffects s ys) p :=
  ⟨done.1,fun _ h => discharged (done.2 _ h)⟩

theorem readback {s : State roles} (sequence : All₂ (@FactMatch roles) first last)
    (done : Readback s first p) : Readback (changeEffects s ys) last p := by
  intro slot recorded test obs heard model valid
  exact done slot recorded test obs heard model ((slice_models (ys := ys) s sequence model).mpr valid)

theorem same_inputs_mono {first last : Assignment → Prop} {a b : Site roles}
    (imp : ∀ m, last m → first m) (same : SameInputs first a b) : SameInputs last a b := by
  refine ⟨same.1,?_⟩
  have rel := same.2
  generalize a.observed.inputs = xs at rel ⊢
  generalize b.observed.inputs = ys at rel ⊢
  induction rel with
  | nil => exact .nil
  | cons related _ ih =>
    obtain ⟨x,y,hx,hy,meaning⟩ := related
    exact .cons ⟨x,y,hx,hy,fun m h => meaning m (imp m h)⟩ ih

theorem class_readback {s : State roles} {e other : Effect roles}
    (sequence : All₂ (@FactMatch roles) first last) (equiv : EffectRelated e other)
    (done : ClassReadback s first e) : ClassReadback (changeEffects s ys) last other := by
  obtain ⟨edges,rfl,_⟩ := equiv
  intro site present links
  exact same_inputs_mono (fun m h => (slice_models (ys := ys) s sequence m).mpr h)
    (done site present ((core_alias _ _).mp links))

theorem trusted_forward {s : State roles} (pair : Correspond s.effects ys) (done : Trusted s first) :
    ∃ last, All₂ FactMatch first last ∧ Trusted (changeEffects s ys) last := by
  induction done with
  | source => exact ⟨[],.nil,.source⟩
  | input p old present read ih =>
    obtain ⟨last,sequence,known⟩ := ih
    exact ⟨.input p :: last,.cons (.input _) sequence,.input p known present (readback sequence read)⟩
  | output e old present recorded input read complete ih =>
    obtain ⟨last,sequence,known⟩ := ih
    obtain ⟨f,available,equivalent⟩ := pair.1 e present
    have plan := equivalent.plan
    refine ⟨.output f :: last,.cons (.output equivalent) sequence,.output f known available
      (plan ▸ recorded) (plan ▸ input_forward sequence input) (class_readback sequence equivalent read)
      (plan ▸ settled complete)⟩
  | merge first last old a b edge atoms fits same ih =>
    obtain ⟨now,sequence,known⟩ := ih
    have back (m : Assignment) (h : SliceModels (changeEffects s ys) now m) :
        SliceModels s _ m :=
      (slice_models (ys := ys) s sequence m).mpr h
    exact ⟨.merge first last :: now,.cons (.merge _ _) sequence,
      .merge first last known a b edge atoms (fun m h => fits m (back m h))
        (same_inputs_mono back same)⟩

theorem justified_forward {s : State roles} (pair : Correspond s.effects ys) {obs}
    (done : Justified s obs) : Justified (changeEffects s ys) obs := by
  obtain ⟨old,first,lo,hi,sound⟩ := done
  obtain ⟨last,sequence,trusted⟩ := trusted_forward pair hi
  exact ⟨old,last,lo,trusted,fun m l r => sound m l ((slice_models (ys := ys) s sequence m).mpr r)⟩

theorem rearchive_self (s : State roles) : changeEffects s s.effects = s := by cases s <;> rfl

theorem justified_iff {s : State roles} (pair : Correspond s.effects ys) (obs) :
    Justified s obs ↔ Justified (changeEffects s ys) obs := by
  constructor
  · exact justified_forward pair
  · intro yes
    have got := justified_forward (s := changeEffects s ys) pair.symm yes
    change Justified (changeEffects s s.effects) obs at got
    simpa only [rearchive_self] using got

theorem cache_iff {s : State roles} (pair : Correspond s.effects ys) (snap) :
    CacheSound s snap ↔ CacheSound (changeEffects s ys) snap := by
  unfold CacheSound
  simp only [← justified_iff pair]

end Yulang.GeneralRebaseArchiveTrust280
