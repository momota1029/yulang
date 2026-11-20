import Yulang.GeneralRebaseDepthRefresh285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseTowerEndpoint285
open GeneralNominalOutputGrowth (tower tower_equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_scalar tagged_nominal)
open CommonNominalFullCarrier (Subtype subtype_refl subtype_trans Equivalent nominal)
open GeneralNominalState (State Descriptor Denotes)

theorem subtype_eq (a b : Nat) : Subtype (tower a) (tower b) ↔ a = b := by
 constructor
 · intro below
   cases a with
   | zero =>
     cases b with
     | zero => rfl
     | succ b => exact nomatch (tag_subtype (tagged_scalar .int) (tagged_nominal 0 [.inl (tower b)]) below)
   | succ a =>
     cases b with
     | zero => exact nomatch (tag_subtype (tagged_nominal 0 [.inl (tower a)]) (tagged_scalar .int) below)
     | succ b =>
       have inv := ((CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mp below).2.2 0
         (.inl (tower a)) (.inl (tower b)) rfl rfl
       exact congrArg Nat.succ ((tower_equivalent a b).mp inv)
 · rintro rfl
   exact subtype_refl _

/-- A same-carrier unary nominal value of positive depth can be represented by
a descriptor only if an endpoint of the right subtype exists. The descriptor
is not assumed point-valued. No source membership follows from denotation alone. -/
theorem requires_lower (s : State) (m : Assignment) (slot : Fin s.base.slots)
    (d : Descriptor s.base.slots) (depth : Nat)
    (atSlot : (m (s.base.source slot)).1 = tower (depth+1))
    (valid : Denotes s.base m slot d) :
    ∃ low : Fin s.base.slots, Subtype (m (s.base.source low)).1 (tower depth) := by
 obtain ⟨args,fits,observed⟩ := valid
 rw [atSlot] at observed
 have invariant := (CommonNominalFullCarrier.nominal_regular_invariant_exact 0 d.declaration.name
   [.inl (tower depth)] args).mp observed.1
 have len : args.length = 1 := invariant.2.1.symm
 have dlen : d.arguments.length = 1 :=
   (GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fits).symm.trans len
 cases descriptors : d.arguments with
 | nil => rw [descriptors] at dlen; cases dlen
 | cons parameter rest =>
   have first : d.arguments[0]? = some parameter := descriptors ▸ rfl
   obtain ⟨v,loc,well⟩ := GeneralNominalIntervalLaws.fitsAll_at _ _ _ _ fits 0 parameter first
   have equal := invariant.2.2 0 (.inl (tower depth)) v rfl loc
   cases v with
   | inr _ => exact equal.elim
   | inl value =>
     cases parameter with
     | row _ => exact well.elim
     | type bounds => exact ⟨bounds.1,subtype_trans well.1 equal.2⟩

theorem requires_present_rank (s : State) (m : Assignment) (rank : Fin s.base.slots → Nat)
    (described : ∀ i, (m (s.base.source i)).1 = tower (rank i))
    (slot : Fin s.base.slots) (d : Descriptor s.base.slots) (k : Nat)
    (deep : rank slot = k+1) (valid : Denotes s.base m slot d) :
    ∃ low : Fin s.base.slots, rank low = k := by
 obtain ⟨low,below⟩ := requires_lower s m slot d k ((described slot).trans (congrArg tower deep)) valid
 rw [described low] at below
 exact ⟨low,(subtype_eq (rank low) k).mp below⟩

/-- This equivalence concerns one fixed assignment and the existence of a
catalogue-compatible descriptor, not a uniform cache certificate. -/
theorem descriptor_iff (s : State) (m : Assignment) (rank : Fin s.base.slots → Nat)
    (described : ∀ i, (m (s.base.source i)).1 = tower (rank i))
    (slot : Fin s.base.slots) (k key : Nat)
    (deep : rank slot = k+1)
    (entry : s.constructors key = some ⟨[.type],0⟩) :
    (∃ d : Descriptor s.base.slots, s.constructors d.constructor = some d.declaration ∧
      Denotes s.base m slot d) ↔ ∃ low : Fin s.base.slots, rank low = k := by
  constructor
  · rintro ⟨d,_,valid⟩
    exact requires_present_rank s m rank described slot d k deep valid
  · rintro ⟨low,rightRank⟩
    let d : Descriptor s.base.slots := ⟨key,⟨[.type],0⟩,[.type (low,low)],rfl⟩
    refine ⟨d,entry,(GeneralNominalState.denotes_singleton_exact s.base m slot low d rfl).mpr ?_⟩
    rw [described slot,described low,deep,rightRank]
    exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralRebaseTowerEndpoint285
