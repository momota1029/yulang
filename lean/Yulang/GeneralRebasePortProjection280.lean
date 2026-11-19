import Yulang.GeneralRebasePortDecode280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePortProjection280
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralRebasePortCopy280 (Write Copy Apart Isolated Unambiguous lookup copy_agrees copy_equation
  copy_value source_unchanged)
open CommonNominalFullCarrier (Equivalent subtype_refl subtype_trans)

def Respects (writes : List Write) (m : Assignment) : Prop :=
  ∀ pair ∈ writes, Equivalent (m pair.1).1 (m pair.2).1

def Project (pool : List Nat) (models : Assignment → Prop) (outer : Assignment) : Prop :=
  ∃ m, Agree pool m outer ∧ models m

def Supported (pool : List Nat) (models : Assignment → Prop) : Prop :=
  ∀ a b, Agree pool a b → (models a ↔ models b)

def Extension (old : Assignment → Prop) (writes : List Write) (m : Assignment) : Prop :=
  old m ∧ Respects writes m

theorem copy_satisfies (unique : Unambiguous writes) (isolated : Isolated writes) (m : Assignment) :
    Respects writes (Copy writes m) := by
  rintro ⟨target,source⟩ recorded
  rw [copy_equation (m := m) unique isolated recorded]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem copy_extends (frames : Supported fixed old) (fresh : Apart writes fixed)
    (unique : Unambiguous writes) (isolated : Isolated writes) (m : Assignment) (valid : old m) :
    Extension old writes (Copy writes m) :=
  ⟨(frames m _ (copy_agrees fresh m)).mp valid,copy_satisfies unique isolated m⟩

theorem copy_readable (frames : Supported fixed old) (fresh : Apart writes fixed)
    (unique : Unambiguous writes) (isolated : Isolated writes) (m : Assignment) :
    Extension old writes (Copy writes m) ↔ old m :=
  ⟨fun made => (frames m _ (copy_agrees fresh m)).mpr made.1,copy_extends frames fresh unique isolated m⟩

theorem project_extension (frames : Supported fixed old) (fresh : Apart writes fixed)
    (observed : Apart writes reads) (unique : Unambiguous writes) (isolated : Isolated writes)
    (target : Assignment) :
    Project reads (Extension old writes) target ↔ Project reads old target := by
  constructor
  · rintro ⟨m,agrees,held,_⟩
    exact ⟨m,agrees,held⟩
  · rintro ⟨m,agrees,held⟩
    exact ⟨Copy writes m,fun id seen => ((copy_agrees observed m id seen).symm).trans (agrees id seen),
      copy_extends frames fresh unique isolated m held⟩

structure Conditions (writes : List Write) (support observed : List Nat) : Prop where
  unique : Unambiguous writes
  isolated : Isolated writes
  fresh : Apart writes support
  privateWrites : Apart writes observed

theorem projected_replace (frames : Supported fixed old)
    (beforeOK : Conditions before fixed observed) (afterOK : Conditions after fixed observed)
    (target : Assignment) :
    Project observed (Extension old before) target ↔ Project observed (Extension old after) target :=
  (project_extension frames beforeOK.fresh beforeOK.privateWrites beforeOK.unique beforeOK.isolated target).trans
    (project_extension frames afterOK.fresh afterOK.privateWrites afterOK.unique afterOK.isolated target).symm

theorem res_append : Respects (first ++ last) m ↔ Respects first m ∧ Respects last m := by
  constructor
  · intro holds
    exact ⟨fun row h => holds row (List.mem_append_left _ h),fun row h => holds row (List.mem_append_right _ h)⟩
  · rintro ⟨left,right⟩ row h
    exact (List.mem_append.mp h).elim (left row) (right row)

theorem linked_sources {a before after : Nat} {first last : List Write} {m : Assignment}
    (had : (a,before) ∈ first) (has : (a,after) ∈ last)
    (old : Respects first m) (new : Respects last m) :
    Equivalent (m before).1 (m after).1 := by
  have one := old (a,before) had
  have two := new (a,after) has
  exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩

theorem append_conflicts {slot before after : Nat} {first last : List Write} {m : Assignment}
    {old : Assignment → Prop} (had : (slot,before) ∈ first) (has : (slot,after) ∈ last)
    (h : ¬ Equivalent (m before).1 (m after).1) :
    ¬ Extension old (first ++ last) m :=
  fun good => h (linked_sources had has (res_append.mp good.2).1 (res_append.mp good.2).2)

theorem append_loses_public {slot before after : Nat} {first last : List Write} {m : Assignment}
    {old : Assignment → Prop} (was : old m) (had : (slot,before) ∈ first) (has : (slot,after) ∈ last)
    (oldRead : before ∈ observed) (newRead : after ∈ observed)
    (h : ¬ Equivalent (m before).1 (m after).1) :
    Project observed old m ∧ ¬ Project observed (Extension old (first ++ last)) m := by
  refine ⟨⟨m,fun _ _ => rfl,was⟩,?_⟩
  rintro ⟨alt,agree,valid⟩
  have why := linked_sources (m := alt) had has (res_append.mp valid.2).1 (res_append.mp valid.2).2
  rw [agree before oldRead,agree after newRead] at why
  exact h why

end Yulang.GeneralRebasePortProjection280
