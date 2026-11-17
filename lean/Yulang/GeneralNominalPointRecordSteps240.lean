import Yulang.GeneralNominalPointRecord240
namespace Yulang.GeneralNominalPointRecordSteps240
open GeneralNominalVersionedJournal232
open GeneralNominalPointRecord240
open GeneralNominalPointKernel240
variable {roles : Roles.RoleDecls}

abbrev Recorded (state : State roles) (source : Nat) (value : Key) :=
 GeneralNominalPointRecord240.Recorded state.core.erased.current.context.state source value

theorem administrative (action : Administrative (before : State roles) focus after)
 (held : Recorded before source value) : Recorded after source value := by
 cases action with
 | enqueue linked absent => exact held
 | equate first last one two equal novel => exact held
 | refresh context certificate name member unknown known =>
   exact GeneralNominalPointRecord240.refines certificate.refines held
 | reobserve revision certificate improved preserved =>
   exact GeneralNominalPointRecord240.reobserve revision preserved held

theorem at_step (action : At registry (before : State roles) focus after)
 (held : Recorded before source value) : Recorded after source value := by
 cases action with
 | administrative action => exact administrative action held
 | refresh focus context certificate name member unknown known =>
   exact GeneralNominalPointRecord240.refines certificate.refines held
 | install effect enabled novel =>
   have context := enabled.snapshot_eq ▸ effect.frame.context_eq
   have valid : GeneralNominalPointRecord240.Recorded effect.plan.packet.context.state source value := by
     rw [context]
     exact held
   obtain ⟨slot,descriptor,identity,found,point,same⟩ := valid
   exact ⟨slot,descriptor,identity,found,point,same⟩
 | merge first last one two equal novel => exact held

theorem step (action : Step registry root (before : State roles) after)
 (held : Recorded before source value) : Recorded after source value := by
 obtain ⟨focus,_,action⟩ := action
 exact at_step action held

theorem path (trace : B4Target.Steps (Step registry root) (before : State roles) after)
 (held : Recorded before source value) : Recorded after source value := by
 induction trace with
 | refl => exact held
 | tail _ action ih => exact step action ih
theorem functional (one : Recorded (state : State roles) source first)
 (two : Recorded state source last) : first = last := by
 obtain ⟨slot,descriptor,identity,found,point,same⟩ := one
 obtain ⟨other,following,otherIdentity,otherFound,otherPoint,otherSame⟩ := two
 have slotEq := state.core.erased.current.context.state.base.source_injective (identity.trans otherIdentity.symm)
 subst other
 have descriptorEq := Option.some.inj (found.symm.trans otherFound)
 subst following
 exact same.symm.trans otherSame

theorem path_unique (trace : B4Target.Steps (Step registry root) (before : State roles) after)
 (one : Recorded before source first) (two : Recorded after source last) : first = last :=
 functional (path trace one) two
end Yulang.GeneralNominalPointRecordSteps240
