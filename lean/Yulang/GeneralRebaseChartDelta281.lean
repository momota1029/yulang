import Yulang.GeneralRebasePhaseMachine281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseChartDelta281
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralRebaseChartStep281 (Chart Public Recorded)
open GeneralRebaseSemanticChart281 (Entails Gain Loss)
open GeneralRebasePortCopy280 (Write Copy Unambiguous Isolated Apart copy_model)
open GeneralRebasePortProjection280 (Respects copy_satisfies)

def Satisfies (meaning : F → V → Prop) (delta : List F) (visible : V) : Prop :=
  ∀ f ∈ delta, meaning f visible

structure LocalDelta (chart : Chart F V) (before after : State roles) where
  obligations : List F
  contained : obligations ⊆ chart.facts
  privateDefs : List Write
  protectedNames : List Nat
  wellDefined : Unambiguous privateDefs
  isolated : Isolated privateDefs
  oldSupport : Support before protectedNames
  privateOld : Apart privateDefs protectedNames
  retained : ∀ m v, chart.agrees m v → chart.agrees (Copy privateDefs m) v
  atom : F → Assignment → Prop
  invariant : ∀ m v, chart.agrees m v → ∀ f ∈ obligations, (atom f m ↔ chart.meaning f v)
  exact : ∀ m, Models after m ↔ Models before m ∧ Respects privateDefs m ∧ Satisfies atom obligations m

theorem delta_exact {chart : Chart F V} {before after : State roles}
    (kernel : LocalDelta chart before after) (visible : V) :
    Public chart after visible ↔ Public chart before visible ∧ Satisfies chart.meaning kernel.obligations visible := by
  constructor
  · rintro ⟨internal,agrees,held⟩
    obtain ⟨prior,_,publicAtoms⟩ := (kernel.exact internal).mp held
    exact ⟨⟨internal,agrees,prior⟩,fun f listed =>
      (kernel.invariant internal visible agrees f listed).mp (publicAtoms f listed)⟩
  · rintro ⟨⟨internal,agrees,held⟩,publicAtoms⟩
    let copied := Copy kernel.privateDefs internal
    have kept := kernel.retained internal visible agrees
    refine ⟨copied,kept,(kernel.exact copied).mpr ⟨
      copy_model kernel.oldSupport kernel.privateOld held,
      copy_satisfies kernel.wellDefined kernel.isolated internal,?_⟩⟩
    intro f listed
    exact (kernel.invariant copied visible kept f listed).mpr (publicAtoms f listed)

theorem after_entails {chart : Chart F V} {before after : State roles}
    (kernel : LocalDelta chart before after) (seen : f ∈ kernel.obligations) :
    Recorded chart after f :=
  fun v full => ((delta_exact kernel v).mp full).2 f seen

theorem strict_delta {chart : Chart F V} {before after : State roles}
    (kernel : LocalDelta chart before after) :
    Loss (Public chart) before after ↔ ∃ f ∈ kernel.obligations, ¬ Recorded chart before f := by
  classical
  constructor
  · rintro ⟨v,had,lost⟩
    apply Classical.byContradiction
    intro absent
    apply lost ((delta_exact kernel v).mpr ⟨had,?_⟩)
    intro f listed
    apply Classical.byContradiction
    intro nope
    exact absent ⟨f,listed,fun entailed => nope (entailed v had)⟩
  · rintro ⟨f,listed,no⟩
    exact GeneralRebaseSemanticChart281.gain_cuts
      ⟨f,kernel.contained listed,no,after_entails kernel listed⟩

theorem gain_exact {chart : Chart F V} {before after : State roles}
    (kernel : LocalDelta chart before after) :
    Gain chart.facts chart.meaning (Public chart) before after ↔
      ∃ f ∈ kernel.obligations, ¬ Recorded chart before f := by
  constructor
  · exact fun h => (strict_delta kernel).mp (GeneralRebaseSemanticChart281.gain_cuts h)
  · rintro ⟨f,seen,notBefore⟩
    exact ⟨f,kernel.contained seen,notBefore,after_entails kernel seen⟩

theorem repeated_is_public_silent {chart : Chart F V} {before after : State roles}
    (kernel : LocalDelta chart before after)
    (already : ∀ f ∈ kernel.obligations, Recorded chart before f) (visible : V) :
    Public chart after visible ↔ Public chart before visible := by
  rw [delta_exact kernel]
  exact ⟨And.left,fun h => ⟨h,fun f listed => already f listed visible h⟩⟩

theorem append_exact {chart : Chart F V} {before after : State roles} {base : V → Prop}
    {prior : List F} (kernel : LocalDelta chart before after)
    (initial : ∀ v, Public chart before v ↔ base v ∧ Satisfies chart.meaning prior v)
    (v : V) : Public chart after v ↔ base v ∧ Satisfies chart.meaning (prior ++ kernel.obligations) v := by
  rw [delta_exact kernel,initial]
  constructor
  · rintro ⟨⟨h,left⟩,right⟩
    exact ⟨h,fun f member => (List.mem_append.mp member).elim (left f) (right f)⟩
  · rintro ⟨h,all⟩
    exact ⟨⟨h,fun f m => all f (List.mem_append_left _ m)⟩,fun f m => all f (List.mem_append_right _ m)⟩

end Yulang.GeneralRebaseChartDelta281
