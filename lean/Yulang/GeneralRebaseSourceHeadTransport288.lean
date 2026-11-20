import Yulang.GeneralRebaseRowLeafLocality288

/-! Transport an independently established nominal denotation by typed
source embeddings, without assuming that the model satisfies the entire
new snapshot. Both type and row coordinate maps are used. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSourceHeadTransport288
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (State FitsAll Parameter Descriptor Denotes)
open GeneralNominalRefinements (Refines renameParameter renameDescriptor)

theorem args_forward {old new : State} (refines : Refines old new) (m : Assignment)
    (parameters : List (Parameter old.base.slots)) (values : List CommonNominalFullCarrier.Argument)
    (fits : FitsAll old.base m parameters values) :
    FitsAll new.base m (parameters.map (renameParameter refines.base.embed)) values := by
  induction fits with
  | nil => exact .nil
  | cons first tail ih =>
    exact .cons ((GeneralNominalRefinements.fits_transport refines m _ _).mpr first) ih

theorem denotes_iff {old new : State} (refines : Refines old new) (m : Assignment)
    (slot : Fin old.base.slots) (d : Descriptor old.base.slots) :
    Denotes new.base m (refines.base.embed slot) (renameDescriptor refines.base.embed d) ↔
      Denotes old.base m slot d := by
  constructor
  · rintro ⟨values,fits,value⟩
    refine ⟨values,GeneralNominalRefinements.fitsAll_transport refines m d.arguments values fits,?_⟩
    simpa only [renameDescriptor,refines.base.source] using value
  · rintro ⟨values,fits,value⟩
    refine ⟨values,args_forward refines m d.arguments values fits,?_⟩
    simpa only [renameDescriptor,refines.base.source] using value

end Yulang.GeneralRebaseSourceHeadTransport288
