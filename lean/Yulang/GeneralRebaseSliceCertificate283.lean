import Yulang.GeneralRebaseSliceJournal283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSliceCertificate283
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231 (Frame Certificate)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralNominalRebaseEffectView243 (body output_exact)
open GeneralNominalRebaseClassView243 (equations)
open GeneralNominalEffectSupport249 (equationReads equation_iff)
open Core.PresenceGeneration (CompTerm)

def readPlan (p : Plan roles) : List Nat :=
  GeneralNominalPacketSupport249.support (GeneralNominalRebasePacketView243.compile p CompTerm.var) ++
  (equations p CompTerm.var p.packet.site.occurrence.demand.outputs).flatMap equationReads

theorem covered (p : Plan roles) (out : GeneralSourceState.Output)
    (present : out ∈ p.packet.site.occurrence.demand.outputs)
    {source : GeneralDictionaryAssociatedProvenance.Body}
    (supplied : GeneralDictionaryAssociatedProvenance.Supplies roles p.packet.declaration out.name source)
    {eqn : GeneralNominalRebaseEffectView243.Equation} (seen : body p CompTerm.var out.target source = some eqn)
    {n : Nat} (read : n ∈ equationReads eqn) : n ∈ readPlan p := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨eqn,?_,read⟩)
  have found := (lookup_exact roles p.packet.declaration p.packet.checked.identified.2.2.1 out.name source).mpr supplied
  unfold equations
  apply List.mem_flatMap.mpr
  refine ⟨out,present,List.mem_flatMap.mpr ⟨source,?_,?_⟩⟩
  · simp [found]
  · simp [seen]

theorem output_stable (p : Plan roles) {a b : Assignment} (rows : ∀ n, (a n).2 = (b n).2)
    (types : ∀ n ∈ readPlan p, (a n).1 = (b n).1) (o : GeneralSourceState.Output)
    (member : o ∈ p.packet.site.occurrence.demand.outputs) :
    GeneralDictionaryDefaultEvidence204.OutputWitness p a o ↔ GeneralDictionaryDefaultEvidence204.OutputWitness p b o := by
  refine (output_exact p CompTerm.var a o).symm.trans (Iff.trans ?_ (output_exact p CompTerm.var b o))
  unfold GeneralNominalRebaseEffectView243.OutputWitness
  apply exists_congr; intro src
  apply and_congr_right; intro supplied
  apply exists_congr; intro eqn
  apply and_congr_right; intro found
  exact equation_iff eqn a b rows (fun n read => types n (covered p o member supplied found read))

theorem certificate (r : Registry) (s : GeneralNominalCenteredSteps.State roles) (p : Plan roles)
    {a b : Assignment} (rows : ∀ n, (a n).2 = (b n).2)
    (types : ∀ n ∈ readPlan p, (a n).1 = (b n).1)
    (focus : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    Certificate r s a focus key children p ↔ Certificate r s b focus key children p := by
  let packet := GeneralNominalRebasePacketView243.compile p CompTerm.var
  have same : GeneralNominalVersionedPlans231.Holds p a ↔ GeneralNominalVersionedPlans231.Holds p b :=
    (GeneralNominalRebasePacketView243.compile_exact p CompTerm.var a).symm.trans
      ((GeneralNominalPacketSupport249.packet_iff packet a b rows
        (fun n found => types n (List.mem_append_left _ found))).trans
        (GeneralNominalRebasePacketView243.compile_exact p CompTerm.var b))
  constructor
  · intro h
    exact ⟨h.frame,h.children_eq,same.mp h.packet,fun o member =>
      (output_stable p rows types o (h.frame.occurrence_eq.symm ▸ member)).mp (h.outputs o member)⟩
  · intro h
    exact ⟨h.frame,h.children_eq,same.mpr h.packet,fun o member =>
      (output_stable p rows types o (h.frame.occurrence_eq.symm ▸ member)).mpr (h.outputs o member)⟩

end Yulang.GeneralRebaseSliceCertificate283
