import Yulang.GeneralNominalInspectionOrigins

/-! Finite forests preserve the input Pattern witnesses. The actual guard
supplies endpoint equality when a constructor root needs origin recovery. -/
namespace Yulang.GeneralNominalGroundForests
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalGroundAccessibility GeneralNominalGroundProduction
open GeneralNominalSaturationState GeneralNominalFeedbackSites
open GeneralNominalInspectionOrigins
open GeneralDeclarationPatterns
open CommonNominalFullCarrier

variable {model : GeneralNominalCommonBridge.Assignment}

structure Entry where
  origin : Origin
  pattern : Pattern
  term : Expr Nat

def Forest (context : GeneralNominalCandidates.Context) (model : GeneralNominalCommonBridge.Assignment)
    (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, ClosedTerm context entry.pattern entry.term ∧
    At model .actual entry.origin (denote (fun _ => .bottom) entry.term)

theorem retained_forest {roles : Roles.RoleDecls}
    {site : GeneralNominalDemandMerging.Site roles}
    (known : Inputs context model site labels) :
    ∃ entries : List Entry, Forest context model entries ∧
      ∀ index : Fin (roles site.occurrence.demand.role).arity, ∀ origin,
        site.inputs[index.val]? = some (some origin) → ∃ entry ∈ entries,
          entry.origin = origin ∧ labels[index.val]? = some entry.pattern := by
  classical
  obtain ⟨length,meanings⟩ := known
  let term := fun index => Classical.choose (meanings index)
  let atIndex := fun index : Fin (roles site.occurrence.demand.role).arity =>
    ((site.inputs[index.val]?).join.toList).map fun origin =>
      (⟨origin,labels[index.val]'(by rw [length]; exact index.isLt),term index⟩ : Entry)
  let entries := (List.finRange (roles site.occurrence.demand.role).arity).flatMap atIndex
  refine ⟨entries,?_,?_⟩
  · intro entry present
    obtain ⟨index,_,present⟩ := List.mem_flatMap.mp present
    change entry ∈ ((site.inputs[index.val]?).join.toList).map _ at present
    obtain ⟨origin,originMem,entryEq⟩ := List.mem_map.mp present
    subst entry
    have recorded : site.inputs[index.val]? = some (some origin) := by
      cases found : site.inputs[index.val]? with
      | none => simp [found] at originMem
      | some value => cases value with
        | none => simp [found] at originMem
        | some other =>
          have same : origin = other := by simpa only [found,Option.join,Option.bind_some,id_eq,Option.toList,List.mem_singleton] using originMem
          cases same; rfl
    have meaning := Classical.choose_spec (meanings index)
    exact ⟨meaning.1,meaning.2.2 origin recorded⟩
  · intro index origin recorded
    refine ⟨⟨origin,labels[index.val]'(by rw [length]; exact index.isLt),term index⟩,?_,rfl,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨origin,?_,rfl⟩⟩
      simp [recorded]
    · exact List.getElem?_eq_getElem (by rw [length]; exact index.isLt)

theorem recovered_forest {roles : Roles.RoleDecls}
    {site : GeneralNominalDemandMerging.Site roles}
    (state : State roles) (valid : Models state model) (known : Inputs context model site labels) :
    ∃ entries : List Entry, Forest context model entries ∧
      ∀ index : Fin (roles site.occurrence.demand.role).arity, ∀ origin,
        (recover state site).inputs[index.val]? = some (some origin) → ∃ entry ∈ entries,
          entry.origin = origin ∧ labels[index.val]? = some entry.pattern :=
  retained_forest (recovered_inputs state model valid known)

theorem recovery_of_missing {roles : Roles.RoleDecls}
    (state : State roles) (site : GeneralNominalDemandMerging.Site roles)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (missing : site.inputs[index.val]? = some none)
    (present : ((recover state site).inputs[index.val]?).join = some origin) :
    EndpointEqual state (site.occurrence.demand.arguments index) ∧
      origin = .source (site.occurrence.demand.arguments index).1 := by
  classical
  have bound : index.val < site.inputs.length := by rw [site.arity]; exact index.isLt
  have old : site.inputs[index.val]'bound = none := by
    rw [List.getElem?_eq_getElem bound] at missing
    exact Option.some.inj missing
  have entry : recoverOrigin state site index = some origin := by
    simpa only [recover,List.getElem?_ofFn,index.isLt,dite_eq_left,Option.join,Option.bind_some,id_eq,Fin.eta] using present
  by_cases equal : EndpointEqual state (site.occurrence.demand.arguments index)
  · refine ⟨equal,?_⟩
    have identity : .source (site.occurrence.demand.arguments index).1 = origin :=
      Option.some.inj (by simpa only [recoverOrigin,old,ite_eq_left equal] using entry)
    exact identity.symm
  · simp only [recoverOrigin,old,ite_eq_right equal] at entry
    cases entry

theorem safe_missing_root {roles : Roles.RoleDecls}
    (state : State roles) (packet : Packet roles)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (queryAt : (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)[index.val]? = some query)
    (constructor : Constructor query)
    (missing : packet.site.inputs[index.val]? = some none) :
    EndpointEqual state (packet.site.occurrence.demand.arguments index) := by
  have length : packet.bounds.length = (roles packet.site.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length packet.context.state.base
      (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located
  have bound : index.val < packet.bounds.length := by rw [length]; exact index.isLt
  obtain ⟨origin,present⟩ := complete_root packet.context.state _ packet.bounds
    (fun index => ((recover state packet.site).inputs[index]?).join) index.val queryAt
    (List.getElem?_eq_getElem bound) constructor safe.1.symm
  exact (recovery_of_missing state packet.site index missing present).1

theorem missing_constructor_meanings {roles : Roles.RoleDecls}
    (state : State roles) (packet : Packet roles)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (queryAt : (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)[index.val]? = some query)
    (constructor : Constructor query)
    (missing : packet.site.inputs[index.val]? = some none)
    (valid : Models state model) (known : Inputs context model packet.site labels) :
    ∃ pattern term, labels[index.val]? = some pattern ∧ ClosedTerm context pattern term ∧
      At model .actual (.source (packet.site.occurrence.demand.arguments index).1) (denote (fun _ => .bottom) term) ∧
      At model .actual (.source (packet.site.occurrence.demand.arguments index).2) (denote (fun _ => .bottom) term) := by
  obtain ⟨length,meanings⟩ := known
  obtain ⟨term,closed,fits,_⟩ := meanings index
  have equal := safe_missing_root state packet safe located index queryAt constructor missing model valid
  have lower := GeneralNominalStructuralContainment.equal_endpoints_exact model fits equal
  refine ⟨_,term,List.getElem?_eq_getElem (by rw [length]; exact index.isLt),closed,?_,?_⟩
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen; exact lower
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    exact ⟨subtype_trans equal.2 lower.1,subtype_trans lower.2 equal.1⟩

end Yulang.GeneralNominalGroundForests
