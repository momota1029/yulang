import Yulang.GeneralNominalSourceReadback

/-! Origin-preserving emissions and recovery of journal-proved point intervals.
The origin search ranges over the actual finite clauses and capture report.
It does not choose a value inside an interval. Compound inputs without a
retained origin continue to use the conservative point-site fallback. -/
namespace Yulang.GeneralNominalFeedbackSites

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

abbrev frame (packet : Packet roles) : GeneralDictionaryEmissionPlans.Frame roles :=
  GeneralNominalAllocation.frame packet.context.state packet.registry packet.site.occurrence.identity packet.bindings

def clauseChild (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) : Occurrence roles :=
  GeneralDictionaryEmissionPlans.occurrence (frame packet)
    (GeneralDeclarationDemands.emit packet.site.occurrence.identity packet.declaration clause valid
      ((frame packet).capture packet.declaration.id) ((frame packet).allocation packet.declaration.id clause))

def OriginAt (packet : Packet roles) (child : Occurrence roles) (position : Nat) (origin : Origin) : Prop :=
  ∃ clause ∈ packet.declaration.requirements, ∃ valid : clause.Signature roles,
    ∃ index : Fin (roles clause.role).arity, child = clauseChild packet clause valid ∧ position = index.val ∧
    ∃ capture ∈ (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds).captures,
      capture.name ∈ packet.declaration.inputNames ∧ capture.origin = some origin ∧
      GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var capture.name

theorem origin_sound (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) (origin : Origin)
    (recorded : OriginAt packet child index.val origin)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    (∃ actual, Observes model origin actual) ∧ ∀ actual, Observes model origin actual →
      GeneralNominalCaptureMerges.Fits model (child.demand.arguments index) actual := by
  obtain ⟨clause,_,signature,position,rfl,same,capture,member,declared,recorded,pattern⟩ := recorded
  have equal : index = position := Fin.ext same
  subst position
  exact GeneralNominalSourceReadback.variable_child_origin packet.registry packet.context packet.site.occurrence
    packet.declaration packet.checked packet.bounds model valid capture member declared origin recorded clause signature index pattern

noncomputable def childOrigin (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) : Option Origin := by
  classical
  exact if h : ∃ origin, OriginAt packet child index.val origin then some (Classical.choose h)
    else (pointSite child).inputs[index.val]'(by rw [(pointSite child).arity]; exact index.isLt)

noncomputable def childSite (packet : Packet roles) (child : Occurrence roles) : Site roles where
  occurrence := child
  inputs := List.ofFn (childOrigin packet child)
  arity := List.length_ofFn

theorem child_retains_origin (packet : Packet roles) (child : Occurrence roles)
    (index : Fin (roles child.demand.role).arity) (existsOrigin : ∃ origin, OriginAt packet child index.val origin) :
    ∃ origin, (childSite packet child).inputs[index.val]? = some (some origin) ∧ OriginAt packet child index.val origin := by
  classical
  refine ⟨Classical.choose existsOrigin,?_,Classical.choose_spec existsOrigin⟩
  simp [childSite,childOrigin,existsOrigin]

theorem child_sound (packet : Packet roles) (child : Occurrence roles)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) : SiteHolds (childSite packet child) model := by
  classical
  intro index origin recorded
  have entry : childOrigin packet child index = some origin := by
    change (List.ofFn (childOrigin packet child))[index.val]? = some (some origin) at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact Option.some.inj recorded
    · contradiction
  by_cases found : ∃ origin, OriginAt packet child index.val origin
  · have same : Classical.choose found = origin := Option.some.inj (by simpa [childOrigin,found] using entry)
    subst origin
    exact origin_sound packet child index _ (Classical.choose_spec found) model valid
  · have point : (pointSite child).inputs[index.val]? = some (some origin) := by
      have bound : index.val < (pointSite child).inputs.length := by rw [(pointSite child).arity]; exact index.isLt
      rw [List.getElem?_eq_getElem bound]
      simpa only [childOrigin,dite_eq_right found] using congrArg some entry
    exact point_holds child model index origin point

structure Emission (packet : Packet roles) where
  sites : List (Site roles)
  exact : sites.map Site.occurrence = packet.children
  sound : ∀ model, packet.Holds model → ∀ site ∈ sites, SiteHolds site model

noncomputable def emitted (packet : Packet roles) : Emission packet where
  sites := packet.children.map (childSite packet)
  exact := by simp [childSite,List.map_map,Function.comp_def]
  sound := by
    intro model valid site member
    obtain ⟨child,_,rfl⟩ := List.mem_map.mp member
    exact child_sound packet child model valid

def legacy (packet : Packet roles) (old : Emitted packet) : Emission packet :=
  ⟨old.sites,old.exact,old.sound⟩

def install (state : State roles) (packet : Packet roles) (emission : Emission packet) : State roles :=
  { state with
    context := packet.privateContext
    packets := packet :: state.packets
    sites := state.sites ++ emission.sites
    edges := state.edges ++ packet.children.map (fun child => (packet.site.occurrence,child)) }

theorem install_models (state : State roles) (packet : Packet roles) (emission : Emission packet)
    (same : packet.context = state.context) (model : GeneralNominalCommonBridge.Assignment) :
    Models (install state packet emission) model ↔ Models state model ∧ packet.Holds model := by
  constructor
  · rintro ⟨_,packets,sites⟩
    have current := packets packet (by simp [install])
    have original := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ current).1
    rw [same] at original
    exact ⟨⟨original,fun p hp => packets p (by simp [install,hp]),
      fun site hs => sites site (List.mem_append_left _ hs)⟩,current⟩
  · rintro ⟨old,current⟩
    refine ⟨current.1,?_,?_⟩
    · intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact current
      · exact old.2.1 p member
    · intro site member
      rcases List.mem_append.mp member with original | generated
      · exact old.2.2 site original
      · exact emission.sound model current site generated

theorem install_equivalent (state : State roles) (packet : Packet roles) (emission : Emission packet)
    (same : packet.context = state.context) (model : GeneralNominalCommonBridge.Assignment) :
    Models (install state packet emission) model ↔ Models (GeneralNominalSaturationState.install state packet (pointEmitted packet)) model :=
  (install_models state packet emission same model).trans (GeneralNominalSaturationState.install_models state packet _ same model).symm

def EndpointEqual (state : State roles) (bounds : GeneralSourceState.Interval) : Prop :=
  ∀ model, Models state model → Equivalent (model bounds.1).1 (model bounds.2).1

noncomputable def recoverOrigin (state : State roles) (site : Site roles)
    (index : Fin (roles site.occurrence.demand.role).arity) : Option Origin := by
  classical
  exact match site.inputs[index.val]'(by rw [site.arity]; exact index.isLt) with
    | some origin => some origin
    | none => if EndpointEqual state (site.occurrence.demand.arguments index)
        then some (.source (site.occurrence.demand.arguments index).1) else none

noncomputable def recover (state : State roles) (site : Site roles) : Site roles where
  occurrence := site.occurrence
  inputs := List.ofFn (recoverOrigin state site)
  arity := List.length_ofFn

theorem recover_sound (state : State roles) (site : Site roles)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) (sound : SiteHolds site model) :
    SiteHolds (recover state site) model := by
  classical
  intro index origin recorded
  have entry : recoverOrigin state site index = some origin := by
    change (List.ofFn (recoverOrigin state site))[index.val]? = some (some origin) at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact Option.some.inj recorded
    · contradiction
  have bound : index.val < site.inputs.length := by rw [site.arity]; exact index.isLt
  cases old : site.inputs[index.val]'(by rw [site.arity]; exact index.isLt) with
  | some prior =>
      have same : prior = origin := Option.some.inj (by simpa [recoverOrigin,old] using entry)
      subst origin
      apply sound index prior
      rw [List.getElem?_eq_getElem bound]
      exact congrArg some old
  | none =>
      by_cases equal : EndpointEqual state (site.occurrence.demand.arguments index)
      · have same : Origin.source (site.occurrence.demand.arguments index).1 = origin :=
          Option.some.inj (by simpa [recoverOrigin,old,equal] using entry)
        subst origin
        refine ⟨⟨_,.source _⟩,?_⟩
        intro actual seen
        cases seen
        exact ⟨subtype_refl _,(equal model valid).1⟩
      · simp [recoverOrigin,old,equal] at entry

noncomputable def SameInputs (state : State roles) (first last : Site roles) : Prop :=
  GeneralNominalDemandMerging.SameInputs (Models state) (recover state first) (recover state last)

theorem merge_dictionary_models (state : State roles) (first last : Site roles)
    (same : SameInputs state first last) (meaning : AssociatedMeaning)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (left : DictionaryOutputs meaning model (recover state first))
    (right : DictionaryOutputs meaning model (recover state last)) :
    Models (merge state first last) model := by
  apply (GeneralNominalSaturationState.merge_models state first last model).mpr
  exact ⟨valid,GeneralNominalDemandMerging.dictionary_outputs_preserved _ _ _ same meaning model valid left right⟩

end Yulang.GeneralNominalFeedbackSites
