import Yulang.GeneralDictionaryDefaultIdentityCenters214

/-! Corrected merge edges identify actual centers semantically. Taking alias
closure does not require equal whole occurrences or equal source descriptors. -/
namespace Yulang.GeneralDictionaryDefaultAliasCenters215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalOriginTerms
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultIdentityCenters214 (CentersSame)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem lists_same {P : Assignment → Prop} {model : Assignment}
    (valid : P model) (first last : List Nat)
    (related : GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related P)
      (first.map fun x => some (Origin.source x)) (last.map fun x => some (Origin.source x)))
    (index : Nat) : Same model (.source (first[index]?.getD 0)) (.source (last[index]?.getD 0)) := by
  induction first generalizing last index with
  | nil =>
      cases last with
      | nil => exact source_self model 0
      | cons x xs => cases related
  | cons x xs ih =>
      cases last with
      | nil => cases related
      | cons y ys =>
          cases related with
          | cons head tail =>
              cases index with
              | zero =>
                  obtain ⟨a,b,one,two,same⟩ := head
                  cases Option.some.inj one
                  cases Option.some.inj two
                  exact same model valid
              | succ index => exact ih ys tail index

theorem same_inputs {P : Assignment → Prop} {model : Assignment}
    (valid : P model) (first last : Site roles) (same : SameInputs P first last) : CentersSame model first last := by
  have related := same.2
  change GeneralNominalDemandMerging.All₂ _ (List.ofFn _) (List.ofFn _) at related
  intro index
  apply lists_same valid (List.ofFn first.center) (List.ofFn last.center) _ index
  simpa only [List.map_ofFn, Function.comp_def] using related

theorem centers_symm (same : CentersSame model (first : Site roles) last) : CentersSame model last first :=
  fun index => same_symm (same index)

theorem centers_trans (one : CentersSame model (first : Site roles) middle)
    (two : CentersSame model middle last) : CentersSame model first last :=
  fun index => same_trans (one index) (two index)

theorem edge_producers
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ edge ∈ state.core.erased.current.aliases,
      ∃ first ∈ state.core.sites, ∃ last ∈ state.core.sites,
        first.occurrence.identity = edge.1 ∧ last.occurrence.identity = edge.2 ∧
        ∀ model, Models state model → CentersSame model first last := by
  induction path with
  | refl => intro edge member; cases member
  | @tail before after path step ih =>
      have growth := GeneralDictionaryDefaultGrowth208.step step
      have old edge (member : edge ∈ before.core.erased.current.aliases) :
          ∃ first ∈ after.core.sites, ∃ last ∈ after.core.sites,
            first.occurrence.identity = edge.1 ∧ last.occurrence.identity = edge.2 ∧
            ∀ model, Models after model → CentersSame model first last := by
        obtain ⟨first,one,last,two,a,b,same⟩ := ih edge member
        exact ⟨first,growth.sites one,last,growth.sites two,a,b,
          fun model valid => same model (stepModels step valid)⟩
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action => cases action <;> exact old
      | refresh | install => exact old
      | merge first last one two same novel =>
          intro edge member
          rcases List.mem_cons.mp member with rfl | prior
          · exact ⟨first,one,last,two,rfl,rfl,fun model valid =>
              same_inputs (merge_models.mp valid).1 first last same⟩
          · exact old _ prior

def RelatedCenters (state : State roles) (model : Assignment) (a b : Nat) : Prop :=
  a = b ∨ ∃ first ∈ state.core.sites, ∃ last ∈ state.core.sites,
    first.occurrence.identity = a ∧ last.occurrence.identity = b ∧ CentersSame model first last

theorem related_trans (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (valid : Models state model) (one : RelatedCenters state model a b) (two : RelatedCenters state model b c) :
    RelatedCenters state model a c := by
  rcases one with rfl | ⟨first,firstAt,middle,middleAt,firstId,middleId,left⟩
  · exact two
  rcases two with equal | ⟨middle',middleAt',last,lastAt,middleId',lastId,right⟩
  · exact Or.inr ⟨first,firstAt,middle,middleAt,firstId,middleId.trans equal,left⟩
  have centers := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same
    checked path middle middle' middleAt middleAt' (middleId.trans middleId'.symm) valid
  exact Or.inr ⟨first,firstAt,last,lastAt,firstId,lastId,centers_trans left (centers_trans centers right)⟩

theorem alias_related (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (valid : Models state model)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current a b) : RelatedCenters state model a b := by
  induction alias with
  | refl => exact Or.inl rfl
  | @edge a b member =>
      obtain ⟨first,one,last,two,left,right,same⟩ := edge_producers path (a,b) member
      exact Or.inr ⟨first,one,last,two,left,right,same model valid⟩
  | symm _ ih =>
      rcases ih with equal | ⟨first,one,last,two,left,right,same⟩
      · exact Or.inl equal.symm
      · exact Or.inr ⟨last,two,first,one,right,left,centers_symm same⟩
  | trans _ _ one two => exact related_trans checked path valid one two

theorem registered_alias_centers (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      first.occurrence.identity last.occurrence.identity) (valid : Models state model) : CentersSame model first last := by
  rcases alias_related checked path valid alias with equal | ⟨a,ha,b,hb,ida,idb,same⟩
  · exact GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same checked path first last one two equal valid
  · have left := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same checked path first a one ha ida.symm valid
    have right := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same checked path b last hb two idb valid
    exact centers_trans left (centers_trans same right)

end Yulang.GeneralDictionaryDefaultAliasCenters215
