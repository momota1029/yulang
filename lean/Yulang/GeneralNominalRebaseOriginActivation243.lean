import Yulang.GeneralNominalRebaseOriginView243
import Yulang.GeneralNominalRebaseViewActivation243
set_option backward.isDefEq.respectTransparency false
/-! The activation check also covers all observations along retained nominal
and structural origin paths. Every observed witness is preserved, not chosen. -/
namespace Yulang.GeneralNominalRebaseOriginActivation243
open GeneralNominalRebaseOriginView243
open GeneralNominalRebaseViewActivation243 (Consumers ValuesAgree)
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalFiniteEquationRealization236
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseRawView243 (View)
open GeneralNominalRebaseLiveView243 (Site)

def sources : Origin → List Nat
 | .source term => GeneralNominalState.typeSources term
 | .nominal parent _ _ => sources parent
 | .structural parent _ _ => sources parent

theorem observes_iff (origin : Origin) {first last : Assignment}
 (same : Agree (sources origin) first last) (value) :
 Observes first origin value ↔ Observes last origin value := by
 induction origin generalizing value with
 | source term =>
   have equal := GeneralNominalCenteredModelExtension.type_eval_same term same
   constructor
   · intro observed
     cases observed
     rw [equal]
     exact .source _
   · intro observed
     cases observed
     rw [← equal]
     exact .source _
 | nominal parent name index ih =>
   constructor
   · intro observed
     cases observed with
     | nominal seen equal found => exact .nominal ((ih same _).mp seen) equal found
   · intro observed
     cases observed with
     | nominal seen equal found => exact .nominal ((ih same _).mpr seen) equal found
 | structural parent shape index ih =>
   constructor
   · intro observed
     cases observed with
     | structural seen length equal found => exact .structural ((ih same _).mp seen) length equal found
   · intro observed
     cases observed with
     | structural seen length equal found => exact .structural ((ih same _).mpr seen) length equal found

theorem head_iff (origin : Origin) {first last : Assignment}
 (same : Agree (sources origin) first last) (test) :
 Head first origin test ↔ Head last origin test := by
 simp only [Head,observes_iff origin same]

theorem same_iff (one two : Origin) {first last : Assignment}
 (same : Agree (sources one ++ sources two) first last) :
 Same first one two ↔ Same last one two := by
 have oneEq := observes_iff one (fun name member => same name (List.mem_append_left _ member))
 have twoEq := observes_iff two (fun name member => same name (List.mem_append_right _ member))
 simp only [Same,oneEq,twoEq]

def reads (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (origins : List Origin) : List Nat :=
 GeneralNominalRebaseViewActivation243.reads view atoms sites ++ origins.flatMap sources

def Checked (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) : Prop :=
 ∀ entry ∈ entries, entry.1 ∉ reads view atoms sites origins

def check (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) : Bool :=
 entries.all (fun entry => !(reads view atoms sites origins).contains entry.1)

theorem check_iff (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) :
 check entries view atoms sites origins = true ↔ Checked entries view atoms sites origins := by
 simp [check,Checked]

theorem observes_preserved (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) (checked : Checked entries view atoms sites origins)
 {first last : Assignment} (kept : Preserves entries first last) :
 ∀ origin ∈ origins, ∀ value, Observes first origin value ↔ Observes last origin value := by
 intro origin member value
 apply observes_iff
 intro name present
 apply kept.1 name
 intro entry included equal
 apply checked entry included
 rw [equal]
 exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨origin,member,present⟩)

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (origins : List Origin) (checked : Checked entries view atoms sites origins)
 (model : Assignment) (valid : Consumers view atoms sites model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 Consumers view atoms sites (patch entries model) ∧ ValuesAgree sites (patch entries model) model ∧
 ∀ origin ∈ origins, ∀ value, Observes (patch entries model) origin value ↔ Observes model origin value := by
 have localCheck : GeneralNominalRebaseViewActivation243.Checked entries view atoms sites :=
   fun entry member present => checked entry member (List.mem_append_left _ present)
 obtain ⟨kept,definitions,consumers,values⟩ :=
   GeneralNominalRebaseViewActivation243.activate entries coherent external view atoms sites localCheck model valid
 exact ⟨kept,definitions,consumers,values,observes_preserved entries view atoms sites origins checked kept⟩
end Yulang.GeneralNominalRebaseOriginActivation243
