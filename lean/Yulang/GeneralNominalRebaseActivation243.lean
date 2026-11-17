import Yulang.GeneralNominalRebaseEscapedProjection242
import Yulang.GeneralDictionaryDefaultRawSupport213
import Yulang.GeneralNominalRebaseLiveLabels241
set_option backward.isDefEq.respectTransparency false
/-! Checked activation of previously unread private type cells. Reservations
alone are not reads. All raw nominal constraints, supplied atoms and live site
endpoint/center consumers remain present. -/
namespace Yulang.GeneralNominalRebaseActivation243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalCenters
open GeneralNominalCenteredFrame179 (Agree)

variable {roles : Roles.RoleDecls}
def siteSources (site : Site roles) : List Nat :=
 (List.ofFn (fun index => [(site.occurrence.demand.arguments index).1,
   (site.occurrence.demand.arguments index).2,site.center index])).flatten

def reads (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List (Site roles)) : List Nat :=
 GeneralDictionaryDefaultRawSupport213.sources raw ++
 atoms.flatMap GeneralNominalState.atomSources ++ sites.flatMap siteSources

def Checked (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles)) : Prop :=
 ∀ entry ∈ entries, entry.1 ∉ reads raw atoms sites

def Consumers (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List (Site roles)) (model : Assignment) : Prop :=
 GeneralNominalState.Models raw model ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧
 ∀ site ∈ sites, site.Holds model

theorem endpoint_center (site : Site roles) (index) :
 (site.occurrence.demand.arguments index).1 ∈ siteSources site ∧
 (site.occurrence.demand.arguments index).2 ∈ siteSources site ∧
 site.center index ∈ siteSources site := by
 have listMem : [(site.occurrence.demand.arguments index).1,
   (site.occurrence.demand.arguments index).2,site.center index] ∈
   List.ofFn (fun i => [(site.occurrence.demand.arguments i).1,
     (site.occurrence.demand.arguments i).2,site.center i]) := List.mem_ofFn.mpr ⟨index,rfl⟩
 exact ⟨List.mem_flatten.mpr ⟨_,listMem,by simp⟩,
   List.mem_flatten.mpr ⟨_,listMem,by simp⟩,List.mem_flatten.mpr ⟨_,listMem,by simp⟩⟩

theorem agree_reads (entries : List Entry) (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 (checked : Checked entries raw atoms sites) {first last : Assignment}
 (preserved : Preserves entries first last) : Agree (reads raw atoms sites) first last := by
 intro name member
 apply preserved.1 name
 intro entry present equal
 exact checked entry present (equal.symm ▸ member)

theorem consumers_iff (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 {first last : Assignment} (same : Agree (reads raw atoms sites) first last) :
 Consumers raw atoms sites first ↔ Consumers raw atoms sites last := by
 have rawSame : Agree (GeneralDictionaryDefaultRawSupport213.sources raw) first last :=
   fun name member => same name (List.mem_append_left _ (List.mem_append_left _ member))
 have atomSame : PresenceNormalForm.All CommonNominalFullCarrier.model first atoms ↔
   PresenceNormalForm.All CommonNominalFullCarrier.model last atoms := by
   apply forall_congr'; intro atom
   apply forall_congr'; intro member
   exact GeneralNominalCenteredModelExtension.atom_same atom (fun name present =>
     same name (List.mem_append_left _ (List.mem_append_right _
       (List.mem_flatMap.mpr ⟨atom,member,present⟩))))
 apply and_congr (GeneralDictionaryDefaultRawSupport213.models_iff raw rawSame)
 apply and_congr atomSame
 apply forall_congr'; intro site
 apply forall_congr'; intro member
 apply forall_congr'; intro index
 have sources := endpoint_center site index
 have point (name : Nat) (present : name ∈ siteSources site) : first name = last name :=
   same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,member,present⟩))
 unfold GeneralNominalCaptureMerges.Fits
 rw [point _ sources.1,point _ sources.2.1,point _ sources.2.2]

theorem centers (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List (Site roles))
 {first last : Assignment} (same : Agree (reads raw atoms sites) first last) :
 GeneralNominalRebaseLiveLabels241.CentersAgree sites first last := by
 intro site member index
 rw [same _ (List.mem_append_right _
   (List.mem_flatMap.mpr ⟨site,member,(endpoint_center site index).2.2⟩))]
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List (Site roles)) (checked : Checked entries raw atoms sites)
 (model : Assignment) (valid : Consumers raw atoms sites model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 Consumers raw atoms sites (patch entries model) ∧
 GeneralNominalRebaseLiveLabels241.CentersAgree sites (patch entries model) model := by
 have kept := patch_preserves entries model
 have same := agree_reads entries raw atoms sites checked kept
 exact ⟨kept,patch_definitions entries coherent external model,
   (consumers_iff raw atoms sites same).mpr valid,centers raw atoms sites same⟩

theorem projection_iff (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (raw : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List (Site roles)) (checked : Checked entries raw atoms sites) (model : Assignment) :
 Consumers raw atoms sites model ↔
 ∃ next, Preserves entries next model ∧ Definitions entries next ∧
 Consumers raw atoms sites next ∧ GeneralNominalRebaseLiveLabels241.CentersAgree sites next model := by
 constructor
 · intro valid
   exact ⟨patch entries model,activate entries coherent external raw atoms sites checked model valid⟩
 · rintro ⟨next,kept,_,valid,_⟩
   exact (consumers_iff raw atoms sites (agree_reads entries raw atoms sites checked kept)).mp valid
end Yulang.GeneralNominalRebaseActivation243
