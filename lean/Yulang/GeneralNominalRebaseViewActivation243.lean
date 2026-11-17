import Yulang.GeneralNominalRebaseViewSupport243
import Yulang.GeneralNominalRebaseLiveView243
import Yulang.GeneralNominalRebaseEscapedProjection242
set_option backward.isDefEq.respectTransparency false
/-! Inactive-cell activation after expression translation. The finite check
includes all nominal View reads, live centers, and live output expressions. -/
namespace Yulang.GeneralNominalRebaseViewActivation243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseRawView243 (View)
open GeneralNominalRebaseLiveView243 (Site Argument)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalState (typeSources atomSources)
open GeneralNominalCenteredModelExtension

def argumentSources (argument : Argument) : List Nat :=
 typeSources argument.lower ++ typeSources argument.upper ++ typeSources argument.center

def siteSources (site : Site) : List Nat :=
 site.arguments.flatMap argumentSources ++ site.outputs.flatMap (fun output => typeSources output.target)

def reads (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site) : List Nat :=
 GeneralNominalRebaseViewSupport243.sources view ++ atoms.flatMap atomSources ++ sites.flatMap siteSources

def Checked (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) : Prop := ∀ entry ∈ entries, entry.1 ∉ reads view atoms sites

def check (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) : Bool := entries.all (fun entry => !(reads view atoms sites).contains entry.1)

theorem check_iff (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) : check entries view atoms sites = true ↔ Checked entries view atoms sites := by
 simp [check,Checked]

def Consumers (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (model : Assignment) : Prop := view.Models model ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧ ∀ site ∈ sites, site.Holds model

def ValuesAgree (sites : List Site) (first last : Assignment) : Prop :=
 (∀ site ∈ sites, ∀ argument ∈ site.arguments,
   argument.center.eval CommonNominalFullCarrier.model first = argument.center.eval CommonNominalFullCarrier.model last) ∧
 (∀ site ∈ sites, ∀ output ∈ site.outputs,
   output.target.eval CommonNominalFullCarrier.model first = output.target.eval CommonNominalFullCarrier.model last)

theorem agree_reads (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (checked : Checked entries view atoms sites) {first last : Assignment}
 (kept : Preserves entries first last) : Agree (reads view atoms sites) first last := by
 intro name member
 apply kept.1 name
 intro entry present equal
 exact checked entry present (equal.symm ▸ member)

theorem site_same (site : Site) {first last : Assignment} (same : Agree (siteSources site) first last) :
 site.Holds first ↔ site.Holds last := by
 apply forall_congr'; intro argument
 apply forall_congr'; intro member
 have argumentSame : Agree (argumentSources argument) first last := fun name present =>
   same name (List.mem_append_left _ (List.mem_flatMap.mpr ⟨argument,member,present⟩))
 have lower := type_eval_same argument.lower (fun name present => argumentSame name
   (List.mem_append_left _ (List.mem_append_left _ present)))
 have upper := type_eval_same argument.upper (fun name present => argumentSame name
   (List.mem_append_left _ (List.mem_append_right _ present)))
 have center := type_eval_same argument.center (fun name present => argumentSame name
   (List.mem_append_right _ present))
 unfold GeneralNominalRebaseLiveView243.Argument.Holds
 rw [lower,upper,center]

theorem consumers_iff (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) {first last : Assignment} (same : Agree (reads view atoms sites) first last) :
 Consumers view atoms sites first ↔ Consumers view atoms sites last := by
 apply and_congr (GeneralNominalRebaseViewSupport243.models_iff view
   (fun name member => same name (List.mem_append_left _ (List.mem_append_left _ member))))
 apply and_congr
 · apply forall_congr'; intro atom
   apply forall_congr'; intro member
   exact atom_same atom (fun name present => same name
     (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨atom,member,present⟩))))
 · apply forall_congr'; intro site
   apply forall_congr'; intro member
   exact site_same site (fun name present => same name
     (List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,member,present⟩)))

theorem values_same (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) {first last : Assignment} (same : Agree (reads view atoms sites) first last) :
 ValuesAgree sites first last := by
 constructor
 · intro site member argument present
   apply type_eval_same
   intro name source
   exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,member,
     List.mem_append_left _ (List.mem_flatMap.mpr ⟨argument,present,List.mem_append_right _ source⟩)⟩))
 · intro site member output present
   apply type_eval_same
   intro name source
   exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,member,
     List.mem_append_right _ (List.mem_flatMap.mpr ⟨output,present,source⟩)⟩))

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (checked : Checked entries view atoms sites) (model : Assignment) (valid : Consumers view atoms sites model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 Consumers view atoms sites (patch entries model) ∧ ValuesAgree sites (patch entries model) model := by
 have kept := patch_preserves entries model
 have same := agree_reads entries view atoms sites checked kept
 exact ⟨kept,patch_definitions entries coherent external model,
   (consumers_iff view atoms sites same).mpr valid,values_same view atoms sites same⟩

theorem projection_iff (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (checked : Checked entries view atoms sites) (model : Assignment) :
 Consumers view atoms sites model ↔
 ∃ next, Preserves entries next model ∧ Definitions entries next ∧
 Consumers view atoms sites next ∧ ValuesAgree sites next model := by
 constructor
 · intro valid
   exact ⟨patch entries model,activate entries coherent external view atoms sites checked model valid⟩
 · rintro ⟨next,kept,_,valid,_⟩
   exact (consumers_iff view atoms sites (agree_reads entries view atoms sites checked kept)).mp valid
end Yulang.GeneralNominalRebaseViewActivation243
