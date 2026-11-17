import Yulang.GeneralNominalRebaseJournalView243
import Yulang.GeneralNominalRebasePacketActivation243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseJournalSupport243
open GeneralNominalRebaseJournalView243 (Journal Effect)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242

theorem list_iff (items : List α) (sources : α → List Nat) (holds : α → Assignment → Prop)
 (exact : ∀ item, ∀ {first last}, Agree (sources item) first last → (holds item first ↔ holds item last))
 {first last} (same : Agree (items.flatMap sources) first last) :
 (∀ item ∈ items, holds item first) ↔ ∀ item ∈ items, holds item last := by
 apply forall_congr'; intro item
 apply forall_congr'; intro member
 exact exact item (fun name present => same name (List.mem_flatMap.mpr ⟨item,member,present⟩))

def classSources (view : GeneralNominalRebaseClassView243.View) : List Nat :=
 view.equations.flatMap GeneralNominalRebaseEffectActivation243.equationSources ++
 view.equalities.flatMap GeneralNominalState.atomSources

theorem class_iff (view : GeneralNominalRebaseClassView243.View) {first last}
 (same : Agree (classSources view) first last) : view.Holds first ↔ view.Holds last := by
 apply and_congr
 · exact list_iff view.equations _ (fun e m => e.Holds m)
     (fun e _ _ h => GeneralNominalRebaseEffectActivation243.equation_iff e h)
     (fun name present => same name (List.mem_append_left _ present))
 · exact list_iff view.equalities _ (fun a m => a.Holds CommonNominalFullCarrier.model m)
     (fun a _ _ h => GeneralNominalCenteredModelExtension.atom_same a h)
     (fun name present => same name (List.mem_append_right _ present))

def observedSources (argument : GeneralNominalRebaseObservedSite243.Argument) : List Nat :=
 GeneralNominalRebaseProjectionSupport243.boundsSources argument.bounds ++
 argument.origin.toList.flatMap GeneralNominalRebaseOriginActivation243.sources

theorem observed_iff (argument : GeneralNominalRebaseObservedSite243.Argument) {first last}
 (same : Agree (observedSources argument) first last) : argument.Holds first ↔ argument.Holds last := by
 apply forall_congr'; intro origin
 apply forall_congr'; intro found
 have obs (actual) := GeneralNominalRebaseOriginActivation243.observes_iff origin
   (fun name present => same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨origin,by simpa using found,present⟩))) actual
 have bounds (actual) := GeneralNominalRebaseProjectionSupport243.bounds_iff argument.bounds
   (fun name present => same name (List.mem_append_left _ present)) actual
 simp only [obs,bounds]

def effectBlocks (effect : Effect) : List (List Nat) :=
 [GeneralNominalRebaseViewSupport243.sources effect.raw,
 GeneralNominalRebaseProjectionSupport243.reportSources effect.projection,
 classSources effect.historical,classSources effect.live]

def effectSources (effect : Effect) : List Nat := (effectBlocks effect).flatten

theorem effect_iff (effect : Effect) {first last}
 (same : Agree (effectSources effect) first last) : effect.Holds first ↔ effect.Holds last := by
 have part (part : List Nat) (member : part ∈ effectBlocks effect) : Agree part first last :=
   fun name present => same name (List.mem_flatten.mpr ⟨part,member,present⟩)
 exact and_congr (GeneralNominalRebaseViewSupport243.models_iff _ (part _ (by simp [effectBlocks])))
   (and_congr (GeneralNominalRebaseProjectionSupport243.models_iff _ (part _ (by simp [effectBlocks])))
   (and_congr (class_iff _ (part _ (by simp [effectBlocks]))) (class_iff _ (part _ (by simp [effectBlocks])))))

def blocks (journal : Journal) : List (List Nat) :=
 [GeneralNominalRebaseViewSupport243.sources journal.current,
 GeneralNominalRebaseViewSupport243.sources journal.source,
 journal.observed.flatMap (fun arguments => arguments.flatMap observedSources),
 journal.sites.flatMap GeneralNominalRebaseViewActivation243.siteSources,
 journal.packets.flatMap GeneralNominalRebasePacketSupport243.sources,
 journal.effects.flatMap effectSources]

def sources (journal : Journal) : List Nat := (blocks journal).flatten

theorem models_iff (journal : Journal) {first last}
 (same : Agree (sources journal) first last) : journal.Models first ↔ journal.Models last := by
 have part (part : List Nat) (member : part ∈ blocks journal) : Agree part first last :=
   fun name present => same name (List.mem_flatten.mpr ⟨part,member,present⟩)
 apply and_congr (GeneralNominalRebaseViewSupport243.models_iff _ (part _ (by simp [blocks])))
 apply and_congr (GeneralNominalRebaseViewSupport243.models_iff _ (part _ (by simp [blocks])))
 apply and_congr
 · exact list_iff journal.observed _ _
     (fun args _ _ h => list_iff args observedSources _ (fun arg _ _ h => observed_iff arg h) h)
     (part _ (by simp [blocks]))
 apply and_congr
 · exact list_iff journal.sites _ _ (fun site _ _ h => GeneralNominalRebaseViewActivation243.site_same site h)
     (part _ (by simp [blocks]))
 apply and_congr
 · exact list_iff journal.packets _ _ (fun packet _ _ h => GeneralNominalRebasePacketSupport243.models_iff packet h)
     (part _ (by simp [blocks]))
 exact list_iff journal.effects _ _ (fun effect _ _ h => effect_iff effect h) (part _ (by simp [blocks]))

def Checked (entries : List Entry) (journal : Journal) : Prop :=
 ∀ entry ∈ entries, entry.1 ∉ sources journal

def check (entries : List Entry) (journal : Journal) : Bool :=
 entries.all (fun entry => !(sources journal).contains entry.1)

theorem check_iff (entries : List Entry) (journal : Journal) : check entries journal = true ↔ Checked entries journal := by
 simp [check,Checked]

theorem kept_iff (entries : List Entry) (journal : Journal) (checked : Checked entries journal)
 {first last} (kept : Preserves entries first last) : journal.Models first ↔ journal.Models last := by
 apply models_iff
 intro name present
 apply kept.1 name
 intro entry member equal
 exact checked entry member (equal ▸ present)

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (journal : Journal) (checked : Checked entries journal) (model : Assignment) (valid : journal.Models model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧ journal.Models (patch entries model) :=
 ⟨patch_preserves entries model,patch_definitions entries coherent external model,
 (kept_iff entries journal checked (patch_preserves entries model)).mpr valid⟩

theorem projection_iff (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (journal : Journal) (checked : Checked entries journal) (model : Assignment) :
 journal.Models model ↔ ∃ next, Preserves entries next model ∧ Definitions entries next ∧ journal.Models next := by
 constructor
 · intro valid
   exact ⟨patch entries model,activate entries coherent external journal checked model valid⟩
 · rintro ⟨next,kept,_,valid⟩
   exact (kept_iff entries journal checked kept).mp valid

/-- All actual journal fields share the same transformed assignment. The finite
check is explicit; no invariant ensuring it after every operation is asserted. -/
theorem compiled_activation (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (state : GeneralNominalVersionedJournal232.State roles)
 (empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty state)
 (mapping : Nat → Core.PresenceGeneration.CompTerm Nat)
 (checked : check entries (GeneralNominalRebaseJournalView243.compile state mapping) = true)
 (model : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models state (GeneralNominalRebaseRawView243.read mapping model)) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 GeneralNominalVersionedJournal232.Models state (GeneralNominalRebaseRawView243.read mapping (patch entries model)) := by
 obtain ⟨kept,definitions,valid⟩ := activate entries coherent external _ ((check_iff ..).mp checked) model
   ((GeneralNominalRebaseJournalView243.compile_exact state empty mapping model).mpr valid)
 exact ⟨kept,definitions,(GeneralNominalRebaseJournalView243.compile_exact state empty mapping _).mp valid⟩
end Yulang.GeneralNominalRebaseJournalSupport243
