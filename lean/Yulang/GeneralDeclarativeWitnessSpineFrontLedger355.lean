import Yulang.GeneralDeclarativeWitnessSpineLedger355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSpineFrontLedger355
open GeneralDeclarativeWitnessSpineFront355 (Source Found Wire read Site Authors)
open GeneralDeclarativeWitnessSpineNode355 (Author Node)
open GeneralDeclarativeWitnessSpineLedger355 (Validated Checked.keys Checked.original Checked.authors Checked.nodePaths)
open GeneralDeclarativeWitnessCovariantWrittenState353 (rebuild)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessTypedRelease354 (Key Authority)
open GeneralSourceMetadataExprDomain291 (bind_success)
open CommonRoleOutermostResolver (All₂)

def declared (k : Key) (a : Site) : Prop :=
  k.ordinal = a.write ∧ k ∈ a.authority.released ∧ k.stamp ∈ a.authority.active ∧
    (a.authority.active.map GeneralDeclarativeWitnessTypedRelease354.position).Nodup

theorem declared_authorities {cat p a} (independent : Authors cat p a)
    {xs : List Key} (author : All₂ Validated xs a) : All₂ declared xs p := by
  induction independent generalizing xs with
  | nil =>
    cases author
    exact .nil
  | cons someRows rest ih =>
    cases author with
    | cons h zs => exact .cons h (ih zs)

theorem actual_continuation {p s w} {a : Found p s w} (r : read p s w = some a) :
    GeneralDeclarativeWitnessNominalSpine355.read a.root a.rawAuthors w.continuation = some a.checked := by
  unfold GeneralDeclarativeWitnessSpineFront355.read at r
  split at r
  · cases r
  · obtain ⟨broad,done,rest⟩ := bind_success r
    obtain ⟨checked,verified,end_⟩ := bind_success rest
    obtain ⟨whole,real,tail⟩ := bind_success end_
    split at tail
    · split at tail
      · cases Option.some.inj tail
        exact real
      · cases tail
    · cases tail

theorem authorized_from_external_source {p s w} {a : Found p s w} (r : read p s w = some a) :
    All₂ declared (Checked.keys a.checked) p.routes ∧
    Checked.original a.checked = w.continuation ∧
    List.Pairwise (fun x y : List Nat => x.length < y.length) (Checked.nodePaths a.checked) := by
  have actual := actual_continuation r
  exact ⟨declared_authorities a.authors (GeneralDeclarativeWitnessSpineLedger355.every_source_release actual),
    (GeneralDeclarativeWitnessSpineLedger355.exact_source_vector actual).2,
    (GeneralDeclarativeWitnessSpineLedger355.path_lengths a.checked).1⟩

end Yulang.GeneralDeclarativeWitnessSpineFrontLedger355
