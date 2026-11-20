import Yulang.GeneralGeneratedDisplayParentCurrent299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedDisplayBothCurrent299
open GeneralNominalExamples (registry model displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseCompiledDisplay277 (after compiled)
open GeneralGeneratedDisplayTable299 (table decode rank rows faithful in_scope ranked closed computed_root)
open GeneralGeneratedMixedCurrentNodes299 (Providers scoped_nodes)
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open B4TargetV8

theorem providers : Providers registry after table decode := by
  intro i e hit _
  rcases rows i e hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨_,GeneralGeneratedDisplayParentCurrent299.current⟩
  · exact ⟨_,GeneralRebaseGeneratedCurrent298.current⟩

theorem local_nodes : Nodes (boundary roles) registry after table decode :=
  scoped_nodes table decode GeneralRebaseCompiledInstall277.reachable faithful in_scope providers

/-- This concrete production does not require the previous monolithic
EvidenceAt theorem or a supplied child dictionary. The tables' two guarded
current effects supply only the local rules; the reader supplies the tree. -/
theorem root_from_current (m) (held : Models after m) :
    (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) :=
  GeneralGeneratedDictionaryNodes299.same_model (b := boundary roles) (r := registry) (s := after) table decode local_nodes m held 2 0 _
    computed_root

theorem child_from_current (m) (held : Models after m) :
    (boundary roles).Evidence registry after m displayChild (.node 3 []) :=
  GeneralGeneratedDictionaryNodes299.same_model (b := boundary roles) (r := registry) (s := after) table decode local_nodes m held 1 1 _
    GeneralGeneratedDisplayTable299.computed_child

theorem instantiated :
    (∃ m, Models after m) ∧
    (Reachable (boundary roles) registry displayRoot after) ∧
    (∀ m, Models after m →
      (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) ∧
      (boundary roles).Evidence registry after m displayChild (.node 3 [])) :=
  ⟨⟨model,GeneralRebaseCompiledSelection277.after_model⟩,GeneralRebaseCompiledInstall277.reachable,
    fun m valid => ⟨root_from_current m valid,child_from_current m valid⟩⟩

end Yulang.GeneralGeneratedDisplayBothCurrent299
