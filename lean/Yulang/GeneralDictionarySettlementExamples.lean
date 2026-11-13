import Yulang.GeneralDictionaryAliasSettlement
import Yulang.GeneralDictionarySettledGuardedClassification
import Yulang.GeneralDictionarySettledReservedExample
import Yulang.GeneralDictionarySettledNamedExample

/-! Positive terminal recorded coverage and negative nonterminal coverage in
actual reachable stable I26 fixtures. These delimit the structural certificate;
semantic Evidence is not silently promoted to ledger settlement. -/
namespace Yulang.GeneralDictionarySettlementExamples
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState CommonRoleOutermostResolver
open GeneralDictionarySettledProjection GeneralDictionaryRecordedSettlement
section General
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

theorem terminal_path_eq {root child : Occurrence roles} {key : Nat}
    (selected : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root (.selected key []))
    (path : B4Target.Steps (fun parent child => Child
      (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child) : child = root := by
  induction path with
  | refl => rfl
  | tail prior edge ih =>
    obtain ⟨other,kids,localRule,member⟩ := edge
    rw [ih] at localRule
    have same := B4TargetV3.local_functional selected localRule
    cases same
    cases member

theorem terminal_coverage {root : Occurrence roles} {key : Nat} {packet : Packet roles}
    (selected : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root (.selected key []))
    (member : packet ∈ state.current.packets) (site : packet.site.occurrence = root)
    (empty : packet.children = []) : PacketCoverage registry state root := by
  intro child path other kids localRule
  have same := terminal_path_eq selected path
  subst child
  have aligned := B4TargetV3.local_functional selected localRule
  cases aligned
  exact ⟨packet,member,site,empty⟩

end General
namespace Reserved
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration)
open GeneralDictionaryReservedNominalRefresh
open GeneralDeclarationExamples (roles)

theorem selected : B4TargetV3.Local (fresh roles).toSourceBoundary registry refreshed root
    (.selected declaration.id []) := by
  apply GeneralDictionarySettledGuardedClassification.selected_local_iff.mpr
  refine ⟨(GeneralNominalValueBoundary.local_correspondence registry refreshed root _).mpr
    GeneralDictionaryReservedRefreshedClassification.value_selected,
    ?_⟩
  -- The actual producer only inspects the source-supported scalar slot.
  constructor
  · intro index
    exact ⟨_,_,Head.scalar (snapshot := snapshot) (1 : Fin 3) .int rfl,
      GeneralNominalSettledSupport.source_head refreshed
        (Head.scalar (snapshot := state) (1 : Fin 2) .int rfl)⟩
  · intro decl visible role bounds located slot inspected
    have options : slot = (0 : Fin 3) ∨ slot = (1 : Fin 3) ∨ slot = (2 : Fin 3) := by
      have bound := slot.isLt
      change slot.val < 3 at bound
      have val : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
      rcases val with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases options with rfl | rfl | rfl
    · exact ⟨_,_,Head.nominal (snapshot := snapshot) (0 : Fin 3) descriptor rfl,
        GeneralNominalSettledSupport.source_head refreshed
          (Head.nominal (snapshot := state) (0 : Fin 2) _ rfl)⟩
    · exact ⟨_,_,Head.scalar (snapshot := snapshot) (1 : Fin 3) .int rfl,
        GeneralNominalSettledSupport.source_head refreshed
          (Head.scalar (snapshot := state) (1 : Fin 2) .int rfl)⟩
    · exact GeneralDictionarySettledReservedExample.output_ready

theorem coverage : PacketCoverage registry refreshed root :=
  terminal_coverage selected packet_recorded rfl packet_children

theorem discharged : Discharged refreshed.current root := by
  apply classified_discharged root (.node declaration.id []) _ coverage
  cases selected with
  | selected safe unique => exact .selected safe unique .nil
end Reserved

namespace Nonterminal
open GeneralDictionarySupportRecursiveExample
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)

theorem no_exact_coverage : ¬ PacketCoverage registry finish displayRoot := by
  intro coverage
  exact GeneralDictionarySettledRecursiveExample.no_discharged displayRoot
    (classified_discharged displayRoot _ GeneralDictionarySettledRecursiveExample.classified coverage)

theorem no_alias_coverage : ¬ GeneralDictionaryAliasSettlement.AliasCoverage registry finish displayRoot := by
  intro coverage
  exact GeneralDictionarySettledRecursiveExample.no_discharged displayRoot
    (GeneralDictionaryAliasSettlement.classified_discharged displayRoot _
      GeneralDictionarySettledRecursiveExample.classified coverage)
end Nonterminal
end Yulang.GeneralDictionarySettlementExamples
