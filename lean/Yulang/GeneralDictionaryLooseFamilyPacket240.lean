import Yulang.GeneralDictionaryLooseFamilySnapshot240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseFamilyPacket240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseLoopSource240 (roles registry declaration declaration_checked root model)
open GeneralDictionaryLooseFamilyNames240 (lower repeated)
open GeneralDictionaryLooseLoopPacket240 (origin0 origin1)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,context n allocated reserved ordinary,GeneralNominalDemandMerging.pointSite root,
 declaration,declaration_checked,[(original n 3,original n 3)]⟩
abbrev plan : GeneralNominalCenters.Plan roles := ⟨packet n allocated reserved ordinary,GeneralNominalCenters.rootSite 4 root,rfl⟩
abbrev calculated : Report (snapshot n allocated reserved ordinary) where
 captures := [⟨0,(anchor n,original n 4),some origin0⟩,⟨0,(anchor n,original n 4),some origin1⟩]
 inspected := [(original n 3,original n 3)]
 checked := [(original n 3,original n 3),(original n 3,original n 3),(anchor n,original n 4),(anchor n,original n 4)]
 anchors := [(origin0,anchor n,original n 4),(origin1,anchor n,original n 4)]

theorem query : GeneralNominalInspection.queries (snapshot n allocated reserved ordinary)
 GeneralDictionaryLooseLoopSource240.interpretation declaration =
 [.nominal 5 [.variables [0],.variables [0]]] := GeneralDictionaryLooseLoopPacket240.query

theorem report_exact : report (context n allocated reserved ordinary) declaration [(original n 3,original n 3)] =
 calculated n allocated reserved ordinary := by
 unfold report
 rw [query]
 have value3 : ((3 : Fin 5) : Nat) = 3 := rfl
 simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,calculated,pair,original,value3]
 rw [inspectMany.eq_2,inspectMany.eq_2,inspectMany.eq_1]
 simp only [inspect.eq_1,Report.append]
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem bindings_exact : (packet n allocated reserved ordinary).bindings = repeated (lower n) := by
 change bindings (snapshot n allocated reserved ordinary)
   (report (context n allocated reserved ordinary) declaration [(original n 3,original n 3)]) = _
 rw [report_exact]
 simp [bindings,GeneralDictionaryLooseFamilyNames240.repeated,source_anchor,source_original]
 rfl
end Yulang.GeneralDictionaryLooseFamilyPacket240
