import Yulang.GeneralNominalSlotObservation198

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalSlotReport198
open GeneralNominalState (State)
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRefinements (Refines renameDescriptor)
open GeneralNominalRefinementTrace197 (Observed ObservedMany)
open GeneralNominalSlotObservation198 (bounds embed_injective typeArguments_rename_some)
variable {before after : State}

def capture (embed : Fin before.base.slots → Fin after.base.slots) (item : Capture before) : Capture after :=
  ⟨item.name,bounds embed item.bounds,item.origin⟩
def report (embed : Fin before.base.slots → Fin after.base.slots) (item : Report before) : Report after :=
  ⟨item.captures.map (capture embed),item.inspected.map (bounds embed),item.checked.map (bounds embed),
    item.blocked.map (bounds embed),item.conflicts.map (bounds embed),item.arity,
    item.anchors.map (fun pair => (pair.1,bounds embed pair.2)),item.tests⟩

theorem report_append (embed : Fin before.base.slots → Fin after.base.slots) (first last : Report before) :
    report embed (first.append last) = (report embed first).append (report embed last) := by
  simp [report,Report.append,List.map_append]

theorem report_visit (embed : Fin before.base.slots → Fin after.base.slots)
    (pair : Bounds before) (origin : Option Origin) (test : Test) (item : Report before) :
    report embed (Report.visit pair origin test item) =
      Report.visit (bounds embed pair) origin test (report embed item) := by
  simp [report,Report.visit,List.map_append,List.map_map]

mutual
  theorem inspect_report (refinement : Refines before after) (source : Observed before query pair)
      (origin : Option Origin) :
      inspect after query (bounds refinement.base.embed pair) origin =
        report refinement.base.embed (inspect before query pair origin) := by
    cases source with
    | variables => simp [inspect,report,capture,List.map_map]
    | point recorded name arguments children =>
      have new := refinement.nominals _ _ recorded
      have args := typeArguments_rename_some refinement.base.embed arguments
      simp only [inspect,bounds,new,recorded,renameDescriptor,name,args,arguments,↓reduceIte]
      rw [refinement.base.source,inspectMany_report refinement children,report_visit]
      rfl
    | interval different lower upper lowerName upperName lowerArgs upperArgs left right =>
      have newLower := refinement.nominals _ _ lower
      have newUpper := refinement.nominals _ _ upper
      have argsLeft := typeArguments_rename_some refinement.base.embed lowerArgs
      have argsRight := typeArguments_rename_some refinement.base.embed upperArgs
      have unequal : refinement.base.embed pair.1 ≠ refinement.base.embed pair.2 :=
        fun same => different (embed_injective refinement same)
      simp only [inspect,bounds,newLower,newUpper,lower,upper,renameDescriptor,
        lowerName,upperName,argsLeft,argsRight,lowerArgs,upperArgs,unequal,different,↓reduceIte]
      rw [refinement.base.source,refinement.base.source,
        inspectMany_report refinement left,inspectMany_report refinement right,report_visit,report_append]
      rfl
  termination_by sizeOf query

  theorem inspectMany_report (refinement : Refines before after) (source : ObservedMany before queries pairs)
      (origins : Nat → Option Origin) (index : Nat) :
      inspectMany after queries (pairs.map (bounds refinement.base.embed)) origins index =
        report refinement.base.embed (inspectMany before queries pairs origins index) := by
    cases source with
    | nil => simp [inspectMany,report]
    | cons first rest =>
      simp only [List.map_cons,inspectMany]
      rw [inspect_report refinement first,inspectMany_report refinement rest,report_append]
  termination_by sizeOf queries
end
end Yulang.GeneralNominalSlotReport198
