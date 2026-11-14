import Yulang.GeneralNominalMetadataInspection

/-! Inspection reports retain every capture, anchor and test when only
reservation and ownership enumeration changes. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalReportMetadata
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalMetadataEquivalence (replace)
variable (state : GeneralNominalState.State)
    (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

def capture (entry : Capture state) : Capture (replace state allocated reserved) :=
  ⟨entry.name,entry.bounds,entry.origin⟩

def report (value : Report state) : Report (replace state allocated reserved) :=
  ⟨value.captures.map (capture state allocated reserved),value.inspected,value.checked,value.blocked,value.conflicts,
    value.arity,value.anchors,value.tests⟩

theorem append (one two : Report state) : report state allocated reserved (one.append two) =
    (report state allocated reserved one).append (report state allocated reserved two) := by
  simp only [report,Report.append,List.map_append]

theorem visit (value : Report state) (bounds origin test) : report state allocated reserved (value.visit bounds origin test) =
    Report.visit (state := replace state allocated reserved) bounds origin test (report state allocated reserved value) := rfl

mutual
  theorem inspect (query : Query) (bounds : Bounds state) (origin : Option Origin) :
      report state allocated reserved (GeneralNominalRecursiveInspection.inspect state query bounds origin) =
        GeneralNominalRecursiveInspection.inspect (replace state allocated reserved) query bounds origin := by
    cases query with
    | variables names =>
      simp only [GeneralNominalRecursiveInspection.inspect,report,List.map_map,Function.comp_def,capture]
    | deferred pattern => simp only [GeneralNominalRecursiveInspection.inspect,block,report,List.map_nil]
    | scalar expected =>
      simp only [GeneralNominalRecursiveInspection.inspect,visit,replace]
      congr 1
      split
      · rfl
      · split
        · split <;> rfl
        · rfl
        · rfl
    | node expected patterns =>
      simp only [GeneralNominalRecursiveInspection.inspect,visit,replace]
      congr 1
      split
      · split
        · exact many patterns _ _ _
        · rfl
      · rfl
      · rfl
    | nominal expected patterns =>
      simp only [GeneralNominalRecursiveInspection.inspect,visit,replace]
      congr 1
      split
      · split <;> rfl
      · split
        · split
          · rfl
          · split
            · exact many patterns _ _ _
            · split
              · rfl
              · split
                · split
                  · rfl
                  · exact (append state allocated reserved _ _).trans
                      (congr (congrArg Report.append (many patterns _ _ _)) (many patterns _ _ _))
                · rfl
        · rfl
    termination_by sizeOf query
  theorem many (queries : List Query) (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat) :
      report state allocated reserved (inspectMany state queries bounds origins offset) =
        inspectMany (replace state allocated reserved) queries bounds origins offset := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany,report,List.map_nil]
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany,report,List.map_nil]
      | cons bounds tail =>
        simp only [inspectMany,append]
        exact congr (congrArg Report.append (inspect query bounds (origins offset))) (many rest tail origins (offset+1))
    termination_by sizeOf queries
end

theorem bindings (value : Report state) :
    GeneralNominalRecursiveInspection.bindings (replace state allocated reserved) (report state allocated reserved value) =
      GeneralNominalRecursiveInspection.bindings state value := by
  simp only [GeneralNominalRecursiveInspection.bindings,report,List.map_map,Function.comp_def,capture,replace]

theorem selfChecks (value : Report state) :
    GeneralNominalRecursiveInspection.selfChecks (replace state allocated reserved) (report state allocated reserved value) =
      GeneralNominalRecursiveInspection.selfChecks state value := rfl

theorem finished (value : Report state) : Finished (report state allocated reserved value) ↔ Finished value := Iff.rfl

theorem projectionModels (value : Report state) (model) :
    ProjectionModels (replace state allocated reserved) (report state allocated reserved value) model ↔
      ProjectionModels state value model := by
  simp only [ProjectionModels,report,List.forall_mem_map,capture,replace,Fits]

end Yulang.GeneralNominalReportMetadata
