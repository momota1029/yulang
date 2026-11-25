import Yulang.GeneralDeclarativeI65I73UnifiedControls408
import Yulang.GeneralDeclarativeWitnessCoverageFixture357
import Yulang.GeneralDeclarativeWitnessCycleFixture350

namespace Yulang.GeneralDeclarativeI65.I72.Check408.Integration
open GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessCoverageFixture357 (prepare)
open GeneralSourceMetadataBareBundle291 (InputBundle)

abbrev C350 := GeneralDeclarativeWitnessCycleFixture350.state

def declaration : Declaration := ⟨88,7,[],[],[],[]⟩

def original (rows : List Declaration) : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨0,[⟨7,0,[]⟩]⟩,rows⟩

def ordinaryLeaf (rows : List Declaration) : Option Problem := do
  let metadata ← prepare (original rows)
  let state : Yulang.GeneralDeclarativeI65.State :=
    ⟨⟨metadata,⟨⟨[],[]⟩,[]⟩,[]⟩,[],[],[]⟩
  let b6 : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,b6⟩,⟨[27],⟨7,[],[]⟩⟩⟩

def leafTest (rows : List Declaration) (r : Result) (w : Witness) : Bool :=
  ((ordinaryLeaf rows).map fun p => check p r w).getD false

theorem actual_source_nullary_integration_passes408 :
    leafTest [declaration] (nullaryReport declaration) .nullary = true := by
  decide +kernel

theorem extra_visible_decl_is_not_silently_dropped408 :
    leafTest [declaration,{declaration with id := 89}] (nullaryReport declaration) .nullary = false := by
  decide +kernel

theorem wrong_dictionary_on_exact_source_refused408 :
    leafTest [declaration] {nullaryReport declaration with verdict := .selected (.node 89 [])}
      .nullary = false := by
  decide +kernel

theorem wrong_diagnostic_on_exact_source_refused408 :
    leafTest [declaration] {nullaryReport declaration with tree := .ambiguous} .nullary = false := by
  decide +kernel

theorem extra_actual_write_is_refused408 :
    leafTest [declaration] {nullaryReport declaration with writes :=
      [⟨[27],0,0,⟨1,3⟩,.explicit ⟨8,1,.var 4⟩,.node 0 [] []⟩]} .nullary = false := by
  decide +kernel

def rawTest (wire : GeneralDeclarativeWitnessCycle350.Wire) (reported : Result) : Bool :=
  ((ordinaryLeaf [declaration]).map fun p =>
    let state := {p.state.core with current := {p.state.core.current with ordinary := C350}}
    let b6 : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
    let root := {p.root with demand := GeneralDeclarativeWitnessCycleFixture350.d}
    check ⟨⟨state,b6⟩,root⟩ reported (.rawRoot wire)).getD false

theorem existing_c350_raw_wire_passes_uniform_entry408 :
    rawTest GeneralDeclarativeWitnessCycleFixture350.certificate rawReport = true := by
  decide +kernel

theorem wrong_raw_closure_is_refused408 :
    rawTest {GeneralDeclarativeWitnessCycleFixture350.certificate with closeAt := .same} rawReport = false := by
  decide +kernel

theorem unhandled_tag_returns_false_not_diagnosis408 :
    leafTest [declaration] (nullaryReport declaration) .unsupported = false := by
  decide +kernel

#print axioms actual_source_nullary_integration_passes408
#print axioms extra_visible_decl_is_not_silently_dropped408
#print axioms wrong_dictionary_on_exact_source_refused408
#print axioms wrong_diagnostic_on_exact_source_refused408
#print axioms extra_actual_write_is_refused408
#print axioms existing_c350_raw_wire_passes_uniform_entry408
#print axioms wrong_raw_closure_is_refused408
#print axioms unhandled_tag_returns_false_not_diagnosis408

end Yulang.GeneralDeclarativeI65.I72.Check408.Integration
