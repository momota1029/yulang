import Yulang.GeneralDeclarativeI65I74CompletedLowerRetained437
import Yulang.GeneralDeclarativeI65I72CompletedUnaryGate406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedSeed437

open GeneralDeclarativeI65
open GeneralDeclarativeI65.CompletedLower437
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonRoleOutermostResolver (Dictionary Tree Summarizes)

/-- After reading original B6 provenance, test one actual retained row.
The lower payload has no selected-trace dependency. -/
structure ReadRow {s q atlas frame i}
    (out : NamedMixedOutput401 (s := s) (q := q) atlas frame i) where
  payload : Payload q.demand.outputs[i].target out.receipt
  code : fixedValueCode403 out.rhs = some payload.code

def readRow {s q atlas frame i}
    (out : NamedMixedOutput401 (s := s) (q := q) atlas frame i) (ordinal : Nat) :
    Option (ReadRow out) :=
  match encoded : fixedValueCode403 out.rhs with
  | none => none
  | some code =>
    if valid : s.current.ordinary.equations[ordinal]? = some (⟨q.demand.outputs[i].target,code⟩ : Equation) then
      some ⟨⟨rfl,code,ordinal,valid⟩,encoded⟩
    else none

theorem checked_row_has_exact_ordinal437 {s q atlas frame i}
    {out : NamedMixedOutput401 (s := s) (q := q) atlas frame i} {j : Nat} {r : ReadRow out}
    (checked : readRow out j = some r) : r.payload.rowOrdinal = j := by
  unfold readRow at checked
  split at checked
  · cases checked
  · split at checked
    · cases Option.some.inj checked
      rfl
    · cases checked

/-- Independent source data at the actual one visible declaration.
No output verdict, report or model resides in this source packet. -/
structure SeedBasis (s : I72.State) (q : I72.Request) (row : Declaration) where
  test : AuthoredUnaryChoice405 s q row
  capture : UnaryActualPayload405 test
  safe : ¬ RootCycle s q
  originalOrdinal : Nat
  ordinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 = some originalOrdinal
  inRegistry : (authoredRegistry s.core.current).declarations[originalOrdinal]? = some row
  noWhere : row.requirements = []

private theorem pickedAtZero {s : GeneralDeclarativeI65.State} {q : I72.Request}
    {row : Declaration} {rows : List Declaration} (shape : rows = [row])
    (picked : AuthoredCandidate s q row) :
    StoredAt395 (shape.symm ▸ CandidateTape.next (.matched picked) .nil) picked 0 := by
  cases shape
  exact .here picked .nil

def SeedBasis.origin {s q row} (x : SeedBasis s q row) :
    SelectedHeadOrigin395 (row := row) (authoredNativeTape405 x.test x.capture) :=
  let picked := authoredNativeCandidate405 x.test x.capture
  ⟨picked,0,x.originalOrdinal,pickedAtZero x.test.visibleOnly picked,x.ordinal,x.inRegistry⟩

def SeedBasis.frame {s q row} (x : SeedBasis s q row) : AuthoredBodyFrame393 s.core q :=
  preoutputFrameOfOrigin399 x.origin unusedPlacement403 (fun _ => emptyCapture403)

def SeedOutputs {s q row} (x : SeedBasis s q row) :=
  ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 x.frame i

def chosenEvent {s q row} (x : SeedBasis s q row) (out : SeedOutputs x) : Event s q :=
  ⟨x.frame,x.origin.pick.head,out⟩

theorem chosen_event_has_no_where437 {s q row} (x : SeedBasis s q row) (out : SeedOutputs x) :
    (chosenEvent x out).kids = [] := by
  simp [chosenEvent,Event.kids,SeedBasis.frame,preoutputFrameOfOrigin399,frameAtSource395,
    frameWhereKids400,AuthoredBodyFrame393.clauses,x.noWhere,children]

/-- The exact selected trace is data, not an existential extracted by
choice. Retention witnesses are read independently at every original
output, and the request/event/dictionary indices stay literal. -/
def chosenTrace {s q row} (x : SeedBasis s q row) (out : SeedOutputs x)
    (retained : ∀ i, ReadRow (out i)) :
    SourceTrace PriorSource406 s q (.selected row.id []) (some (chosenEvent x out)) := by
  let actual : AuthoredNativeSelected405 (chosenEvent x out) :=
    ⟨x.test,x.capture,x.origin,rfl,rfl⟩
  have allKept : RetainedTypedValueRows403 (chosenEvent x out) := by
    intro i
    let kept := retained i
    exact ⟨kept.payload.code,kept.code,List.mem_of_getElem? kept.payload.row⟩
  exact .selected (chosenEvent x out) x.safe (.inr ⟨rfl,⟨actual⟩,.inr allKept⟩) .nil
    ((chosen_event_has_no_where437 x out).symm ▸ .nil)

def seedDictionary (row : Declaration) : Dictionary := .node row.id []

theorem seedSummarizes (row : Declaration) : Summarizes (.selected row.id []) (.selected (seedDictionary row)) :=
  .selected .nil (.selected rfl)

def exactNeed {s q row} (x : SeedBasis s q row) (out : SeedOutputs x)
    (i : Fin q.demand.outputs.length) : OutputNeed s :=
  needOfSelected404 (chosenEvent x out) (seedDictionary row) i

def exactSupport {s q row} (x : SeedBasis s q row) (out : SeedOutputs x)
    (retained : ∀ i, ReadRow (out i)) (i : Fin q.demand.outputs.length) :
    SupportForest PriorSource406 s [exactNeed x out i] :=
  .cons (chosenTrace x out retained) (seedSummarizes row) rfl .nil

theorem exact_support_preserves_one_model437 {s q row} (x : SeedBasis s q row) (out : SeedOutputs x)
    (retained : ∀ i, ReadRow (out i)) (i : Fin q.demand.outputs.length)
    (m : I72.Model) (fits : I72.Fits s m) :
    DictionaryEvidence s m q (seedDictionary row) ∧ (retained i).payload.Means m := by
  obtain ⟨_,_,source⟩ :=
    authored_native_dictionary_reuses_given_trace405 (chosenTrace x out retained) (seedSummarizes row)
  exact ⟨source m fits,
    retained_literal_typed_output_means_same_lower437 (retained i).payload (retained i).code m fits⟩

/-- The scoped executable output reader for an original one-output
request. The supplied locator is checked against the actual source
receipt, not against an asserted expected dictionary. -/
structure OneOutput {s q row} {x : SeedBasis s q row} (out : SeedOutputs x) where
  i : Fin q.demand.outputs.length
  sole : ∀ j : Fin q.demand.outputs.length, j = i
  kept : ReadRow (out i)

def OneOutput.values {s q row} {x : SeedBasis s q row} {out : SeedOutputs x}
    (p : OneOutput out) : ∀ j, ReadRow (out j) :=
  fun j => (p.sole j).symm ▸ p.kept

def OneOutput.support {s q row} {x : SeedBasis s q row} {out : SeedOutputs x}
    (p : OneOutput out) : SupportForest PriorSource406 s [exactNeed x out p.i] :=
  exactSupport x out p.values p.i

def readOneOutput {s q row} {x : SeedBasis s q row} (out : SeedOutputs x)
    (sole : q.demand.outputs.length = 1) (rowOrdinal : Nat) : Option (OneOutput out) := do
  let i : Fin q.demand.outputs.length := ⟨0,by rw [sole]; decide⟩
  let verified ← readRow (out i) rowOrdinal
  have only (j : Fin q.demand.outputs.length) : j = i := by
    have size : j.val < 1 := Nat.lt_of_lt_of_le j.isLt (Nat.le_of_eq sole)
    apply Fin.eq_of_val_eq
    change j.val = 0
    omega
  return ⟨i,only,verified⟩

end Yulang.GeneralDeclarativeI65.I72.CompletedSeed437
