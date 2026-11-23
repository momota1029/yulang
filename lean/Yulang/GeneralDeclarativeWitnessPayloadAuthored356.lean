import Yulang.GeneralDeclarativeWitnessMixedRecursiveFrontFixture356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPayloadAuthored356
open GeneralDeclarativeWitnessPayloadRoute356 (Route read)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessRecursiveSource356 (AuthorPlan AuthorPlans ParsedPlan ParsedPlans)
open GeneralDeclarativeWitnessRecursiveMixed356 (Plan)
open GeneralDeclarativeWitnessSpineFront355 (Site)
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line printRow exact_list)
open GeneralDeclarativeHead320 (State)

theorem literal_clause_and_binder {s : State} {p : Node s} {i d c b} {q : Route p i d}
    (found : read p i d c b = some q) :
    q.clause.id = c ∧ q.binder = b := by
  unfold GeneralDeclarativeWitnessPayloadRoute356.read at found
  split at found
  · cases found
  · split at found
    · rename_i identified
      split at found
      · split at found
        · cases Option.some.inj found
          exact ⟨identified,rfl⟩
        · cases found
      · cases found
    · cases found

mutual
def rawRows : AuthorPlan → List (List Line)
  | .typed written continuation => written.rows :: allRawRows continuation
  | .payload .. => []
termination_by x => sizeOf x

def allRawRows : AuthorPlans → List (List Line)
  | .nil => []
  | .cons a rest => rawRows a ++ allRawRows rest
termination_by x => sizeOf x
end

mutual
def receivesRows : Plan → List (List Line)
  | .typed a branches => (a.rows.map printRow) :: receivesMany branches
  | .ordinaryPayload .. => []
termination_by x => sizeOf x

def receivesMany : List Plan → List (List Line)
  | [] => []
  | head::tail => receivesRows head ++ receivesMany tail
termination_by x => sizeOf x
end

theorem preserves_literal_recursive_source {cat raw plans} (chosen : ParsedPlans cat raw plans) :
    receivesMany plans = allRawRows raw := by
  refine @ParsedPlans.rec cat
    (fun raw plan _ => receivesRows plan = rawRows raw)
    (fun raw plan _ => receivesMany plan = allRawRows raw)
    ?_ ?_ ?_ ?_ raw plans chosen
  · intro entered body child checked known kids applied
    rw [receivesRows.eq_def,rawRows.eq_def]
    change entered.map printRow :: receivesMany child = checked.rows :: allRawRows body
    rw [exact_list known,applied]
  · intro c b
    rw [receivesRows.eq_def,rawRows.eq_def]
  · rw [receivesMany.eq_def,allRawRows.eq_def]
  · intro first head more tail a rest firstProof secondProof
    rw [receivesMany.eq_def,allRawRows.eq_def]
    change receivesRows head ++ receivesMany tail = rawRows first ++ allRawRows more
    rw [firstProof,secondProof]

theorem all_source_rows_from_owner {p s w} (a : GeneralDeclarativeWitnessRecursiveSource356.Found p s w) :
    a.root.input.rows.map printRow = p.written ∧ receivesMany a.formed = allRawRows p.author :=
  ⟨exact_list a.written,preserves_literal_recursive_source a.authors⟩

end Yulang.GeneralDeclarativeWitnessPayloadAuthored356
