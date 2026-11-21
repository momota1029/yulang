import Yulang.GeneralDeclarativeVisibleRecord326
import Yulang.GeneralDeclarativeGraphRows321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordK2326
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeGraphRows321 (fields shapeOf observed)
open GeneralDeclarativeK2Graph321 (Shape Descends)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row normalize residual)

abbrev empty : Expr := .primitive .emptyRecord []
def row (xs : Row Nat) : Expr :=
  withTail (xs.map (fun entry => (entry.1,.variable entry.2))) empty

/-- The ordinary K2 graph observes the same visible cells as the
canonical first-field projection, independently of output origins. -/
theorem fields_exact (xs : Row Nat) : fields (row xs) = some (normalize xs) := by
  induction xs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨label,payload⟩ := entry
    change fields (.record label (.variable payload) (row rest)) = _
    simp only [fields,ih,Option.map_some,normalize]
    congr 2
    unfold residual
    congr 1
    funext field
    simp [ne_comm]; exact eq_comm

theorem exact_edges {s : State} {xs : Row Nat}
    (stored : (⟨root,row xs⟩ : Equation) ∈ s.equations)
    (payload : labelPair ∈ normalize xs) :
    Descends (observed s) root labelPair.2 := by
  have shape : shapeOf (row xs) = some (.record (normalize xs)) := by
    cases xs with
    | nil =>
      have impossible : labelPair ∈ ([] : Row Nat) := payload
      cases impossible
    | cons field rest =>
      change (fields (row (field::rest))).map Shape.record = _
      simp [fields_exact]
  exact ⟨.record (normalize xs),⟨row xs,stored,shape⟩,List.mem_map.mpr ⟨labelPair,payload,rfl⟩⟩

end Yulang.GeneralDeclarativeRecordK2326
