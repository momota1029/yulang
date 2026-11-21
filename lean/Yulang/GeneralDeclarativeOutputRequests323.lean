import Yulang.GeneralDeclarativeOutputSource323
import Yulang.GeneralDeclarativeEmissionErasure322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputRequests323
open GeneralDeclarations (Checked)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeSourceEmission322 (demand)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeBatch320 (collect)
open GeneralNominalCenteredHeadWFSource (Coverage)

theorem child_declared (checked : Checked r) (visible : decl ∈ r.declarations)
    (member : child ∈ children decl names place) : Declared r child := by
  obtain ⟨clause,present,rfl⟩ := List.mem_map.mp member
  have legal := (checked.2 decl visible).signature.2.2.2 clause present
  intro out requested
  rw [GeneralDeclarativeSourceEmission322.outputs_match_source decl clause legal] at requested
  exact (GeneralDeclarationDemands.childDemand decl clause legal names.old
    (GeneralDeclarativeEmissionErasure322.oldPlacement place clause)).declared out requested

/-- When a generated child later has a selected checked declaration,
its existing output request names are already legal by source formation.
No output-target guard needs to be added to local selection. -/
theorem child_rows_generated (checked : Checked r) (cover : Coverage r interp)
    (parent : decl ∈ r.declarations) (member : child ∈ children decl names place)
    (selected : impl ∈ r.declarations) (role : impl.role = child.role) :
    ∃ rows, collect (rootFact r interp impl child capture) child.outputs = some rows :=
  GeneralDeclarativeOutputSource323.generated checked cover selected role
    (child_declared checked parent member)

end Yulang.GeneralDeclarativeOutputRequests323
