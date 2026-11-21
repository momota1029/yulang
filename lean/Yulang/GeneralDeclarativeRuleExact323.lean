import Yulang.GeneralDeclarativeAssocModel323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRuleExact323
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeAssocRule323 (SourceEquation compiler_is_ordinary)
open GeneralDeclarativeOutputSource323 (Declared declared_rows)
open GeneralDeclarativeRigidLocal323 (RootClosed)
open GeneralDeclarativeOutputExact323 (root_exact)
open GeneralDeclarativeAssocModel323 (actual_output)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- A stabilized ordinary state may retain the normalized equations
literally or entail them by other ordinary facts. For the actual chosen
capture, this weak semantic formulation is exactly root compiler closure. -/
theorem exact {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role)
    (declared : Declared r d) :
    RootClosed s r interp d impl capture ↔
      ∀ row, SourceEquation r interp d impl capture row → Entails s row := by
  constructor
  · intro closed row source m valid
    obtain ⟨out,requested,body,chosen,nf,spelled,rfl⟩ := source
    obtain ⟨emitted,found⟩ := declared_rows (capture := capture) checked cover visible role declared out requested
    have outMeaning := (root_exact checked visible found m).mpr
      (closed out requested emitted found m valid)
    exact (actual_output checked visible chosen spelled m).mpr outMeaning
  · intro source out requested row emitted
    exact compiler_is_ordinary checked cover visible requested emitted source

end Yulang.GeneralDeclarativeRuleExact323
