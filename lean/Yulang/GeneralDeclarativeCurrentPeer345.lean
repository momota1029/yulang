import Yulang.GeneralDeclarativeCurrentSnapshot345
import Yulang.GeneralLatePeerRecursive311
import Yulang.GeneralLatePeerJoint311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeCurrentPeer345
open GeneralDeclarationExamples (roles)
open GeneralLatePeerSource311 (registry root compiled)
open GeneralLatePeerRoot311 (direct z direct_output)
open GeneralLatePeerRouteInstall311 (emitted)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerMerge311 (final alias reached raw_sites identity_before child_new)
open GeneralLatePeerFinalPeerPlan311 (plan named_requests)
open GeneralDeclarativeCurrentOrder345 (Row rows exact_row)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenteredHeadMatStepRoles (Origin)
open GeneralNominalCenteredHeadMatEffects (Ready compileBody)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralNominalSaturationState (Alias)

abbrev row : Row := ⟨1,0,⟨1,z⟩⟩

theorem before_no_row : row ∉ rows emitted.core child.occurrence := by
  intro member
  obtain ⟨site,position,_,related⟩ := exact_row.mp member
  change emitted.core.erased.current.sites[1]? = some site at position
  rw [raw_sites] at position
  have same : direct.observed = site := Option.some.inj position
  subst site
  exact child_new (identity_before related)

theorem after_row : row ∈ rows final.core child.occurrence := by
  apply exact_row.mpr
  refine ⟨direct.observed,?_,?_,alias⟩
  · change emitted.core.erased.current.sites[1]? = some direct.observed
    rw [raw_sites]; rfl
  · change direct.occurrence.demand.outputs[0]? = some ⟨1,z⟩
    rw [direct_output]; rfl

theorem ready_with_peer :
    child.occurrence.demand.outputs = [] ∧
    RequestsDeclared final.core child.occurrence plan ∧ Ready final.core child.occurrence plan ∧
    ∃ (body : GeneralDictionaryAssociatedProvenance.Body) (code : GeneralNominalCenteredHeadMatExpressions.Expr),
      Origin compiled final.core.erased.source.state.seed root direct.occurrence ∧
      GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration 1 = some body ∧
      compileBody plan body = some code := by
  obtain ⟨declared,ready,receipt⟩ := GeneralDeclarativeCurrentSnapshot345.from_reached_frame
    ⟨rfl,GeneralLatePeerSource311.checked⟩ reached GeneralLatePeerCurrent311.frame
  obtain ⟨site,body,code,position,_,_,author,found,done⟩ := receipt row after_row
  change emitted.core.erased.current.sites[1]? = some site at position
  rw [raw_sites] at position
  have same : direct.observed = site := Option.some.inj position
  subst site
  exact ⟨named_requests,declared,ready,body,code,author,found,done⟩

end Yulang.GeneralDeclarativeCurrentPeer345
