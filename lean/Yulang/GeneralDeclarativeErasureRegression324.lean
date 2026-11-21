import Yulang.GeneralDeclarativeMetadata324
import Yulang.GeneralDeclarativeHiddenWhereProof324
import Yulang.GeneralDeclarativeHiddenResolve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeErasureRegression324
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation raw normal empty normCode normal_compiles)
open GeneralDeclarativeMetadata324 (Same keys normalized_probe normal_meaning)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeDemand320 (sourceValue)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeNFComplete324 (facts produces)
open GeneralDeclarativeHiddenWhere324 (registry parent root child implementation capture row place exact_emission)
open GeneralDeclarativeHiddenWhereProof324 (root_read root_declared root_covered root_stable)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeHiddenState324 (direct)

def withErasedConstructor : Interpretation :=
  ⟨interpretation.primitives,fun n => n == 9, by
    intro n has
    have eq : n = 9 := beq_iff_eq.mp has
    subst n
    rfl⟩

theorem hidden_translation_now_available :
    translate catalogue withErasedConstructor raw =
      some (.record 7 (.variable 0) (.record 7 (.nominal 9 [.variable 40]) empty)) := rfl

theorem same_after_erasure :
    Same catalogue catalogue interpretation withErasedConstructor (keys (normalize raw)) := by
  intro n mentioned
  change n ∈ [4] at mentioned
  cases List.mem_singleton.mp mentioned
  exact ⟨rfl,rfl,rfl⟩

theorem approved_observation_unchanged :
    Matches s catalogue interpretation arg raw ↔ Matches s catalogue withErasedConstructor arg raw :=
  normalized_probe same_after_erasure

theorem approved_head_value_unchanged (cap : Nat → GeneralDeclarativeWhere319.Capture) (m : Assignment) :
    sourceValue catalogue interpretation cap m raw = sourceValue catalogue withErasedConstructor cap m raw :=
  normal_meaning same_after_erasure normal_compiles

theorem whole_normal_batch :
    facts registry interpretation capture.input parent root [child] =
      some [⟨0,direct⟩,⟨3,.variable 3⟩,⟨3,.variable 3⟩,⟨3,.variable 3⟩,row,⟨6,.variable 3⟩] := rfl

theorem whole_batch_entailed :
    Result GeneralDeclarativeHiddenWhere324.state (facts registry interpretation capture.input parent root [child]) := by
  rw [← exact_emission]
  exact produces GeneralDeclarativeHiddenWhere324.checked List.mem_cons_self rfl root_declared
    root_covered root_read root_stable

end Yulang.GeneralDeclarativeErasureRegression324
