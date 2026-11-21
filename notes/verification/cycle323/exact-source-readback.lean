import Yulang.GeneralDeclarativeProvisionalClosure323
import Yulang.GeneralDeclarativeAssocModel323
import Yulang.GeneralDeclarativePlainFixture323
import Yulang.GeneralDeclarativeRepeatedResolve323
import Yulang.GeneralDeclarativeRecordFixture323

open Yulang

example :
    GeneralDeclarativeEmissionForest322.children GeneralDeclarationExamples.wrap
      GeneralDeclarativeEmissionFixture322.names GeneralDeclarativeEmissionFixture322.place =
      [GeneralDeclarativeExampleSource320.child] := rfl

example :
    GeneralDeclarativeAssocRule323.SourceEquation GeneralDeclarativeExampleSource320.registry
      GeneralDeclarativeExampleSource320.interp GeneralDeclarativeExampleSource320.child
      GeneralDeclarativeExampleSource320.leaf GeneralDeclarativeEmissionFixture322.leafNames.input
      GeneralDeclarativeProvisionalFixture323.row := by
  exact ⟨⟨1,5⟩,List.mem_cons_self,.explicit GeneralDeclarativeExampleSource320.association,
    .explicit _ List.mem_cons_self rfl,.variable 0,rfl,rfl⟩

example :
    GeneralDeclarativeOutputFacts320.rootFact GeneralDeclarativeExampleSource320.registry
      GeneralDeclarativeExampleSource320.interp GeneralDeclarativeExampleSource320.leaf
      GeneralDeclarativeExampleSource320.child GeneralDeclarativeEmissionFixture322.leafNames.input ⟨1,5⟩ =
      some [⟨5,.variable 3⟩] := rfl

example :
    GeneralDeclarativeEmissionForest322.children GeneralDeclarativeRepeatedSource323.parent
      GeneralDeclarativeRepeatedReads323.parentNames GeneralDeclarativeRepeatedReads323.place =
      [⟨0,[⟨3,3,3⟩],[]⟩] := rfl

example :
    GeneralNominalInspection.translate GeneralDeclarativeExampleSource320.registry.constructors
      GeneralDeclarativeExampleSource320.interp
      (GeneralDeclarationPatterns.normalize GeneralDeclarativePlainFixture323.source) =
      .node (.variant 7) [.variables [0,1]] :=
  GeneralDeclarativePlainFixture323.actual_source_lowering

example :
    CommonRoleCanonicalRows.residual [7] GeneralDeclarativeRecordFixture323.fields =
      [(9,.variable 51)] := rfl

example :
    GeneralDeclarativeRecordResidual323.withTail
      (CommonRoleCanonicalRows.residual [7] GeneralDeclarativeRecordFixture323.fields)
      GeneralDeclarativeRecordFixture323.terminal = .record 9 (.variable 51) (.primitive .exactEmpty []) := rfl
