import Yulang.GeneralDeclarativeI65I75ProjectedCoreOutput425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65
namespace OutputBranch425
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body)
open CommonNominalFullCarrier (Ty)

/-- Candidate event output type below C402. Both alternatives are
indexed by the actual declaration and output address. Only the legacy
alternative carries a named frame, so a projected tail need not
pretend to have a named capture. This does not redefine I72.Event. -/
inductive ActualOutput {s : State} (atlas : B6OccurrenceAtlas401 s) (q : Request)
    (i : Fin q.demand.outputs.length) : GeneralDeclarations.Declaration → Nat → Type where
  | named (f : AuthoredBodyFrame393 s q) (out : NamedMixedOutput401 atlas f i) :
      ActualOutput atlas q i f.decl f.ordinal
  | projected (out : ProjectedCore425.Output s atlas q i) :
      ActualOutput atlas q i out.row out.ordinal

def ActualOutput.body {s atlas q i row ordinal} (o : ActualOutput (s := s) atlas q i row ordinal) :
    Body :=
  match o with
  | .named _ old => old.body
  | .projected actual => .explicit actual.assoc

def ActualOutput.plan {s atlas q i row ordinal}
    (o : ActualOutput (s := s) atlas q i row ordinal) :
    B6MixedRhs401 s false (normalize (bodyPattern o.body)) :=
  match o with
  | .named _ old => old.plan
  | .projected actual => actual.plan

/-- Both branches read the actual exact atlas entry; a projected
branch cannot replace an original B6 plan with a denotational alias. -/
theorem original_atlas_body_and_typed_term_in_both_branches425
    {s atlas q i row ordinal} (o : ActualOutput (s := s) atlas q i row ordinal) :
    atlas.read q ordinal i o.body = some o.plan := by
  cases o with
  | named f old => exact old.originalTyped
  | projected actual => exact actual.atAtlas

/-- No generic serial form is chosen here. This is semantic output
evaluation, not equality of a legacy and a projected source receipt. -/
def ActualOutput.valueAt {s atlas q i row ordinal}
    (o : ActualOutput (s := s) atlas q i row ordinal) (m : Model) :
    Option (List Nat × Nat × Nat × Nat × Ty) :=
  match o with
  | .named f old => (old.receipt.actualEquation m).map fun (target,v) =>
      (q.occurrence,f.ordinal,i.val,target,v)
  | .projected actual => actual.valueAt m

theorem named_branch_is_the_exact_legacy_model_write425
    {s atlas q i} (f : AuthoredBodyFrame393 s q)
    (old : NamedMixedOutput401 atlas f i) (m : Model) :
    ∃ v : Ty,
      (ActualOutput.named f old).valueAt m =
        some (q.occurrence,f.ordinal,i.val,q.demand.outputs[i].target,v) ∧
      evaluateMixedRhs401 (sourceRead401 m (f.slots old.body)) old.plan = some v := by
  obtain ⟨v,original,literal⟩ := named_mixed_output_is_fixed_equation401 old m
  exact ⟨v,by simp [ActualOutput.valueAt,original],literal⟩

theorem projected_branch_uses_only_actual_interval_observation425
    {s atlas q i} (out : ProjectedCore425.Output s atlas q i) (m : Model) (fit : Fits s m) :
    EndpointHead423.Meaning out.head m ∧
    ∃ v : Ty,
      GeneralDeclarativeRecordChannel330.project out.label false [] (m.assignment out.arg.center).1 =
        some v ∧
      (ActualOutput.projected out).valueAt m =
        some (q.occurrence,out.ordinal,i.val,q.demand.outputs[i].target,v) :=
  ProjectedCore425.projected_core_original_B6_uses_actual_required_field425 out m fit

end OutputBranch425
end Yulang.GeneralDeclarativeI65
