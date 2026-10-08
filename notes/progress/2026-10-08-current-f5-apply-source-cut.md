# Current F5 application-to-source cut

Date: 2026-10-08
Baseline: `4c114d68464d9a71fa5ad5ea1182c937875b6c10`
Branch: `research/simple-sub-intrusion`
Status: bounded read-only production correspondence trace
Claim class: current-path ownership and scoped absence
Authority: none; no implementation or cutover gate closed

## Result

The inspected default HIR-to-solver pipeline does not type expression
application. It retains source Lambda Function endpoints and solves structural
four-port relations. The opt-in shadow Apply candidate emits a structural
callee-to-demand constraint, but its API and recorded unresolved premises do
not establish the selected source Call contract. Neither path retains a
canonical source `VIncl` certificate or a complete-clause action.

This identifies an early production correspondence gap for replacing F5:
ordinary Apply syntax is not admitted into the default solver path, and the
shadow candidate cannot be treated as that admission layer.

## Exact current owners

- `yu-hir::lower_module` uses default lowering. Apply nodes are retained only
  in the opt-in shadow mode; ordinary Apply/Group bodies are categorized as
  errors by collection. The HIR Apply node carries syntax/occurrence and child
  structure, not a Function descriptor or comparison evidence.
- `ConstraintBatch::collect` builds a `LambdaRecipe` from structural
  positions. `InferenceSession::admit_lambda_fact` creates
  `PosFunction(parameter−, Empty−, body_effect+, body_value+)` and admits it
  against the Lambda root. This is source Lambda endpoint formation, not a
  Call rule.
- `TermView` and the Function term arena retain four structural ports.
  `constrain_live_value` decomposes Function/Function comparisons into those
  ports; the pair memo/worklist retain structural replay and diagnostics, not
  semantic clause evidence.
- The feature-gated `shadow-apply-candidate` path retains callee, argument and
  result positions. For Apply it constructs a negative Function demand from
  the argument endpoint, pure effect constants and negative result endpoint,
  then runs the same structural solver. It does not prove that these endpoints
  are the selected source `A_f`, dependent complete `F_c`, or
  `ExecuteCallableImage`.
- The candidate explicitly retains unresolved premises including
  `ApplicationTypingRule`, `CompleteInvocationImage`,
  `WholeArgumentProviderCompatibility`, `SourceTypingAndAdmission`,
  `CompleteFunctionInterpretation` and `QIndependentCallViewFormation`. Its
  private observation cannot be published as `SolvedModule`.
- Production generalization and `ClosedValueScheme` retain structural
  quantified/recursive Function nodes and four ports. They do not retain the
  original source relation or a whole-clause action. Session pair caches and
  worklists are dropped at terminal transfer.

## Selected source contract comparison

The reviewed source Call construction requires a dependent complete `F_c`,
`WF_Dec(F_c)`, `VIncl(A_f,F_c)`, whole-argument provider compatibility,
containment of the complete callable execution image in the computation
endpoint, and a typed-call certificate. The separate RT.2 analysis shows why
ordinary final-model `VIncl` is also insufficient by itself to transport
complete clauses through relative interpretations.

Structural port equality or matching printed endpoints cannot fill those
source-owned premises. The current-path retained structures establish only the
row/endpoint graph and constraint provenance described above; they do not
establish source typing/admission or the required comparison evidence.

## Next correspondence step

Freeze one exact `CandidateRelation::Apply` occurrence and crosswalk its
callee/demand/result terms to the source constructor's `A_f`, `F_c`, `E_c`, and
`A_c`, using actual operand occurrences and allocation ownership. Mark each
field's producer, scope and lifetime, and name the first missing authentic
supplier. In particular, do not infer a complete `F_c` or `VIncl` action from
structural solving. Use this crosswalk to identify the earliest source-owned
output absent from the candidate before proposing retained representation.

## Scope and omissions

Inspected: default and shadow HIR entrypoints, Apply lowering, ordinary
collection/body status, Lambda recipe/admission, structural term comparison,
candidate Apply formation/admission, F5 generalization/export and closed
scheme reconstruction/terminal transfer, plus the selected source Call and
RT.2 records.

Not established: a full backend/runtime audit; every annotation/import/State
path; a source comparison construction; production conformance; natural
inference completeness; principality; or F5 cutover readiness. No edits to
compiler code, tests, builds, executable probes or performance measurements
were made.
