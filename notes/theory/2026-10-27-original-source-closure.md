# Original Lambda body: EventProof ownership and checked consumer

Date: 2026-10-27. Baseline: `6148fc868565617d7db6ef193a6ff164700d88f7`,
branch `yulang3`. Producer: `/root/soundness_hygiene`, bounded Lean leaf.
Implementation: `lean/YulangClosure/OriginalSourceClosure.lean`.

The original parent is full Yulang inference soundness and Effect hygiene.
This construction closes the local declaration-preservation and finite body
consumer step under the actual original Lambda Build. It does not establish
the complete original source-membership theorem, recursive L4, every primitive
interpretation, or native solver success. No compiler or existing semantic
module is modified.

## Original source rule and first missing step

Source Generalize §3.3 in
`2026-10-08-source-generalize-definition-and-proof.md` distinguishes:

- the Parameter's Desc at its complete pre-invocation typing telescope;
- actual EventField/OneShot runtime and installed Shared data;
- description-owned EventProof evidence inside the actual body event.

Its §3.2(3–4) requires actual finite same-computation or Function checking;
the semantic inclusions are conclusions of those finite constructors.
The original source builder's Lambda rule emits its body EventProof
existential immediately above the original body consumer check and body
derivation. `OriginalFormalShared.checkedBody` calculates that exact tree.

The adopted `OriginalFormalAdmission` already selects the formal contract
from the actual prior telescope and preserves it through invocation, receipt,
Return where applicable, and Shared. It deliberately leaves EventProof
admission unchanged. The raw `Logical` carrier can otherwise contain arbitrary
descriptor/interface writes. Consequently that earlier theorem alone does not
preserve the selected formal across the body's proof frame.

The new module supplies the actual permitted EventProof packet and applies
the existing finite Checking soundness theorem to the generated body check.
It assumes neither a desired final formal-readback equation nor a body
computation-inclusion law.

## Constructor and coverage boundaries

`EventProofPacket` is indexed by an original `Owner`. It contains the complete
independently chosen view interpretation, assignment and current logical
witness. Its encoder has no Desc or interface writes. Actual body-local Desc
introductions remain the body's separate original source constructors; the
proof packet does not erase or replace those source constructors.

`proofAdmissions` retains the old independent logical predicate and recognizes
this field ownership at `.eventProof`. It is a constructed local admission
instance, not a proof that every arbitrary pre-existing opaque
`LocalAdmissions.logical` already obeys this ownership. A source/native use
must use the original proof-field constructor, or identify its own original
catalogue with it. `proof_packet_admission_exact` proves completeness for every
packet of this constructor: all independent old predicate checks and all
choices of the permitted fields remain.

`other_logical_admission_unchanged` covers every other logical kind.
`runtime_admission_unchanged` and `checking_runtime_admission_unchanged` cover
all six original Runtime constructors, including invocation, receipt,
Return/rebind, response, rigid operation and one-shot. No checked challenge,
provider, pending observation or actual future history is filtered by these
new proof-field rules. Shared admission is unchanged by definition.

`closureKernel` installs the source admission and goal-indexed checking
admission before the registered finite Checking kernel. Its Function
constructors therefore capture the actual final checking admission, avoiding
a stale record-update closure. `closure_kernel_is_local` proves that the
earlier local source constructor can be reapplied without changing this
final kernel; both complete Build consumers use that equation definitionally.

## Actual owner, telescope and decoder

`body_proof_owner_registered` locates the EventProof in the original computed
`checkedBody`, at its second sequence child. `actual_lambda_body_owner`
locates the same owner in the whole raw Lambda source traversal for both
entry modes. `scoped_body_owner_registered` additionally retains the actual
enclosing route and complete ambient scope. The input source pattern and body
remain arbitrary; repeated Site values require no uniqueness premise.
`body_owner_keeps_ambient` records every prior dependency explicitly.

These owners are those of the Lambda child selected by the source rule.
An outer source annotation retains its separate boundary obligations, as in
the existing `annotation_child` construction; neither that annotation nor the
formal's own annotation is removed from the input Build.

`admitted_proof_packet` inverts the original heterogeneous admission and
constructs the raw packet. It does not infer a field class from a solved
descriptor or semantic membership. `proof_packet_preserves` then calculates
the real decoder's behavior. It retains:

- all descriptors and interfaces, installed certificates and binding addresses;
- actual endpoint values and roots;
- the original static fiber and eta0;
- current runtime history/configuration, scope, authority, incidence and dictionary;
- the complete fixed-frame prefix, source callable owners and active raw call.

`proof_packet_uses_current_evidence` separately exposes the permitted new
eta, logical witness and view interpretation. These are not frozen to the
closure-creation values. `body_proof_keeps_actual_identity` proves that the
actual environment extension retains its event path, anchors, publications,
origin and replay state. Thus changing a body proof cannot create a new
actual event or replace its installed evidence.

## Application to the original generated body

`checked_body_consumer` consumes an actual `Judgment` for the calculated
original `checkedBody`, with one already decoded predecessor. It inverts the
real sequence and EventProof existential, and returns the same packet and
extended environment for all of:

1. the original pattern source judgment;
2. the original finite `Checking` proof from `body.finalRoot` to
   `lambda.bodyConsumer` in computation mode;
3. the arbitrary original body source judgment;
4. preservation of the selected formal contract through the proof frame;
5. the semantic computation action for every complete raw observation.

The fifth conclusion is obtained from `OriginalSourceChecking.checking_sound`
and `computation_action`, including the finite check's recursive children.
The statement does not take an assumed body-inclusion certificate. It uses
completed `Meaning`, and makes no invalid extension of ordinary finite
checking to an arbitrary provisional recursive candidate.

The two main public roots apply this construction back to the actual original
Build, rather than stopping at a conditional body helper:

| Theorem | Inputs and conclusion |
| --- | --- |
| `generated_value_body_consumer` | Original Introduction, FormalAssignment, Inputs/primitive registry/readouts, complete Prior, optional annotation, Value entry, and satisfaction of the actual Lambda Build. It constructs the actual Desc/View and, for every independently admitted invocation, its receipt. Every independently admitted Return reaches the original Shared/body scope and yields `BodyConsumer`. |
| `generated_computation_body_consumer` | The same original input data, Computation entry, and actual Lambda Build satisfaction. Every admitted invocation and its receipt reach the original retained Shared/body scope and yield `BodyConsumer`, without introducing an argument Force or Value Return. |

`BodyConsumer` is only the output property. It contains the decoded source
environment, actual EventProof payload, selected pre-invocation formal
contract, both source subjudgments, the finite original computation check,
and its derived semantic action. It occurs in no Kernel field or admission
predicate. Neither root accepts an entry/body derivation, chosen contract,
EventProof packet, final descriptor equality or body-soundness law as input.

## Parent application and remaining owners

This discharges the original local step from source-selected formal declaration
through the body EventProof to the actual finite body consumer. It gives the
soundness induction a computation action at the exact retained original
source environment, together with the unmodified selected formal contract.

The first remaining source-membership premise is independent membership of
the body's actual input/result trace or installed formal at that contract.
The computation action transports such membership; it does not create it
from the existence of a source judgment. Its owners are the actual primitive
and source-constructor interpretation, operational Call/Force result incidence,
and joint recursive introduction L4. The concurrent Return/world packet owns
the native/current-world correspondence at the entry boundary.

The existing current-event-only Function domain reading still cannot supply
every later independently admitted domain inclusion; the exact obstruction
and remaining Event/EventField registration are in `OriginalFunctionFuture`.
No generic future-event law is assumed here. Complete guards/captures,
operation/State contracts, all source/native constructor correspondence and
the full same-witness inference solution remain open.

Global route-sensitive formal declaration selection is also unchanged:
the earlier `OriginalFormalAdmission` local instance cannot reconstruct an
arbitrary original occurrence from a flat Binder. The new EventProof field
grammar is owner-uniform, so its preservation proof does not need to make
that false reconstruction. The complete route and ambient telescope are
still retained in its source registration and output packet index.

## Verification and frozen evidence

The direct dependency is the freshly adopted and checked
`OriginalFormalAdmission`, SHA-256
`77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`.
All its original mathematical dependencies remain at the stated baseline.
The new source is frozen at SHA-256
`e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a`.

Actual executable versions are Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. Direct checks use the resolved absolute Lake path,
`env lean -j1 -M1024`, with no `-o` and no worker cache writes.
The final source check exited 0 without errors or warnings; its output is
`/tmp/yulang-soundness-20261027/source-closure-check.log`.

Material construction diagnostics were one rejected existential binder syntax
and one unused simp argument, both fixed before freezing. There was no
mathematical premise strengthening in either repair. Earlier passing partial
checks were followed by the complete final check after both Build consumers,
scoped owner registration and all preserved event fields were present.

The full originating-declaration/type/axiom audit is run separately against
the primary's freshly built frozen artifact. Its final result is recorded
below. Independent review and integration remain primary-owned; no parent
theorem is promoted by successful kernel checking.

### Final originating audit

The primary's fresh build completed successfully. The imported complete audit
then exited 0 with no errors or warnings. It enumerated 73 actual originating
declarations: 43 theorem constants, 27 definitions, one inductive declaration,
one constructor and one recursor. All nineteen authored public theorem roots
were required and found. This includes the private body-application helper
and all declarations generated during elaboration, including equation lemmas
whose names begin with an imported namespace. The executing audit introduced
no declarations of its own.

Every originating declaration's full type and transitive axiom set is in
`/tmp/yulang-soundness-20261027/source-closure-audit.log`, SHA-256
`da8915a4b9e3dc816ccd5835cb05d6f9f5e1053df0283d1a608dcd34d79d42fe`.
The parsed complete census is
`/tmp/yulang-soundness-20261027/source-closure-complete-census.json`, SHA-256
`5e77177bb61b65a061ff363a4769e9b6915ace2d1869c925409164016505d585`.
The actual axiom union is exactly `propext`, `Classical.choice`, and
`Quot.sound`. Both generated Build/body-consumer theorems and
`checked_body_consumer` use all three. `proof_packet_preserves` uses no axioms;
`admitted_proof_packet` uses only `propext`. No project axiom, `sorryAx`,
unchecked native evaluation or kernel bypass appears.

An additional explicit public-root audit prints `#check` and `#print axioms`
for all nineteen new roots and all thirty-five adopted FormalAdmission roots
at `/tmp/yulang-soundness-20261027/public-root-types-axioms.log`. It supplements
the complete originating census; it does not replace it.
