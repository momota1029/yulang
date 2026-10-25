# Higher-order research core and structural embedding

Status: Draft research construction; checking and review evidence is recorded in
the sprint outcome and its frozen receipts. This is not production authority.
Scope: frozen LEAN-HIGHER-ORDER-PROOF-CORE-20261025/r1 research representation.
Initial author: /root/higher_order_proof_core_astra_r1; requested gpt-6-astra/medium,
observed model/effort UNKNOWN. Primary /root repairs and integrates after author
STOP; the outcome records final authorship and independent review. No descendants.
Production authority: none. The operational paper is a proposal/target; the
2026-10-07 complete-Call definition §1 records permission for legitimate research
definitions, not adoption of this representation as compiler architecture.

The parent RESPONSE-ENCODING-1 / ENV-CALLABLE-1 lacked a callable constructor in
its formal Value sort. The candidate removes that specific representational
obstruction by constructing a new callable type and actual lambda/wrap values.
Every Original.Val/Comp and TypedCall.Value/Comp/Adapter/Function constructor is
mapped structurally. No old term is retained behind an opaque original opcode.
The full parent, native readback and operational safety remain OPEN.

## Syntax and quantifiers

`HigherOrderSyntax.lean` retains every old type constructor, all eight literal
domains and their exact payload representations, variables, delay, injections,
single-child intersection/top values and all seven Original computations. It
adds the existing Call view/scope/expose/request/fail nodes, lambda/wrap values,
and dynamicCall. Request's continuation binds its operation instance's response
type. The type language can place callable types beneath thunk/union/intersection
and in operation instances. The value, computation and adapter syntax is mutually
inductive; all typing judgments are defined afterwards.

Value-entry lambda binds A; computation-entry lambda binds Thunk A. Both retain
receipt, annotated input/body/result types, body and result consumer. Wrap keeps
the input adapter c→a and output adapter b→d around an a→b function. DynamicCall
accepts a thunk carrier. This fixes a research typing interface without asserting
an execution rule or operational equivalence for the new constructor.

`ContextEmbedding old new` quantifies over every old lookup fact. The mutual
Original and TypedCall preservation proofs quantify over arbitrary old terms,
old typing derivations and target contexts satisfying that relation. Closed
Original nodes embed under any target context using the empty lookup relation;
binders use `extend_embedding`. The Function theorem quantifies over every old
FunctionTyped derivation and every target context. No original constructor,
source-domain restriction or independent continuation quantifier is discarded.
This is one-way typing preservation, not reflection or full conservativity.

## Metadata boundary

Paths retain component lists, port kinds and translated endpoint types;
occurrences retain identities and paths. Operation instances retain operation
identity, ordered type arguments and both payload/response types. Receipt slots
and profiles retain order, identity and typed paths. Adapter metadata retains
all path correspondences and captured occurrences. Interface-port metadata also
has a structural map.

PathRule is a Prop in the accepted input. `embedPathRule` translates its proof
into a new Prop proof. It does not eliminate that proof into a data-valued map
identity. In particular the old permissive adapterMap rule remains permissive;
this work cannot prove that a mappingIdentity absent from runtime data can be
reconstructed. Syntax is **typing-proof-free**, not entirely proof-free. The old
Adapter.typed field is omitted from syntax and consumed solely to construct the
new extrinsic AdapterTyped derivation. The retained PathRule metadata neither
contains a typing judgment nor creates a typing-definition cycle.

## Parent application

`embedFunction_typed` constructs a ValueTyped callable from an old FunctionTyped
proof. `function_as_argument` and `call_with_function_argument` use it in the
actual new delayed argument and dynamicCall constructors.
`request_callable_response` constructs a request that binds and returns a
callable-typed response. `function_cell` pushes the embedded function into the
existing generic NativeClosureEnvironment.Store, proves the actual current cell
equality and supplies its callable typing derivation.

`read_embedding` preserves the exact old selected cell address while mapping the
current store pointwise. `read_embedding_typed` combines that equation with the
accepted `successful_read_typed` theorem. `captured_value_typed` applies the
accepted `realized_substitution_typed` supplier to each represented context index;
`captured_body_typed` applies its actual successful capture and closed-body
construction before embedding. Both keep successful realization and CellsTyped
as explicit original premises. Nothing claims that arbitrary native closures
already satisfy those premises, or that old stores already represent new
callable values. Generic new callable storage and old represented-read transport
are two separate constructions whose native connection is still open.

## Remaining source obligations and reuse

Accepted CoreSyntax typing and CallEnvironmentRealization supply precisely their
existing domains. CoreSubstitution's bind/request lifting is reused through
close_body, without reproving lookup or assuming a new substitution rule. The
NativeClosureEnvironment.Store remains generic; no machine fields change.
Historical literal readback is not extended to callable readback by analogy.
No failure is dismissed by a narrower theorem; no new source restriction,
Simple-sub bypass or production implementation is introduced.

Luna/source intake owns ENV-LAYOUT-1 (resolved free-variable order and binder
indices from source Lambda/Name/Apply), ENV-CELL-VALUE-1 (current native Value
encoding), ENV-GRAPH-1 (recursive cell/closure graphs), ENV-CALLABLE-1's remaining
native body/consumer mapping, and ENV-DISPATCH-1. Relevant native owners remain
machine.rs `Instruction::Lambda`, `Frame::ValueEntry`, `Machine::lookup`,
`Machine::extend`, closure/Callee branches and receiving.rs lambda schema
construction. The primary's disjoint source map gives their complete exact
producer/consumer inventory, including unit/record/default entry cases.
Force, native transitions, new-core substitution/progress/preservation,
whole-trace safety, operation authenticity and original inference A/B remain
OPEN. No F1/FK1 or foreign-continuation theorem is claimed here.

## Intake and checks

No Lean/build/tests/native checks were run by the author. A shell `python`
invocation failed because the executable was absent; the generation was then
performed with python3. This was a file-writing failure before any write, not a
failed proof check. Primary owns bounded elaboration, public signature/axiom
inspection, distinguishing examples, repairs after author STOP and fresh
independent review. Author/coauthor cannot independently certify this candidate.
Only the four exact leased files were created; there are no scratch paths,
background processes, descendants, compiler changes or Git operations.
