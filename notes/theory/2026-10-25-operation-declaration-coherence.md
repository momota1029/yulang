# Primitive operation declaration coherence and retained response instance

Status: source argument candidate, pending combined Lean/source independent review.
Primary author: `/root`; constructive companion author:
`/root/primitive_operation_instance_astra_r1`. Requested Astra/medium for child,
observed model/effort UNKNOWN. Baseline
`6d9e769abbd6c119bf71c4a2f9bb9202bed064de`, research/simple-sub-intrusion.
Contract: LEAN-PRIMITIVE-OPERATION-INSTANCE-20261025/r1,
SHA `2d885257c3e93748dc2b9b5e42a6bce1a3a5c615be382f561e484b3ea71f7c0a`.
All contract source hashes were checked before use. Additional exact read pin:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |

## Claim, exact successful domain and exclusions

Let P be a successfully source-constructed RuntimeProgram on the public
inference-playground execute/execute_module/execute_module_report path, with its
immutable HIR/source world. Consider an operation declaration whose signature
is a Function with Unit/Int/Bool/Str argument and result values and **None effects
at all three annotation nodes** (root, argument, result). Call this the supported
primitive declaration observation. For all such declarations and all their actual
request creation, capture and accepted primitive response uses:

1. the complete operation identity determines this primitive signature among
   the declarations supplied by this source construction;
2. request, captured template and response consumer retain the exact original
   declaration, hence the same signature and identity;
3. a single finite numbering of the actual program's operation identities covers
   all those uses without collisions, and the corresponding formal instance
   obtains both endpoint types from that one declaration;
4. the expected response base read by the native consumer is the instance's
   response base. This supplies the previous local hinstance premise once the
   formal requesting head is the interpretation of this declaration.

This partial interpreter does not reject or change Yulang. In particular the
native handler checks root/argument effects but can accept a primitive result
with an effect annotation; this argument's successful interpretation deliberately
leaves every effect-bearing annotation (even Some empty row), variable, hole,
tuple, callable endpoint or nonfunction declaration outside its represented
branch. No absence of effects is inferred merely from runtime acceptance.
The full source domain and original A/B parents remain OPEN. General full
signature coherence with context-resolved effect rows is not claimed here.

An arbitrary caller can construct a public SourceOperationDeclaration struct
with reused id and different signature; native id equality alone cannot rule
that out. The claim is over the inspected source producers and their propagation,
not arbitrary hand-built embedding inputs. It is source correspondence reasoning
about these Rust owners, not a Rust semantics proof performed by Lean.

## 1. Identity and deterministic source formation

`module.rs:29–115` defines the complete module identity by realm and normalized
workspace-relative file path, retained as data with Eq. `source_annotation.rs:33–61`
adds the effect-family declaration key and operation-member declaration key.
Names, visibility, offsets alone and hash outputs are not operation identities.
Distinct modules/families/member declarations remain distinct even with identical
spelling; hash tables use Eq after hashing and do not turn a hash collision into
an equality certificate.

`yu-syntax/full_parse.rs:61–124` retains immutable source/green syntax and a parse
brand. SourceNodeKey equality checks the same live Arc parse brand, same retained
green-node allocation and same start. Cloning retains allocations, preventing
allocation-reuse aliasing. Keys are minted only from the owning parse and child
descent. For these nonempty declaration/member nodes, an equal key identifies
the same node of the same immutable parse: disjoint nonempty occurrences have
different starts; a proper ancestor cannot be the same finite acyclic green
allocation as its descendant. This uses the existing immutable Rowan/Arc source
identity contract; it is not a proof of the implementation of those libraries.

`source_identity.rs:33–48::try_source_keys` traverses that parse and maps each
syntax node to its owned key; it does not synthesize keys from spans/spellings.
`module.rs:2304–2316::index_source_effects` and local lowering initialize counters
from that exact map and check file/module consistency. `declarations_selected`
(source_annotation:204–401) is the sole production constructor of operation
records in the searched HIR/runtime sources. It accepts actual Act members,
requires an annotation and a Function signature, and stores the family key,
member key, signature position and parsed signature together in one fresh Arc.
It inserts clones into both the namespace and family operation vector. Selected
projection chooses existing nodes; it never rewrites their signatures.

For the supported branch, parsing is independent of namespace context. In
`parse_type_source:491–600`, int/bool/str are exact token cases; `parse_group:601–630`
returns Unit for an empty parenthesized group and transparent grouping for one
unseparated element. Arrow formation takes its argument and recursively parsed
result from that same syntax. No BracketRow at any represented annotation means
no parse_row call on the successful type tree. There are no variable or hole
branches and no effect-family lookups. Parenthesized groups preserve any effects,
so an effect annotation is not silently lost into the supported branch.

Induction on this finite parse/type tree establishes: two successful formations
of the same member key, even using fresh counters or different selected-family
sets, have the same supported primitive endpoint constructors and absent effects.
If either formation is supported, the same syntax forces the other's successful
formation to be supported with the same endpoints. Thus an id comparison at
request/handler selection supplies the relevant signature equality. This does
not assert that arbitrary effect-bearing declarations have identical resolved
rows under independently supplied namespaces. The supported tree contains no
type/effect variables or holes, so there is no parameter to instantiate; the
formal empty typeArguments vector is justified by this syntax, not native field
absence or an assumed monomorphic instance.

## 2. Resolver and import supply, including separately resolved handlers

Local source operation uses and catch arms share `resolve_operation`
(local_source.rs:2282–2293). It demands exactly one family and exactly one member,
rejects private resolution and returns a clone of the retained declaration.
Ambiguous/unresolved/private alternatives remain explicit. Operation expressions
use that resolver at2060–2071; catch patterns use it at2349. They do not reparse
or independently select types after selecting identity.

Qualified imported uses are handled at local_source:2047–2054 from the retained
ImportedOperation. `module.rs:512–677::selected_member_operation_paths` selects
source effect records by actual export declaration keys/module checks and member
identity; successful cases clone the selected operation Arc. `namespace:3518`
retains that exact operation path record. `source_exports.rs:271–400` stores the
record in a parse/identity-bound environment; id-based dedup/equality does not
itself establish signature coherence, so the producer argument above is required.
Local shadowing or ambiguity can change success/failure or select a different id,
but cannot change the signature associated with one source-produced supported id.

The public source execution route is not supplied arbitrary operation records:
`lib.rs:490–612::prepare_with_world` parses the consumer, constructs identity,
resolves imports, lowers local source, and constructs the candidate/world.
`pinned_source_world:659–691` retains each provider's same ParsedFile with its
export indexes and source identity. Provider projection (`project_selected:816–851`),
member projection (:1027–1042), exact implementation-member projection (:1221–1237)
and applicable-member projection (:1419–1443) obtain every effects vector by
`shadow::index_source_effects` on those retained parses and exact exported Act
keys; that API delegates to the source constructor above. Unsupported families
can be skipped, but no fabricated declaration replaces them. All four production
calls to with_selected_member_operations consume those vectors. The scoped
route uses only the consumer HIR and does not introduce an alternate supplier.

`pinned_candidate_world:1140–1185` combines these projections and follows requested
provider/member dependencies. It may form multiple records from the same parse,
so pointer equality of declaration Arcs is not assumed across HIR projections.
The key/parse determinism proof gives the supported signature equality there.
Imports passed by an arbitrary external API caller are outside this public
source-produced supply argument. No claim of source authentication is derived
from public struct visibility or id-based import equality alone.

`RuntimeProgram` lowering (:954–969) copies Operation resolution and Catch arm
patterns from their LocalSource forms; it does not reconstruct signatures.
`machine::propagate_request:2120–2152` compares the handler-resolved declaration id
with the pending request id, then checks the handler signature/payload. Therefore
for the represented branch the same-id source lemma equates its argument/result
bases with those of the request. Native closed_primitive/local_grant, installation,
payload/view and continuation-pattern conditions remain separate conditions;
this argument neither assumes nor proves the global hygiene/eligibility gate.

## 3. Retention from execution to response

Every declaration-bearing transition in this slice preserves the same record:

| Transition owner | Preserved data / exact action |
| --- | --- |
| program:954–955, machine:939–963 | LocalSource Operation resolution is cloned to immutable code, then to RuntimeValueKind::Operation. |
| machine:1337–1418 | Callee takes the Resolved declaration and clones it; reads its Function/root effects; chooses Value/Computation payload entry. |
| machine:1137–1140 | OperationPayload moves the declaration with the evaluated payload into make_request_carrier. |
| machine:2361–2378 | make_request_carrier stores that declaration in ExecutableValue::Request. |
| machine:2560–2583 | execute_with_substitution clones the executable, changes payload dispatch only and moves the declaration into PendingRequest. |
| machine:2100–2321 | Unwind/forward extends suffix or leaves owners; no declaration rewrite. Selected handler calls capture_template on the original request, not its separately resolved handler declaration. |
| machine:1841–1911 | capture_template builds nodes, then appends ResumeTemplate with request.declaration.clone(); failure publishes no partial template. |
| continuation:12–22 | ResumeTemplate stores the Arc declaration beside root/nodes/original event. |
| machine:1211 and1033–1076 | Continuation execution retains its template handle in ResumeArgument; return reads this template's declaration.signature Function result and applies primitive_matches or the separate callable branch. |

The private resume_templates vector starts empty and its sole production append
is capture_template. Searches find no mutation of an existing template declaration,
no make_mut, no assignment to a signature, and no alternate runtime operation
record constructor. Numeric handles are validated before access; they index an
append-only arena, so they do not retarget an old template after another capture.
Entering a template recreates frames/owners/views but keeps its declaration.
Nested resume frames carry validated handles, not reconstructed operation names.
Repeated internal resume reads the same retained immutable declaration each time.
This is declaration preservation only, not a claim that all recreated owners,
views, environments or complete frame behavior already simulate the formal model.

Unhandled source requests capture only for the authenticated host operation
(machine:2325–2340). resume_host_write:599–651 checks stopped continuation/operation,
program capability, unused continuation and the retained template declaration;
program:531–537 checks exact id plus str->unit signature. It allocates Unit itself.
This is consistent with the same supported interpretation; it introduces neither
a new operation declaration nor arbitrary external value injection. The broader
typed external-response protocol in the original theorem remains allowed/open.

## 4. Finite shared numbering and source coverage

For a fixed successfully constructed P, choose I by traversing finite P.code in
index order, collecting each resolved Instruction::Operation identity and each
resolved operation-pattern identity in each finite Instruction::Catch arm list.
Keep duplicates; their order is immaterial to semantics but the chosen I stays
fixed for the whole interpretation. This is a mathematical construction over an
existing finite immutable program, not a proposed runtime registry or an assumed
injective hash. Use the complete native Eq identity as the formal key type.

The first-index construction in the companion Lean module provides member
coverage and proves that two successful lookups at the same number have the same
key, without any Nodup assumption. Equal keys have the same lookup by function
congruence, including repeated occurrences and independently cloned declarations.
Distinct module/family/member identities cannot collide in one fixed I. The
number is scoped to P/I; numbers from different programs/tables are not compared.

Coverage follows by induction on the inspected native value/request lifecycle.
Initially no RuntimeValue exists. The only production RuntimeValueKind::Operation
constructor is the code Operation case at machine:963, whose id is in I by
construction. All other value producers create nonoperation kinds; copying
handles, records, closure environments or generic tuple/variant data adds no
new operation identity. A request takes a declaration only from such an operation
value; forwarding/capture/resume preserve it by section3. Handler resolutions
come from copied code arm patterns and are included directly. The immutable code
arena is populated before publishing RuntimeProgram and the machine never appends
or replaces its declarations. The host response adds Unit, so does not extend I.
Thus every request/template identity in this public source execution is covered.
This structural source argument does not give a formal encoding of entire native
machine traces or all host-created fresh graph extensions.

## Parent application and remaining work

The checked formal constructor will use one observed declaration and this shared
I for operation number, primitive payload/response types and ground empty type
arguments. Source sections1–3 show why request, handler primitive endpoints and
retained template use the same observation; section4 supplies identity coverage.
The Call consumer can derive hinstance from constructor success and then reuse
accepted native literal producer/readback typing for the same expected result.
The full formal requesting head/prefix must still correspond to this native
request; that whole-trace bridge is not supplied by a source field projection.

This reduces RESPONSE-INSTANCE-1 only on the explicitly supported signature
branch. Polymorphic/effectful signatures, callable/code/environment typing,
source lexical and full numeric primitive semantics, owner/view/template replay,
Force realization and original Call/inference A/B remain OPEN with their existing
owners. No constructor field equation, green example or Rust clone alone closes
them. NO_SAFE_CODE_SLICE follows from inspected ResumeArgument/capture_template:
there is no established production defect or semantics change to implement.
No Lean/Cargo/native/test execution was used to establish this source argument.

## Exact formal observation and checked-application seam

The companion Annotation Effect Hole is obtained structurally from the actual
SourceAnnotationType: retain effects as the same Option row observation; map
Unit/Int/Bool/Str to primitive unit/int/bool/string, Variable to its same name,
Hole to its exact SourceNodeKey, Tuple recursively to its element list, and
Function recursively to argument/result. Effect can be the native row data
observation (position, concrete complete family identities, variable names);
Hole can be the native complete source-key type. No primitive branch requires
choosing or forgetting either payload. The complete identity itself supplies Key
with its decidable Eq; spelling is copied only as descriptive data and is not
used by number or interpret.

`decode_exact` recovers the precise supported function/primitive/None syntax;
`interpret_exists` constructs the shared index and OperationInstance from member
coverage and decode success. `interpret_fields` and `interpret_ground` recover
both endpoint types and the empty type vector. `expected` is a partial observer:
on decode-success it is exactly the response-base projection read by the native
consumer; outside it, none does not mean native rejection. `interpret_response`
derives the former hinstance from `request`/`expected`. The source invariants
above supply why both read the same declaration. The `request` and `template`
Lean aliases are convenient consumer names and are not themselves simulations.

`actual_call_request_completed_declared_literal_response` preserves the complete
prior conclusion. It retains hrequest (the actual formal head operation is this
constructed instance) and hexpected (the expected base is this partial observer).
These are representation correspondences: section3 justifies the local retained
source fields, but the global native-to-formal prefix/head relation is still
OPEN. The structural observation is defined by the case map above and is not an
executable Rust-to-Lean extractor. Source review and Lean checking jointly
support this local bridge with that explicit boundary, not a whole compiler proof.
