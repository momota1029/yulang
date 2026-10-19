# R114 rev3: authentic family identity and current conditional permission route

Status: **FROZEN CANDIDATE / SOURCE DERIVATION / NOT INDEPENDENTLY REVIEWED**.
Revision 1. Author: `/root/r114_source_identity_proof`, sole author; no
coauthors or descendants. Requested Sol/high; observed model/effort
UNKNOWN/UNKNOWN, since this worker has no model-routing metadata receipt.
This is neither reviewed theorem authority nor production authority.

## Parent, scope and actual result

Governing contract: R114 rev3,
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev3.md`,
SHA-256 `82653f7ec4a515e7a06b7c138499341bb75fc283c3ad2dda0dcdca1668943689`.
The named baseline is `a96f040f4c2e07c1832e8ffca05db673da4318e5`; no Git command
was used to independently authenticate that commit. All prescribed current
file bytes were authenticated by SHA-256 at startup and freeze.

The parent is the unchanged finite R114 source, 195 UTF-8 bytes without final
LF, SHA-256 `91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`:

```yu
act signal:
    our ping: bool -> bool
act other:
    our unrelated: int -> int
my receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }
my main = receive (signal::ping true)
```

**Result:** candidate derivation discharges precisely P-ID under its original
successful-parse/formation premise: the authentic declaration keys differ,
and therefore the family identities S (`signal`) and O (`other`) differ.
Applying that result to the inspected current constructors and consumer yields
`[O].contains(S) = false` and hence no positive local Grant at this receiver.
The current finite Machine control route and public error withholding are
traced below. Successful current preparation, empty candidate conflicts,
construction/execution and the exact public CLI observation are **UNVERIFIED**
until Luna's separately gated command. No parent/general theorem is closed.

The premise is the same successful parse and ordinary preparation already
required by rev1. It is not a new admission restriction or substitute theorem.
A parser, inference or preparation failure remains a falsifier of the original
fixed prediction. We do not prove parser correctness or complete solver
correctness from these pins. Resource availability and the specified 10,000
execution-step observation also remain the original bounded verification gates.

## Governing meaning

The annotation policy in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1 grants
function-local permission for the resolved concrete identity. Its §1.1 makes
that permission an open computation input, rather than a closed effect upper
bound. The charter
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §13 requires matching
typed source paths; the receiver-relative clarification in
`notes/design/2026-10-15-callback-identity-forwarding.md` preserves independent
receiver protections. These policy authorities are not current execution
proof. `HandlerEvidence` records missing positive evidence; it proves neither
language rejection nor outward forwarding.

## Constructor lemma and application to P-ID

Let P be the successfully formed ParsedFile of exactly these bytes, and let
A_s and A_o be its two direct-root positive-width ActDeclaration occurrences.
Their starts are 0 and 39, respectively, computed from the unchanged UTF-8
source prefix. These are declaration offsets used for key inequality, not
invented handler diagnostic spans. Exact parser admission/shape is covered by
the original successful-parse/formation premise, not inferred from old tests.

1. `full_parse.rs::parse_file` (317–341) retains the supplied source and
   constructed green tree and creates `parse_identity: Arc::new(())`.
   `ParsedFile::source_root` (130) creates the root with that same brand.
   `SourceNode::children` (120) descends the actual tree and clones the brand.
   Induction on descent therefore gives every visited node the same authentic
   P brand and its actual syntax node. No caller-supplied node receives a brand.
2. `SourceNode::key` (113) constructs exactly `(parse.clone(),
   node.green().into_owned(), node.text_range().start())`. The green allocation
   is retained, so equality is not based on recycled address guesses.
   `SourceNodeKey::eq` (86) requires parse pointer equality, green pointer
   equality, **and** start equality. Thus K_s != K_o because 0 != 39,
   independently of whether green interning happens to share allocations.
   Both keys satisfy `P.owns_source_key` by its pointer comparison.
3. `source_identity.rs::{source_keys,try_source_keys}` (26,36) start at that
   parse-owned root. Their finite stack walk inserts `(node.syntax().clone(),
   node.key())` for each popped node and adds all actual children. By the usual
   finite-tree traversal invariant every reachable node is visited with its
   own key. Hashing is an index; hash collision alone cannot equate unequal
   keys. An identical SyntaxNode revisit retains the same key; no key value is
   synthesized from a spelling. In the fallible version, allocation failure
   returns IdentityExhausted rather than publishing a successful partial map.
4. `module.rs::lower_module_with_local_source` (1140 onward) initializes
   `counters.source_nodes` using `source_keys(P)` and enables LocalSource.
   The ordinary `lower_module` path uses `try_source_keys`; if successful it
   has the same constructor invariant. `lower_module_with_counters` creates
   its root from P's same retained green tree and calls
   `source_annotation::declarations` before source formal formation.
5. `source_annotation.rs::declarations` (149 onward) iterates the actual direct
   ActDeclaration nodes. `SourceEffectId` (33) derives fieldwise equality on
   `(module, declaration)` and each declaration field is cloned from
   `counters.source_nodes.get(&node)` (193 onward). Hence the successful
   lookup for A_s yields K_s and for A_o yields K_o; the resulting S and O
   cannot be equal because their declaration fields differ. This implication
   does not require a separate theorem about ModuleId equality.

This proves the exact P-ID constructor premise and applies it immediately to
S != O. It does **not** prove global SourceNodeKey injectivity: the pinned
`full_parse.rs` even contains a shared-green, zero-width example whose keys
alias. That example does not meet this lemma's distinct-start premise and
cannot refute or extend it. No test of assumed key transitions is used as proof.

## Current source correspondence across all seven changed owners

The audit reads each current pinned owner on the forms in this exact source;
it does not claim an exhaustive historical textual diff. No Git or old source
checkout was used. Rev1 source claims are re-established at current owners
below rather than imported from their old hashes.

| Changed owner | Current exact-source path and consequence |
|---|---|
| `module.rs` | LocalSource entry initializes authentic keys, registers both families before binding formation, and retains registered Act placeholder errors. `receive` and `main` retain their own binding roots. Ordinary/expression carrier machinery does not rewrite the family keys. |
| `module/local_source.rs` | Named formal construction (600–660) parses the original annotation with that binding's owner and stores it in the Lambda parameter. `resolve_operation` (1128) uses unique family ID then member spelling; both request and arm resolve the same `signal::ping` declaration. `Case`/CaseBinder construction is not selected by any form here. |
| `candidate_source.rs` | `preflight` (451) admits the resolved monomorphic Boolean operation and unused payload/continuation patterns. Lambda visit (998 onward) emits original source-owned FormalEntry and FormalAnnotation actions. Operation and Catch use their resolved declarations; Case actions are not emitted here. This proves these dispatch facts, not conflict-free completion of the entire solver. |
| `shadow_apply.rs` | Ordinary `solve` (270) uses `solve_mode(hir,false,false)`; LocalSource preflight and registered Act placeholder handling occur in `solve_mode` (385), followed by collection and session execution. Scoped and operation-v1 research paths are not selected. Solver success remains a verification premise. |
| runtime `program.rs` | `from_hir` (262) admits the registered Act placeholders and projects the same binding LocalSource. Roles (435 onward) mark the annotated formal Name Execute; Lambda projection (510 onward) sets Computation and constructs RootCompSchema from the original parameter. Operation/Catch projection clones resolutions, patterns, source sites. Case projection is not selected. Only `main`'s Apply is a computation scheduling root; `receive`'s Lambda is a value fetched when needed. |
| runtime `primitive.rs` | `closed_primitive` returns false immediately for any constructed Lambda. The `receive` Lambda suffices before any Case or dependency classifier can matter. This program never receives that closed-world bypass certificate. |
| runtime `machine.rs` | Existing Apply, Lambda, annotated parameter consumption, OperationPayload/result consumer, request propagation and Catch branches are selected; Case evaluation and CaseBinder lookup are not selected. The concrete frame route below accounts for receiver activity and the retained declaration operand. |

The unchanged `source_annotation::parse_row` (529) reads the unique `other`
namespace entry and clones O into `concrete`. There is one concrete member
and no symbolic variable. Neither parameter annotation formation nor runtime
projection adds S. Operation declaration formation (272 onward) stores
`SourceOperationId.family = S` and indexes `(S, "ping")`; arm and request
therefore compare equal operation IDs while their family remains S.

The unchanged `candidate_effect::candidate_formal_entry_annotation` (1449)
does not close the computation input to its concrete row. Formal annotation
construction retains source row, owner, scope, port path and concrete identity
in FormalPermission, and admits value constraints normally. Candidate action
emission is source evidence; complete solver behavior is not inferred from
its presence. Runtime receives the original HIR, not a reconstructed permission
from solved graph output (`lib.rs::execute` discards `_candidate` after prepare).
No generation, accumulation, propagation, levels, extrusion, qualifying
intrusion or generalization rule is weakened by this proof.

## Concrete conditional Machine trace

The following trace is from the actual pinned constructors, under successful
ordinary preparation/runtime construction and available resources. It is not
an executable model that assumes its own transitions.

```text
P's A_s -> K_s -> S -> ping operation/request family ------------------+
P's A_o -> K_o -> O -> parse_row [other] -> original Lambda formal     |
  K_s != K_o => S != O                  |                             |
                         RootCompSchema.formal clone                  |
                                      |                             |
Apply receive: inert Delay -> invocation r -> Comp entry/view/receipt |
                                      |                             |
Catch installed under r -> Execute original input -> operation request
                                      |                             |
operation receiver exits; request observes genuine executing views   |
RootCompReturn saves its frame; Catch remains installed under live r |
                                      |                             |
                    local_grant(owner=r, row=[O], family=S) <---------+
                                      |
                                  false
                                      |
         HandlerEvidence(original Catch SourceSite) -> execute Err
                                      |
              CLI failure, empty stdout, original-site stderr
```

`Machine::start_source_schedule` / `start` and `begin_root` execute `main`'s
Apply. The ModuleDef Name fetches `receive` once through GlobalRead and
constructs its closure without executing its body. `Frame::Callee` (898)
allocates an inert Delay for `signal::ping true`; that argument does not run
before entry selection. It mints receive invocation r via `new_invocation`
(1294), whose descriptor is active, and pushes ReceiverReturn(r).

The Computation branch (996) calls `receiving.enter` on the original schema,
mints its receipt with Invocation(r) and the exact formal, and binds that formal
to its Delay and resulting view. `RootCompSchema::from_parameter` validates
matching source roots and primitive Bool, then clones the original formal.
`Receiving::enter` retains inherited image/unknown coverage rather than erasing
it, and adds r's boundary. Catch evaluation (726) installs a new occurrence
with current owner Invocation(r), then evaluates the original `input` Name.

`consume` (1904 onward) obtains the genuine receipt, opens an execution view,
pushes RootCompReturn and executes the Delay. The enclosed operation Apply
resolves the same authentic ping declaration, mints its own distinct invocation
q, and pushes OperationResultConsumer, ReceiverReturn(q), OperationPayload.
The Boolean payload returns; OperationPayload constructs a request carrier
with the unchanged declaration. ReceiverReturn(q) leaves q and restores r.
OperationResultConsumer then executes that carrier, which creates PendingRequest
with the retained declaration, fresh event, and `receiving.observe` over the
actual executing views (`execute`, 1977 onward).

The first propagation step saves/unwinds RootCompReturn via
`end_execution_view`, preserving the request's recorded observations. It does
not leave r: ReceiverReturn(r) is below the still-installed Catch. The next
propagation step sees that Catch at the top and validates that its installer
r is the current, active owner. Matching compares the actual operation ID;
the request and arm both carry ping's ID. This accounts for the original
request reaching the consumer; it assumes no foreign continuation or resumed
frame case.

`Receiving::local_grant` (230) requires an active Invocation owner and the
boundary for that exact receiver. It then checks the original annotation owner
and `row.concrete.contains(family)` (258–266), before further receipt/image
queries. By P-ID, row `[O]` does not contain S, so local_grant returns false
regardless of the later observation predicates. This calculation does not
collapse views, receipts, event, image, provider, witness or residual lineages.
It proves absence of this positive local certificate only.

Since `closed_primitive == false`, `propagate_request` (1628–1637) immediately
returns `HandlerEvidence(handler.site.clone())` before selection commits or
executes `false`. `step` converts that Err to RuntimeOutcome::Unavailable.
The original Catch SourceSite is projected from its HIR root, occurrence and
range; no numerical handler span is hand-authored. The finite route contains
no source loop or recursive demand, but the exact 10,000-step observed result
is still NOT_RUN here.

The unchanged public `lib.rs::prepare` uses identical bytes, empty syntax
imports and `ModuleIdentity` key `("inference-playground", "-")`, matching the
frozen direct Machine test. `execute` (167) returns the formatted runtime error
before result rendering. `main.rs::run` obtains `execute(...)?` before print;
`main` emits the returned error on stderr and exits failure. Therefore, if the
specified runtime outcome is reached, stdout is empty and stderr derives from
that original SourceSite. Authentic parse keys are not numerically serialized
into the expected diagnostic; the frozen test derives it from its direct
Machine error and compares the public child result. Actual cross-process
observation and successful preparation remain unverified.

## History, remaining premises and next action

Rev1 proof author `/root/r114_proof` supplied the conditional consumer plan and
identified P-ID. Reused only within those premises, it guided the present
reinspection; none of its changed-owner claims were accepted from history.
Rev2's seven mismatches and STOP remain immutable, not retrospectively repaired.
The new rev3 approved byte overrides are the only reason those owners are now
in scope. Historical Machine assertions and frozen test source are not current
runs. The full SourceNodeKey injectivity claim is rejected as unnecessary and
false for the pinned zero-width sharing example; the exact distinct-start
lemma above suffices for this parent.

Remaining original gates: current syntax/formation and inference success with
zero conflicts, successful current runtime construction, actual bounded Machine
outcome, public child exit/stdout/stderr result, and fresh independent review.
The frozen Rust test expresses these observations, but has not run in this
assignment. This candidate is not an independent certificate of itself.
Luna owns prospective/final review adjudication and the one authorized command.
No newly required direct owner or production implementation TODO was found.
If any observation differs, stop under the original falsifier; no repair or
scope narrowing is authorized. No F1/FK1, general hygiene, foreign-continuation,
Simple-sub/evaluator A/B, source-law, adoption or production gate is discharged.

## Frozen dependency receipt

All 26 prescribed direct/artifact inputs and both contract hashes matched at
startup and freeze. This table records the current approved bytes; the rev3
contract records the seven superseded rev1 hashes.

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-15-callback-identity-forwarding.md` | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/candidate_effect.rs` | `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0` |
| `crates/yu-solver/src/shadow_apply.rs` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/primitive.rs` | `da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `tools/inference-playground/tests/cli_permission_boundary.rs` | `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13` |
| `notes/theory/2026-10-19-r114-wrong-family-permission.md` | `447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92` |
| `tasks/agent-loop/inbox/20261019-r114-implementation.md` | `6eecb772e7ee30d7582c1f5d89b47e9310273f18a393c550f464f67960cf609e` |
| `notes/theory/2026-10-20-r114-source-identity-completion.md` | `8f2a79d5c3a4c7f458da787d18927414d747a93315ccb35356c9677bca43e925` |
| `tasks/agent-loop/inbox/20261020-r114-proof-continuation.md` | `2d8cfd2daf37d374dc8fe86850f25c7425a325c056fa9c9a317c5ba733a833b3` |
| `tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md` | `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c` |
| `tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev3.md` | `82653f7ec4a515e7a06b7c138499341bb75fc283c3ad2dda0dcdca1668943689` |

## Resources and writer stop

Read/hash/source inspection only. No tests, builds, CLI/compiler execution,
formatter, Git, external contact, nested CLI, delegation or Astra. Assignment
cap 360 seconds. First observed clock `2026-10-19 15:20:47 UTC`;
artifact freeze clock `2026-10-19 15:24:34 UTC`; observed elapsed
228 seconds, approximately 132 seconds before the original cap at this freeze.
Luna may conservatively retain the complete 360-second reservation; prior R114
resource charges are unchanged. Remaining authorized work ends at handoff STOP.

Only new paths: this artifact and
`tasks/agent-loop/inbox/20261020-r114-proof-current.md`. Scratch paths: none.
Rev2 files unchanged. Writer STOPPED after handoff freeze, no descendants,
background process or pending mutation. Next action belongs to Luna's review
and verification gate; no in-envelope worker continuation remains.
