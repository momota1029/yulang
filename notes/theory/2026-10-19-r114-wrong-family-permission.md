# R114 finite wrong-family permission: source-identity obstruction

Status: **FROZEN CANDIDATE / HARD INPUT BOUNDARY / STOPPED**. Revision 1.
Author: `/root/r114_proof`, sole author; no descendants or coauthors. Requested
model/effort: Sol/high. Observed model/effort: UNKNOWN/UNKNOWN; no effective
routing receipt is available to this worker. This artifact is neither an
independently reviewed theorem nor production authority.

## Parent claim and exact application

Contract: `tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md`,
SHA-256 `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
Luna's assignment permits only this artifact and
`tasks/agent-loop/inbox/20261019-r114-proof.md`, at most 480 seconds, with no
new direct source owner and no delegation or executable compiler work.

The parent finite claim concerns exactly the 195-byte Boolean source below,
SHA-256 `91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`,
without final LF:

```yu
act signal:
    our ping: bool -> bool
act other:
    our unrelated: int -> int
my receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }
my main = receive (signal::ping true)
```

Subject to ordinary preparation, the requested result is direct Machine
`Unavailable(HandlerEvidence(original_handler_site))`, followed by public stdin
CLI failure with empty stdout and the corresponding original-site diagnostic.
The required source bridge includes authentic unequal `signal` and `other`
identities; it cannot assume that premise merely because their spellings differ.

**Actual result:** a required identity-constructor premise crosses the frozen
input boundary. The proof stops before establishing the complete finite claim.
The inspected consumer calculation below reduces the runtime permission decision
to that exact premise. It does not discharge it, establish current preparation
success, or establish the current CLI observation. No parent gate closes.

## Governing authority

The annotation policy §1 in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` grants
function-local subtraction for the specified resolved concrete identity at a
contravariant position. The charter
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §13 preserves typed
source identity and permits no authority at an unexposed position. The
receiver-relative clarification in
`notes/design/2026-10-15-callback-identity-forwarding.md` preserves other
receivers' protections. These are policy premises, not proofs of source-key
injectivity, CandidateInference correctness, or actual runtime correspondence.

## Decisive missing constructor premise

In `crates/yu-hir/src/module/source_annotation.rs:33`, `SourceEffectId` derives
`Eq`, `Hash`, and `PartialEq` on exactly `module: Arc<ModuleId>` and
`declaration: SourceNodeKey`. Spelling is absent from identity.
`source_annotation::declarations` (same file, declaration allocation near line
193) constructs each ID with `module.clone()` and
`counters.source_nodes.get(&node).clone()`. Thus for these two declarations in
the same module, unequal family IDs requires unequal declaration source keys.

The pinned `crates/yu-hir/src/module.rs` delegates population of
`counters.source_nodes` to `crate::source_identity::try_source_keys(parsed)` or
`crate::source_identity::source_keys(parsed)` (lines 1110, 1123, 1135, 1148).
The direct owner of that minting/injectivity premise is the unpinned module
`crates/yu-hir/src/source_identity.rs`, symbols `try_source_keys` / `source_keys`.
That path has **not been read or modified** by this worker. No claim is made
about its bytes or correctness. Reading it to establish the required premise
would add a required direct owner outside all 19 frozen pins, triggering the
contract's stop condition.

The exact open premise P-ID is: for the successfully formed parse of this exact
source, the keys retrieved for its two distinct `ActDeclaration` syntax nodes
are unequal, and retain the authentic declaration ownership consumed by
`SourceEffectId` equality. The inspected map consumer does not itself prove
this producer property. Different names and distinct map keys do not prove
distinct map values. An existing successful Machine assertion also cannot
substitute for this constructor proof.

Falsifier for P-ID: both declaration entries yield equal identity keys, or a key
is not associated with its actual declaration. Such a result invalidates the
requested family-membership argument even if name lookup distinguishes the
spelling strings.

## Inspected conditional source/consumer calculation

The following is a candidate calculation inside the unpromoted finite trace.
It is useful only under independently established authentic distinct declaration
keys and successful source preparation. Uninspected transitions are not silently
assumed established.

```text
source ActDeclaration nodes
  -> module.rs: source_identity::{try_source_keys,source_keys}  [P-ID OPEN]
  -> source_annotation::declarations: SourceEffectId(module,key)
       signal = S                 other = O                 [need S != O]
       | operation ID.family=S       | parse_row [other] -> concrete=[O]
       |                              -> LocalSourceParameter.annotation
       |                              -> Instruction::Lambda.root_schema
       |                              -> RootCompSchema.formal (clone)
       |                              -> Computation entry boundary(receiver)
       |                              -> Receiving::local_grant(..., S)
       + request.declaration.id.family ----------------------> [O].contains(S)
                                                              = false if S != O
       Lambda -> closed_primitive=false
       matching Catch arm + false local grant
         -> HandlerEvidence(handler.site) -> execute error -> CLI failure
```

1. `source_annotation::declarations` creates operation declarations with
   `SourceOperationId { family: family.id.clone(), declaration: ... }` and
   indexes operation lookup by `(family.id, member spelling)`. HIR
   `local_source.rs::Builder::resolve_operation` resolves that family namespace
   before operation lookup. This retains family identity as an operand; it is
   not permission by spelling. It still needs P-ID for the two family operands
   to be distinct.
2. `LocalSourceParameter` in `local_source.rs:348` retains the resolved annotation.
   Named-formal formation near line 601 calls `source_annotation::parse_annotation`
   and stores it in the same parameter cloned into `LocalSourceForm::Lambda`.
   The row parser in `source_annotation.rs::parse_row` looks up a unique family
   and appends its declaration identity to `concrete`. For this `[other]` row,
   the intended authentic singleton is `[O]`; no `signal` token occurs in it.
3. Runtime `program.rs:418` gives an effect-annotated formal executable Name
   consumption. Its Lambda projection near line 488 selects
   `ParameterRole::Computation` whenever the formal annotation has an effects
   row, and calls `RootCompSchema::from_parameter` with the original lambda
   `SourceSite` and original parameter. `receiving.rs:22` checks matching
   annotation/formal/lambda source roots, an effects row, and a primitive value
   type including Bool; it clones the original formal without rewriting its row.
   This is a projection from the same HIR, not evidence that a solved candidate
   graph is consumed to build runtime permission.
4. At a closure application, `machine.rs`'s `Frame::Callee` branch constructs an
   inert argument Delay, mints an invocation, and on Computation entry calls
   `receiving.enter(delay, delay_view, activation, schema.clone())`. It creates
   the receipt under `ExecutionOwner::Invocation(activation)` with the original
   formal ID and binds that parameter to the resulting view. These are inspected
   constructors, not an executable probe assuming an arbitrary transition.
5. `receiving.rs::Receiving::local_grant` first requires an Invocation owner,
   active invocation and a boundary for that receiver. It then checks the exact
   retained annotation owner and `row.concrete.contains(family)`, returning
   false on failure **before** further observation/image/receipt checks. With
   authentic `[O]` and request-family S, P-ID entails `O != S`, hence no local
   positive grant. This implication does not require collapsing inherited
   coverage, images, receipts, providers or witnesses. Unknown coverage remains
   unknown, and absence of a local certificate gives no negative certificate.
6. `primitive.rs::closed_primitive` immediately returns false for any constructed
   `Instruction::Lambda`. The receive formal generates such a Lambda under the
   inspected runtime projection. Thus this source is outside that bypass's
   certified universe; there is no appeal to a withdrawn bypass.
7. `machine.rs::propagate_request` near line 1582 checks the actual operation
   declaration ID against the request, then under `!program.closed_primitive`
   invokes `local_grant` on `request.declaration.id.family`, the request event,
   observations, installer owner and live invocations. A false result returns
   `RuntimeUnavailable::HandlerEvidence(handler.site.clone())` before handler
   selection commits. This is an original handler HIR site, not a manually
   invented numeric span. Complete formation of this exact request/observation
   and reaching this Catch were not independently completed after the hard
   identity boundary; they remain required finite correspondence checks.
8. `lib.rs::execute` uses ordinary `prepare`, constructs the runtime from the
   returned HIR, and turns `RuntimeOutcome::Unavailable(error)` into
   `Err(bounded_message(format_args!("runtime unavailable: {error:?}")))`
   before completed-result rendering. `main.rs::run` obtains the complete
   returned output using `?` before `print!`; `main` writes errors to stderr and
   returns failure. Therefore that same error, **if reached after successful
   preparation**, cannot publish a completed result on stdout. No actual CLI
   execution or independently established preparation success is claimed.

## Static acceptance, history and independent quantifiers

The reused historical evidence is only the pinned source fixture
`runtime_receiving.rs::primitive_roots_require_the_original_receivers_exact_concrete_permission`
and its helper `machine` / `assert_missing_evidence`. Its Boolean / `other`
instantiation contains the exact fixed source. The helper asserts empty syntax
diagnostics and candidate conflicts, constructs the runtime from the same HIR,
and expects HandlerEvidence at 10,000 steps. The checked-in assertion is not a
current run and cannot prove authentic source identity or the source-to-runtime
bridge. No old green result is reused as current execution evidence.

Candidate registration/constraint propagation and a full current static solve
were not proved. The constructor obstruction occurs earlier. No claim is made
that the accepted annotation policy has complete static effect-hygiene
realization, nor that arbitrary candidate source constructors emit assumed
transitions. This packet changes no Simple-sub generation, accumulation,
propagation, levels, extrusion, qualifying intrusion or generalization.
F1/FK1, evaluator/A/B quantifiers and foreign-continuation cases are untouched.
No earlier conditional general hygiene theorem or R113 cursor/continuation
storage result is used to close a premise here.

HandlerEvidence is experimental missing positive evidence. It establishes
neither language-level rejection nor successful outward forwarding. The source
has distinct operation spellings; no same-spelling sibling operation theorem,
sibling-view isolation, general transport theorem, universal admission claim,
or production cutover follows.

## Frozen dependencies

All 19 pins matched before analysis and again at artifact freeze. Contract hash
also matched. No dependency bytes were changed.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-15-callback-identity-forwarding.md` | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_effect.rs` | `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0` |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

## Checks, resources and exact stop

Read-only source inspection and SHA-256 checks only. The exact source byte
length/hash and all 19 pins were checked using Python 3. An initial `python`
hash utility invocation was unavailable (exit 127); a subsequent read-only
Python 3 hash invocation had a parsing mistake, then the corrected line-based
hash check succeeded. These were utility failures, not compiler attempts or
source outcome mismatches. No build, test, runtime, CLI, formatter, Git, network
operation, scratch file or subprocess worker was used. No compiler/test/source
file was edited. No self-review or independent certification is claimed.

Budget reservation: 480 seconds; exact total observed runtime unavailable to
this leaf, so leave the full reservation charged pending Luna's launch receipt.
Work ended at the first new required-owner boundary, with no expansion, repair
or retry. Only the two exact leased outputs were created. Writer state at
submission: **STOPPED**, no descendants, no further writes after freezing.

Next step requires Luna, not further worker action: decide whether to reject
this incomplete candidate or issue a separately frozen contract that explicitly
includes the source-key producer and the remaining finite request/preparation
checks. Current proof and production gates remain OPEN.

Mutual TODO R114-P-ID: Luna owns contract/input adjudication. First missing
evidence is authentic unequal declaration keys from the actual source-key
producer; required inputs are its frozen bytes and existing HIR consumer pins;
proposed output is a finite constructor lemma applied to S != O and the
membership failure; falsifier is equal/misattributed declaration keys. No new
owner read is authorized in the current packet.

Mutual TODO R114-P-EXEC: Luna owns the independent test lane and command gate.
This candidate supplies no proof clearance for executing the gated command.
Ordinary preparation success, exact request/observation reachability and the
same-source stdin diagnostic remain to be established; a preparation failure,
different runtime outcome, CLI success, nonempty stdout or wrong-site diagnostic
falsifies the fixed prediction. Fresh review belongs to Luna; this producer is
ineligible to certify either its own result or the combined sprint.
