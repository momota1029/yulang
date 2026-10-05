# Production correspondence for the literal Int Initial context

Date: 2026-10-06 (assigned artifact date)
Status: reviewed bounded research-only source audit; production `chi` formation remains open
Baseline: `33df8d3c708f8c73f1515ce80c5651cfcae642b7`
Lease: this file only
Implementation authority: none
Method: bounded production-path inspection and a minimal lowering obstruction

## Objective and result

Determine whether the current parser/HIR/solver path supplies the independently
typed punctured context and complete decorated slot/view consumed by the fresh
Int Initial construction. The inspected path supplies lexical binder identity,
integer facts, structural Function endpoints and scheme-use transport. It does
not supply a complete call certificate for the smallest ordinary application.
The missing generation seam occurs before collection, at resolved expression
lowering; the existing objects named `View` and `AdmissionReceipt` do not close
the decoration premise through an alternative inspected path.

This is a bounded characterization of the named production path, not a theorem
of repository-wide absence, an information-theoretic insufficiency result, or
a semantic counterexample to the selected language. No new interpretation of
the selected entry or Function meaning is proposed.

The prior literal Initial note is a historical conditional construction. Its
decorated witness remains a hypothesis; its committed presence is not proof
authority. This audit neither edits that note nor independently certifies its
mathematics.

## Baseline, decisions and direct dependencies

The current task and design index were read at the baseline. Governing rules
read: `rules/research-lab.md`, `rules/design-authority.md`,
`rules/git-concurrency.md`, `rules/orchestration-budget.md`,
`rules/agent-orchestration.md` and `rules/question-board.md`.

Exact semantic scopes consumed:

- Charter §21 fixes an unannotated parameter as `Value(A)` and places the
  single entry demand/rebind inside the actual receiver activation. Pure
  introduction or empty support does not select a different entry.
- Callback delivery §4 preserves an existing Pure value's actual role/entry;
  the invocation slot supplies its original typed boundary/profile.
- Typed core §2 takes typed paths, `Flow`/receipts and one original `(nu,K,D)`
  as inputs. §6 synthesizes literal/name/lambda/application structure relative
  to known lexical/declaration interfaces, retaining whole argument incidence.
  §9 distinguishes `J_arg`, `J_body` and `J_call`, and retains the actual
  receiver, executing view and result rebind. Its bounded construction still
  consumes supplied typed-profile/path entries (§9:988–995).
- Theorem C §2.1 takes decorated kernel witnesses before the query; §2.2 says
  a scalar primitive cannot manufacture a receipt, typed path or capture
  grant. §3 Initial consumes a locally typed whole carrier with its declared
  result port/profile/path and the punctured context/known slot.
- Source-indexed realization §§2, 3.1–3.2 and 4 define a reference construction
  from those supplied decorations. Current-production conformance remains open.
- Approved inlet-domain d1 decisions 1–5 quantify over all independently typed
  compatible punctured contexts, including unused exports, with callable and
  whole carrier holes and joint evidence at one original fiber. Admission must
  be independent of the pending Function comparison.
- Approved denotation d1 decisions 1–5 keep complete original `Rel_C` and
  independently interpreted endpoint/admission obligations. Approved bound
  membership d1 decisions 1–4 allow independently licensed Option 2 extras;
  source constructors are not required for every production observation.

Direct pinned blobs (all equal to current HEAD and worktree at dependency
check; no mutable shared draft was consumed):

| Path | Git blob |
| --- | --- |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `fb4a169a2d748422490cc74c026338587290e90c` |
| `crates/yu-syntax/src/full_parse.rs` | `333418af36d9a9ef4fb730ebbbbe28bcf1a46998` |
| `crates/yu-syntax/src/declaration/binding.rs` | `165ad487cfebde8b40327a4144ac870782fc9acd` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `2ccc0ef818deeb4fdc47c415aabff9e6c8fcf2ff` |
| `crates/yu-hir/src/lib.rs` | `0c5e1ac6c1acba5707b33911be82fe4a1d75caa0` |
| `crates/yu-hir/src/module.rs` | `668d1b6f82fb17a96178a2353543d288c32e2762` |
| `crates/yu-solver/src/lib.rs` | `fa118b726ebbfdc7d32b617373b4e2cb04e84682` |
| `crates/yu-types/src/lib.rs` | `c3a4e95d199fba0784b7e6448b6bb37a1f2c7798` |
| `crates/yu-core/src/lib.rs` | `b2f06181fd47a991935cd7d1d8f117db9523beec` |
| `notes/progress/2026-10-06-function-id-literal-inlet-source-subcase.md` (historical input only) | `6272e6cf1b97b73b9dca830f9731ba2ff79cafaa` |

## Production trace and the minimal obstruction

Use the proof-level hole interface `H:Value(Int -> Int)` with Value entry and
an Int result, a whole literal carrier, an empty other environment and empty
history. This notation is not a proposed raw annotation or compiler type tag.
The smallest source-shaped caller body is `h 1`; the unary declaration
`my invoke h = h 1` exposes that body with a lexical parameter representing
the callable hole. It does not itself fix `h`'s inferred endpoint at the
declared proof-level interface.

The following is a source-inspection derivation, not an executed parse:

1. `yu-syntax/full_parse.rs:246` `parse_file` establishes the accepted operator
   table and calls `cursor::parse_root`. `declaration/binding.rs:198–253`
   separates binding header/target and body. `expression/operator_chain.rs:782`
   `ml_argument` emits `SyntaxKind::MlArgument` around its expression child.
2. `yu-hir/lib.rs:299–314` handles ordinary `MlArgument`, fixed `CallTail`,
   and outer `TypeAnnotationTail` as structural continuations.
   `structural_continuation` at `:463–482` puts the preceding expression first
   and retains child expressions. Ordinary application is therefore a
   non-leaf `HirExpr::Value`; `HirExpr::Apply` at `:64` denotes dynamic operator
   application and must not be mistaken for resolved callable application.
3. `module.rs:1037` `plan_root` recognizes only direct expression chains and
   plain admitted bindings. `plain_binding_header` at `:1471–1517` admits an
   identifier plus at most one identifier parameter; it creates no typed
   callable-slot or annotation contract. `lower_plan` at `:1155–1205` allocates
   that parameter and wraps the lowered body in `ResolvedExpr::Lambda`.
4. `lower_body` at `:1362` calls `lower_simple_chain`. Its `:1419–1423` guards
   reject a missing atom or anything other than a childless `HirExpr::Value`.
   The associated `h 1` fails that leaf requirement (or stops at the earlier
   atom guard); `:1374–1385` records `UnsupportedExpression` and an error body.
   This conclusion needs no assumption about a successful Function comparison.
5. `ResolvedExpr` at `:426–449` is exhaustively Lambda/Integer/Name/Error.
   There is no call, delay, result-rebind or typed-slot node on this path. The
   integer inside this unsupported body is not a separately resolved call
   operand that collection can connect to a receiver.

This is minimal in interaction structure: one callable hole, one scalar
argument and one ordinary call. Removing the call leaves only a name/literal
and no invocation certificate to audit. The witness isolates a generation
obstruction; it is not a rejection policy for the approved broad inlet domain.
The parenthesized spelling `h(1)` takes the same fixed-postfix continuation
seam, conditional on its parser-produced CallTail. No syntax execution or
recovery-free acceptance claim for either spelling was measured here.

## Callable interfaces and the alternate objects checked

| Object/path | What the inspected production code supplies | Why it does not supply the Initial decoration |
| --- | --- | --- |
| Lexical parameter/name | `module.rs:1443–1464` resolves a leaf to `HirParameterId` or `DefId` | Binder/name resolution supplies identity. It does not independently type a punctured call or identify its demand/result `Flow` path. |
| Lambda collection | `yu-solver/lib.rs:1041–1051` calls `emit_lambda`; `:1557–1617` records `LambdaRecipe` | Recipe fields retain parameter position, body/root/effect components and insertion position. They contain no call operand or executing slot/profile. |
| Identity Function endpoint | `admit_lambda_fact` at `:10539–10579` constructs a positive Function from parameter/body terms and records its root fact | The identity case shares one parameter ordinal with its result. Its negative EmptyEffect and body-effect fields are structural terms, not a proof of incoming carrier purity or a complete invocation view. |
| Literal endpoint | `emit_integer` at `:1454–1498` records Int lower/upper and bottom/empty effect facts | A separately lowered scalar leaf has these facts. Theorem C §2.2 forbids deriving receipts/paths/grants from a scalar relation alone. |
| Scheme-use transport | `route_internal_inner` at `:13990` connects definition-root/use rows; `route_incoming_inner` at `:14877–14963` routes nontrivial predicates through `instantiate_and_route_closed_inner` at `:14527`, alongside direct Bottom-provenance (`:14903`) and Int (`:14937`) branches | Fresh quantified variables, restored recursive bounds and routed positive predicate facts preserve type-use structure. A definition use is not an invocation or independently admitted punctured context. |
| Closed type views | `yu-types/lib.rs:585–620` defines positive/negative Function views with four polarized type/effect handles; `ClosedValueSchemeView` at `:638` references an arena and scheme; `:798–807` projects stored fields | These `View` names describe arena lookup. They contain no current receiver activation, carrier path, invocation receipt, history or slot boundary. No constructor inspected interprets them as the complete executing CallView. |
| Solver admission receipt | `AdmissionReceipt` at `yu-solver/lib.rs:2858` has store token, serial, constraint occurrence, cause, fact and delta; `:3559` mints it; `record_provenance` at `:3273` checks exact store/fact/cause and consumes it | Its certified event is a constraint-store transaction. The actual receiver/invocation receipt in typed core §9 is a different obligation; matching the noun does not establish a correspondence. |
| Retained solve result | `SolvedModule` at `:7168` retains HIR, schemes, arena, routed-use provenance and store; `:15665` enters `InferenceSession::run` (`:9731`) | Retention could support a future reconstruction proof. Its existing field map/public queries (`:15668`, `:15677`, `:15729`) do not themselves form that proof. |
| Core seam | The pinned `yu-core/src/lib.rs` contains only the backend-neutral boundary module comment | This particular file supplies no executable typed-context constructor. Other backends/legacy crates were not exhaustively audited. |

Evidence for a future bridge is concrete: immutable occurrences, source ranges,
lexical parameter identity, retained HIR and closed polarized schemes are real
inputs. Evidence against claiming an existing bridge is the stopped call
lowering and the actual payload/consumers of the alternate view/receipt objects.
Neither observation establishes that reconstruction from richer retained or
future inputs is impossible.

## Exact missing premise and claim separation

For this Int challenge the open premise is an independently formed certificate
`chi` for the punctured call, at the original joint `xi=(nu,K,D)`, containing:

- the declared callable-hole interface and known instantiated slot `beta`,
  its original typed profile and applicable view contract;
- the whole carrier's designated computation/result port and typed Int path;
- the actual receiver activation/receipt and complete executing-view relation,
  including designated demand, typed result rebind and result consumer;
- compatible initial configuration, scope/authority, lexical realization and
  local constraints, all valid before the filling's output satisfaction or Q.

Empty history and no other environment values remove provider/history
extensions; they do not supply the remaining receiver/slot/path premises.
The literal rule determines `Value(Int)` and its normalized
`Comp(empty,Int)` result. Charter §21 determines the actual unannotated Value
entry. These two facts alone do not form `chi` or the slot's static
`d-`/`d+`/`b+` correspondences of Theorem C §2.3.

**Conditional reference claim:** with independently valid `chi`, its carrier
derivation, declared result profile/path and local constraints, Theorem C §3
Initial admits the empty prefix before Q. This audit uses that conditional
rule to identify required operands; it does not prove its source premises.

**Production characterization:** the named current lowering/collection/scheme
path produces no call certificate for the minimal application, and the
inspected alternate view/receipt paths certify different objects. The stronger
claim that all existing production paths lack `chi` remains unverified.
Option 2 membership, exhaustive admission, production adequacy and containment
are not reduced to this source-certificate subcase.

## Commands, independence, limits and resources

Checks already run: bounded `git show BASE:path` section/range reads;
`rg -n`/`rg --files` symbol and call-site location; read-only `git diff BASE --`
on the six main parser/HIR/solver/type files (empty); a Python subprocess pass
checking all 17 pinned blobs against HEAD and worktree bytes (all matched);
lease-path absence before creation. Final lease scope and dependencies are
rechecked at handoff. Only this note is written; no tests/builds/code/formatters
or Git mutations are authorized or run.

Initial locator commands attempted nonexistent `yu-vm`, `expression.rs` and
`my_decl.rs` paths and returned exit 2. They were replaced with actual paths
from `rg --files`; their absent/missed matches support no absence claim.
Several broad captured locator reads were truncated; only explicitly reread
bounded sections support the claims above. Call-site searches included inline
test modules, so search hits alone were not classified as production paths.
The test-only HIR candidate below `yu-hir/lib.rs:691` is excluded from the
production bridge. Existing solver research models are not a production oracle.

No checker, executable oracle, finite search, seeds/ranges or mutation run was
used. Independence here is the correspondence method: inspect committed
source payloads and their actual consumers instead of supplying model
transitions. Shared assumptions are the selected role/calling convention and
conditional reference rules; code inspection is not an independent proof of
those language rules. The claimed structural obstruction is invalidated if a
changed dependency introduces a resolved call/decorated-context path, or if
an uninspected alternative production path is demonstrated.

Coverage is the named parser-to-resolved-HIR seam and solver lambda/literal,
internal/incoming scheme transport, closed type-view and receipt seams.
Omitted: complete parser acceptance/recovery, all call sites, complete solver
branch audit, legacy/backend correspondence, opaque imports, annotations or
adapters beyond the inspected structural boundary, request histories, mutable
state, latent providers and exhaustive production membership. This is one
audit method, not a second equivalent toy probe.

Resources: one worker, zero children, zero build/test processes; lightweight
commands completed in under one second each. At most two independent read
commands ran together once; all later inspections were sequential. CPU,
aggregate wall time and peak RAM were not instrumented. No enumeration or
long-running process remains incomplete. This is bounded correspondence
evidence; it does not certify a universal absence claim or the semantic
authority of the conditional source rules.

Independent review by `production_view_bridge_review` confirmed the bounded
HIR/lowering obstruction and found no blocking or major findings. One minor
dispatch wording issue was closed by qualifying the generic incoming scheme
route and naming the direct Bottom-provenance and Int branches in §4. The
review did not execute the parser or audit every production/legacy path.

Recommended next action: isolate formation/interpretation of `chi` for this
one independently declared Int hole and literal carrier in the existing
decorated source kernel, naming its actual original inputs. If production
generation is required, request a separate exact call/profile/path gate before
compiler edits. A scalar check or another assumed transition model cannot
close this missing premise.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-function-production-initial-view-bridge.md` only.
- Baseline SHA: `33df8d3c708f8c73f1515ce80c5651cfcae642b7`.
- Dependency changes: none at the 17-blob HEAD/worktree equality check; pins above. Final recheck accompanies handoff.
- Review status: independently reviewed bounded research-only production correspondence audit; no theorem closure or production conformance certification.
- Checks already run: committed section reads, bounded symbol/call-site searches, six-file baseline diff, 17 dependency identity/byte checks, lease absence and final scope/dependency check; zero tests/builds/models.
- Proposed one-line research-checkpoint commit message: `research: audit production bridge for literal Int Initial view`.
- Shared-record deltas left for primary/curator: retain independent `chi` formation/endpoint conformance as open; distinguish closed type views and store receipts from execution decoration; record the pre-collection call seam only for the inspected path. `tasks/current.md`, design index/authority, theory maps and question bundles are intentionally untouched.
