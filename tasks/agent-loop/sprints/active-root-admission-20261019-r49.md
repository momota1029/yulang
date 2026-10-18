# Sprint R49 — active-root Apply admission feasibility

Status: ACTIVE, revision 1
Baseline: `49f7680234ddfd2c9f3ad198c81a502ebdc916a1`
Branch: `research/simple-sub-intrusion`
Parent: full inference/evaluator theorem and original Simple-sub A/B, original
quantifiers, source domain and accepted semantics; **OPEN, 0 -> 0**.

## Fixed outcome

Determine whether the unchanged active-root recursive fixture has a complete,
source-supported native path from active initializer reference through scoped
Apply authentication, admission and execution cutpoint under existing approved
semantics.

Return exactly one bounded result:

1. A complete existing producer -> authentication -> admission path with its
   exact premises and owner transitions; or
2. Owner-specific `NO_SAFE_CODE_SLICE`, naming the first missing contract,
   authority or architecture decision.

Do not re-prove R48's known `Action::Link` / `LocalFreshRoute` mismatch in
isolation. Decide whether the existing authority permits an authentic
monomorphic active-root reference to satisfy the scoped Apply consumer, or
whether that compatibility is an unmade design decision. Do not require the
missing `Desc` / `D_q` source-formation theorem to answer this structural
admission question. Structural reachability does not establish source typing.

## Scope and hard boundaries

The source case is the existing parameterized local recursive function whose
initializer is active while its direct recursive Apply and nested helper-body
Apply are visited. Preserve the exact HIR identities, active-initializer
lifetimes, source action order, monomorphic shared root, helper occurrences,
existing scope and all accepted source behavior.

This is a read-only proof and owner-map sprint. **No compiler source, fixture,
expected-output, public API or semantic edit is authorized. No build, Cargo,
test or runtime probe is authorized.** Do not synthesize a LocalFreshRoute,
reuse a sibling route, alter scheduling, freshen an active monomorphic root,
weaken authentication, or infer authority from endpoint equality. Any source
route/admission change or fixture substitution requires a new explicit primary
contract and applicable semantic approval.

The authoritative `local-self-recursive-binding` decision requires recursive
occurrences to link to the same open monomorphic initializer root and forbids
routing them through LocalScheme/FreshUse during initialization. The scoped
Apply consumer currently requires an exact occurrence-indexed LocalFreshRoute.
R49 decides whether an already-approved interpretation reconciles those owners;
it does not create one.

## Frozen baseline and dependencies

Grant commit: `49f7680234ddfd2c9f3ad198c81a502ebdc916a1` on `research/simple-sub-intrusion`; predecessor
R48 closeout commit `6f848b778f01cc41276639203089d11207086bfb`. Luna must replace
the abbreviated grant locator with the verified full `git rev-parse HEAD`
before activation and record all listed hashes.

| Dependency | SHA-256 | Role |
|---|---|---|
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` | Authoritative monomorphic active-root source decision |
| `questions/2026-10-10-local-recursive-binding-scope/approved-answer.md` | `1c0ea94c359f08496185594848ab9082b4eac174ab247d67d37f316462db145b` | User-approved scope decision |
| R48 closeout | `35de4c623562f01c636b3c5e463f0dd105fe996136fefdf39a5149d5825c7e98` | Reviewed obstruction and no-test disposition |
| R48 compiler review | `b91fa227bd1a686ab08b9a5fa492fc69a2530ba4671f158fd5f1c0563b513fea` | Exact Link/authentication blocker and owner audit |
| R48 spec review | `4ec09e82ae00e13f47332178b64dde325c4c1baf8bdbc84db92e06dc0943d53c` | Authority/scope confirmation |
| `candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Active-initializer producer and source action ordering |
| `candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Scoped Apply authentication consumer |
| `candidate_scheme.rs` | `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278` | Local route publication and transaction owners |
| `shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Scoped Apply admission gate |
| `lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Route transaction commit/rollback boundary |
| `candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Existing unchanged fixture and identity assertions |
| `notes/design/2026-10-17-local-use-retention-code-contract.md` | `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a` | Unapplied draft; explicitly not authority |

All hashes are revalidated at activation below. Source files are read-only
inputs. No historical claim, stale RUNNING row, or R48 implementation candidate
establishes a live worker or source authority.

## Lanes and exact output leases

### Sol — admission feasibility proof

Derive the compatibility judgment from the authoritative source decision and
existing admission contract. Trace the exact active-root and generalized-local
producer records, occurrence identity, authentication premises, gate and
execution owner. Produce a protocol table for active monomorphic references
versus installed generalized local uses. If no existing interpretation
supports the exact consumer, return the first missing law/owner and the
smallest decision required; do not invent semantics.

Exact writes:
- `notes/theory/2026-10-19-r49-active-root-admission.md`
- `tasks/agent-loop/inbox/20261019-r49-proof.md`

### Luna — source owner map (read-only)

Trace `Action::Link` and `Action::Local` from source scheduling through action
execution; trace `ApplySourceInput.local_callee` through scoped authentication,
route publication, transaction commit/rollback and the failing execution
cutpoint. Identify all existing exact-Name, active-root and LocalFreshRoute
owners. Map the smallest potentially implementable seam only if existing
authority already licenses it; otherwise report `NO_SAFE_CODE_SLICE` and the
missing decision owner. Make no source changes.

Exact writes:
- `notes/progress/2026-10-19-r49-active-root-owner-map.md`
- `tasks/agent-loop/inbox/20261019-r49-implementation.md`

### Independent review

After both lanes freeze the same source/authority snapshot, assign fresh
compiler and spec reviews. They must verify authority applicability, complete
producer/authenticator/consumer path, exact occurrence identity, monomorphic
versus generalized mode, transaction lifetime and the stated stop result.
Reviewers write only their exact receipt paths:
- `notes/progress/2026-10-19-r49-compiler-review.md`
- `notes/progress/2026-10-19-r49-spec-review.md`

## Resources and stop conditions

Fresh cap: **2400 seconds**, no carryover. Sol proof 900; Luna read-only owner
map 600; two independent reviews 300 each; Luna integration 300. Astra 0.
No verification process, build, test or runtime. CPU/RSS UNKNOWN unless
measured. Resource allocations are charged on issuance; reserve 300 seconds for
integration after proof, mapping and reviews.

Stop at the fixed decision, the first unsupported authority premise, any
source/dependency/lease change, or budget boundary. If the result is
`NO_SAFE_CODE_SLICE`, close R49 after review; do not continue into output
formation, `Desc`/`D_q`, or another source audit. Parent remains OPEN 0 -> 0.

## Primary activation receipt

Luna revalidated the listed dependencies and the R48 closeout against the
current worktree after R48 closeout commit `49f7680234ddfd2c9f3ad198c81a502ebdc916a1`; exact HEAD, branch,
session, worker identity and current-state resource/lease records are in
`tasks/agent-loop/current.json`. R49 grants only the output leases above.
