# Local negative filters: contribution-sensitive source discriminator

Status: frozen, unreviewed research source characterization; no language
counterexample, runtime bug, theorem closure, or implementation authority.
Producer: primary-assigned researcher leaf; no delegation.
Baseline: `eb2666f80c56ebb1500fc2e359774581c79b2ffb`, branch
`research/simple-sub-intrusion`.
Exclusive lease: this file only. Static inspection; no builds/tests/Oracle.

## Objective, authority, and hypotheses

Determine whether existing endpoint/context dispatch implements a local
contravariant concrete filter over a symbolic tail, subtracting only the
annotation-authorized contribution while preserving the tail connection and
an independent contribution of the same resolved effect.

Governing sections:
[annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5;
[contextual attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, including §3.1;
[residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
“Selected policy” and “Preserved contract and open obligations”; and
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and “Authority and integration”. The last source supersedes unconditional
abnormal restoration requirements. No annotation meaning is reconsidered.
General negative source admission remains disabled.

Inputs are the independently reviewed
[Oracle negative Stack/Filter derivation](../theory/2026-10-12-oracle-negative-stack-filter-source-proof.md)
N/F/R and
[Y3 construction bridge](../theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md)
§§3–6. Their scope is retained: Oracle FILTER checks its true receiver and
preserves an inner relation to the original tail; separately constructed
operations supply subtraction. FILTER alone does not establish a reached
weighted residual reduction. Oracle's residual cache does not override Y3's
distinct constructor-lineage policy.

The derivation assumes valid current candidate handles, normally completed
allocations and reached calls to the named consumers. Two lowers meeting the
same row/upper are an explicit operational premise, not a proved source-program
history. An authentic negative attachment assigning subtraction authority to
one of those lowers is the missing construction premise. No callback output,
pending question answer, all-path replay, or queue completion is assumed.

## Smallest contribution discriminator

Use one resolved nullary effect `E`, one receiving row `p`, one target view
`v` with `allowed=[E]` and `tail=Some(x)`, and two distinct concrete lower
identities. The production constructors can retain their different origins:

```text
source annotation view a: allowed=[E], source_weight=Some(s), Annotation origin
independent operation view b: allowed=[E], Operation origin, source_weight=None
u = AnnotationMember(a,0)
w = AnnotationMember(b,0)
u <: p; w <: p; p <: Allowance(v)
```

`candidate_signature_view` (`candidate_effect.rs:733–770`) retains source set
identity, owner/position, and `ViewOrigin`. `candidate_operation`
(`786–801`), Function result-family selection (`1425–1437`), and the omitted
result-row family constructor (`1459–1466`) construct the operation view's
`Support(b)`. `Support(a)` and `Support(b)` are expanded into these exact
member endpoints by `candidate_check_effect_operand` (`895–917`). Despite its
name, `AnnotationMember` is also the endpoint emitted for an operation view.
This distinction is read from `ViewOrigin`, not from the variant name.

The source annotation set `s` above is current covariant construction metadata;
it is **not** an established negative subtraction grant. For the intended
negative cut, suppose authentic local construction licenses only `u` under
its local attachment/route, while `w` is independent. This is the precise
premise against which reusing the existing matcher is tested, not a claim
that current Y3 constructs that negative cut.

When the supplied opposite bounds are actually replayed, their distinct
endpoint pairs remain distinct. Both matching calls nevertheless take the
same branch (`candidate_effect.rs:918–950`):

```text
check(u, Allowance(v)): effect = views[a].allowed[0] = E
check(w, Allowance(v)): effect = views[b].allowed[0] = E
allowed.contains(E) => Ok(()) in both calls
```

The branch reads neither `a`/`b` provenance, lower attachment identity,
occurrence/owner, processing relation fiber, nor the independent operation's
origin after resolving its operand. It enqueues no continuation or residual
for either matching member. The alternate `Contribution(i)` arm likewise
reads only `contributions[i].effect`, ignoring its retained `origin` and
`instance` for membership. Thus a supplied annotation member and a supplied
independent Contribution of the same `E` have the same outcome. Fresh-use
restoration can copy Contribution endpoints at `candidate_scheme.rs:1064–1067`;
no new ordinary-source Contribution seed is inferred from that copying path.

This is a minimal static discriminator for the proposed shortcut “interpret
successful nominal Allowance matching as local subtraction.” Two contribution
identities are necessary to distinguish local removal from independent
survival; one concrete identity, one receiver, one view and one tail suffice.
Reusing that branch as an output suppression decision would suppress both
members unless an earlier owner separately classified their authentic routes.
There is no such subtraction classifier in the inspected dispatch chain.

**Actual result versus conditional failure:** current code accepts both
membership obligations. It does not delete either stored lower or project a
complete output. Consequently this is not an observed loss of `w`, a runtime
type error, or a source-language counterexample. It falsifies the proposed
consumer correspondence under the supplied local-authority premise. The
approved clause preserving independent same-family contributions requires
an attachment/route-sensitive subtraction consumer beyond this membership
branch. Merely observing that matching `E` is not forwarded does not establish
a defect: local subtraction may require that outcome for the licensed member.

## Tail and filter counter-paths

For an open view, `source_weight` may exist but `closed_weight=None`
(`candidate_effect.rs:758–762`). `candidate_context_source`
(`candidate_context.rs:2483–2494`) therefore supplies IDENTITY. Its live
execution returns without filter work at `2754`. Ordinary row application
stores `p <: Allowance(v)` and replays opposite bounds
(`candidate_extrusion.rs:840–863`); it emits no separate `p <: x` relation.
The tail is reached only by the unmatched-member branch (`946–950`). Capture
incidence `(tail,source,view)` at `candidate_effect.rs:552–559` is explicitly
capture incidence, not an executable row edge or negative continuation.

A secondary operand `F` distinct from `E` discriminates the open Allowance
from the reviewed Oracle finite FILTER consumer: Allowance forwards `F` to
`x`; the reviewed finite FILTER checks `F` on the receiver and generates a
membership violation before its inner relation proceeds. This is a static
consumer difference, not an assertion that Oracle's entire negative mechanism
must be represented by that filter alone. Adding a direct row edge does not
supply selective subtraction or the required residual projection.

Reusing an existing closed filter has two distinct limits:

- A genuine closed Allowance checks both `u` and `w` for membership, accepts
  both when `E` is listed, and contains no symbolic tail. It still does not
  classify either contribution for subtraction.
- Attaching `PrefixLeft(source_weight(v), IDENTITY)` to an open view cannot
  activate the closed-filter executor: `candidate_zero_word_filters`
  (`candidate_context.rs:2647–2652`) requires
  `boundary.closed_weight == Some(weight)`. That condition is false for `v`.
  The owner returns `IdentityExhausted` via `exhausted()` before publishing
  checks. This is an internal validation counter-path, not a proposed source
  rejection or a run result. No wrapper is constructed here.

## Why context, fiber, and replay retention do not supply subtraction

| Existing owner | Actual bounded behavior | Missing fact/action |
| --- | --- | --- |
| `LocalWeight` / `AttachmentSet`, `candidate_context.rs:113–137,2174–2196` | Retains resolved operands, source owner/position, set grouping, polarity, scope and ordinals. Live left/right word arrays have length zero. | An executable attachment-local operation and its authentic contribution route. |
| `ContextExpr`, `candidate_context.rs:178–201` | Retains PrefixLeft, SuffixRightPops, Swap, BothFromRight, Replay and WithoutLeftFilter construction. | No current negative open-tail wrapper/consumer is supplied by these variant names. |
| Detached filter/algebra, `1089–1145,1487–1533,2200–2215` | Finite filter intersection and supplied count/ID operations; dormant unit PUSH can be materialized into a detached value. | No live bound, filter registration, subtraction/output projection, or gamma is produced. The adapter is prepared only for positive nonempty sets. |
| Closed-filter execution, `2744–2815` | Uses the true task lower, installs/replays a retained closed Allowance, then marks discharge. | Membership checks alone neither choose the local removable contribution nor connect an open negative tail. |
| `RelationKey`, `Origin`, bound admissions and fibers, `202–218,262–266,344–371` | Preserve endpoint/context and source derivation evidence separately from semantic membership. | The matching branch does not consume that evidence as a subtraction license. Retention is not an authorization theorem. |
| Replay, `candidate_extrusion.rs:763–802` | Reaches ordered opposite endpoint pairs using both bound inputs. | Repeating the membership consumer cannot introduce a missing attachment-sensitive residual transition. |

The ordinary and retained drain paths invoke context execution before dispatch
(`lib.rs:12057,12269`); `dispatch_live_item` (`12333–12347`) then applies the
Effect task unless the endpoint was consumed or memoized. On the open IDENTITY
case nothing intercepts the matching branch with an attachment classifier.
Different member endpoint pairs need not be memo-collapsed for the
discriminator to hold. The failure is in the consumer's supplied observation,
not an assumed global merge of identities.

The existing origin-to-fiber transport gap is already recorded by the separate
[recipe-delivery falsifier](2026-10-12-negative-recipe-delivery-falsifier.md).
This note neither repeats that attack nor claims the original origin data is
destroyed. Even fully paired origins would remain unused by this matcher.
`ReplayRecipe` is bound-evidence metadata, not a concrete residual recipe.
No live lineage-owned gamma/source-feedback/gamma-to-original-tail constructor
appears in the inspected owners. Distinct residual creations must retain
distinct constructor lineages despite equality of `p`, `E`, or current keys;
adding a source-row watcher cannot substitute for that identity.

## Exact blocker and next owner

Preflight (`candidate_source.rs:117–132`, reached by `shadow_apply.rs:92`)
and paired/general constructors (`candidate_effect.rs:1034–1070,1507–1509`)
still independently guard negative concrete rows. Those established guards are
context, not this note's repeated falsification target.

The unsupplied premise is an internal negative constructor and reached
consumer retaining the actual set/occurrence/scope, original tail coordinate,
and an operation that distinguishes the licensed contribution route from an
independent same-effect route. Its residual consequence must correlate heads,
exact context, original source, gamma and outgoing original-tail projection
under each separate constructor lineage. No complete output or contribution
survival theorem follows from successful Allowance membership.

One recommended next action: assign the bounded internal
`candidate_formal_effect_port` / `candidate_signature_effect` construction
plus `candidate_context_execute_relation` / `candidate_check_effect_operand`
consumer seam an exact contribution-local invariant, with the two same-`E`
origins above as its decisive discriminator. Keep public/source preflight
unchanged. Have the owning constructive lane derive the actual subtraction
and correlated residual obligations before implementing that seam. This
researcher has no compiler/test authorization or theorem-review authority.

## Checks, independence, coverage, and resources

Static source derivation only: bounded `cat`/`sed`/`rg` reads, read-only Git
baseline/status/branch inspection, in-memory SHA-256 comparison against
`git show eb2666f80:PATH`, and final note whitespace/link inspection. No
executable model or checker, seed/range enumeration, mutation execution,
build/test, Oracle execution, measurement, Git mutation, child launch, or
shared-record edit. Initial combined reads exceeded output capture; claims
use subsequent bounded owner reads. No exhaustive repository search is claimed.

Oracle independence: the reviewed frozen Oracle source derivation is an
external construction reference; current Y3 branch outcomes are derived
directly from its source, rather than copied transition assumptions. Both
descriptions presuppose resolved operands and completed named calls. Neither
establishes the other's source reachability or global semantics. The proposed
membership-as-subtraction shortcut is falsified statically under an explicit
local-authority premise; no checker assumes and then certifies that premise.

Coverage omits source-program reachability of the two-lower meeting,
arbitrary invariant type arguments (Y3's current operands are nullary),
positive weighted-payload normalization, weighted negative residual equations,
all insertion/transport paths, fresh-use/intrusion correctness, complete
Call/Catch/output projection, abnormal completion, soundness, principality,
termination and production admission. No original OPEN gate is closed.

Compute budget consumed: zero build/test/Oracle/probe/measurement processes;
only short read commands and one-process static checks. No explicit wall-time,
CPU/RAM limit was supplied in this packet; actual CPU/RAM and cumulative shell
process counts were not instrumented. Writes stop at frozen handoff; a fresh
independent review remains primary owned.

## Commit packet

- Exact lease: `notes/progress/2026-10-12-negative-filter-source-falsifier.md`.
- Baseline: `eb2666f80c56ebb1500fc2e359774581c79b2ffb`.
- Dependency changes: none; complete-byte hashes below equal the baseline.
- Claim/review: unreviewed bounded source discriminator, conditional failure
  of the membership-as-subtraction shortcut; no runtime/language bug claim.
- Checks: narrow source inspection, baseline/hash equality, note whitespace
  and relative-link checks. No tests/builds/Oracle.
- Proposed message: `research: distinguish local negative subtraction from Allowance membership`.
- Shared deltas left for primary/curator: link the contribution-sensitive
  discriminator; retain missing authentic route classifier, executable
  negative continuation and separate-lineage correlated residual construction
  as OPEN. `tasks/current.md`, theory/index/authority files and questions were
  intentionally untouched.

### Frozen dependency SHA-256

All complete-file hashes equal the pinned baseline bytes.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-12-oracle-negative-stack-filter-source-proof.md` | `b34465d7132259284389eb04507705239b46b40d6788f70567f3f58447689133` |
| `notes/theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md` | `1a58d1134091e0b91acaf8014baca3a43f72b7764889ff15bbb3c382cd6245e6` |
