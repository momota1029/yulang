# Copied Allowance activation: bounded static falsification

Status: reviewed research-only source-owner characterization; fresh M2
`compiler_referee` found no findings on the paired bounded artifacts. No
authenticated source-qualified counterexample and no all-path activation
theorem. H1/H2/U remain OPEN; H3/P remain disabled. Production/F5 gates remain
separate.

Baseline: `d8a6209c1dc181858948c4d811259aa20683d64e`, branch
`research/simple-sub-intrusion`. Exclusive output lease: this file only.
Method: independent static adversarial trace of physical bounds, source/copy
links, relation transport, queued work, drain completion and residual consequences.
The constructive proof and concurrent test fixture were not read.

## Objective and fixed premises

The original parent still covers every originally admitted shallow Catch under
one scoped sigma, preserving consumed, protected, unmatched, outside-arm and
raw-resumed contributions and complete dependent interfaces. This packet attacks
only the H2 activation seam identified in
`notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md` §6; it does
not change eligibility, source admission, protection or intrusion qualification.
The reusable native primitive is the reviewed
`notes/theory/2026-10-14-native-handler-residual-cut.md` §§3–4, conditional on
its stated successful-processing premises. Top-level inference principles
§§1–5 and §1.1 retain ordinary accumulation/propagation and only necessary
abnormal-path safety.

Notation: `s <= A(v)` has concrete head set J and tail gamma. Positive
extrusion to target level l maps selected lower bounds; negative extrusion maps
selected upper bounds. Primes denote actual outputs of one operation-local
map, not arbitrary rows satisfying similar equations. A view ID is not
canonicalized by row equality.

## First decisive transition and owner crosswalk

All code locations below refer to the pinned baseline, whose line numbers differ
from some historical note citations.

| Transition / owner | What the source establishes | What it does not establish |
| --- | --- | --- |
| `candidate_extrusion.rs:89–179`, row Visit | A too-young positive row copies its selected lowers; the original gets an upper link to the copy. A negative row copies selected uppers; the original gets a lower link from the copy. Positive gamma visitation schedules incoming cuts and positive source visitation. | Inserting the one-sided link does not itself replay existing opposite bounds. The link is neither equality nor an executed composition. |
| `candidate_extrusion.rs:295–327`, IncomingAllowance / Bound | Installs the reconstructed bound and transfers its actual source fibers/origins. | No direct replay operation for its existing lower/upper Cartesian product is created at these calls. |
| `candidate_effect.rs:563–603`; `candidate_context.rs:3403–3417` | Bound transport creates a child relation, Transport dependency, evidence transform and bound attachment. The origin-table pass explicitly marks `MissingOriginAssociation`. | A Transport dependency is not a typed task or a receipt. That coverage gap alone is not a lost semantic consequence. |
| `candidate_extrusion.rs:409–573` | Insertion journals storage, registers Allowance-tail capture incidence, marks intrusion dirty and emits bound evidence. | Dirty marking is not blanket replay of all copied bounds. |
| `candidate_intrusion.rs:297–315`, finish extrusion | Records the actual comparison/output PairGroup and parent span. | No internal copied-cut traversal. |
| `lib.rs:12469–12516`, structural Value branch | Calls extrusion for a structured non-row endpoint against a row, at the receiving row's level, and queues the rewritten Value comparison. | A hand-built row scenario that never passes this branch is not a source-qualified witness. The rewritten root alone does not enumerate every internal effect pair. |
| `candidate_extrusion.rs:766–809,843–867`, ordinary effect admission | Installing a new lower or upper calls replay against the live opposite side. | This owner is distinct from initialization by bare insertion. |
| `candidate_context.rs:3131–3212,3280–3344`; `lib.rs:12283–12336,12378–12393` | Replay forms actual relation children from new/old fiber quadrants; ordinary driving queues owned children. The typed drain executes context and dispatches Effect work. `Queued` leaves completion with that drain. | A replay handle, a queued child and a drained child are different evidence states. Empty-worklist processing cannot consume an uncreated task. |
| `candidate_intrusion.rs:519–624`; `lib.rs:12283–12315` | Qualified equality transfers both bound sides, splices incidence, canonicalizes bound fibers, and explicitly replays merged lowers against uppers. The drain settles pending intrusion when its queue is empty. | Unqualified copies do not become equal merely because row endpoints form a convenient graph. Distinct view IDs are not merged by this equality. |

Thus bare copied-bound insertion is the first unsupported *direct activation*
step. It is not yet a missing-consequence step: the original graph and copied
gamma must be checked before claiming a counterexample.

## Concrete-current-lower attack: a rejected false witness

The following is a conditional source-code derivation, not a claim that these
hypotheses have been authenticated for every source history. Assume:

1. `s <= A(v)` and concrete Contribution endpoint q are live, with q a current
   selected exact lower of s; the relevant paths have identity context.
2. Original processing of q against A(v), including its forwarded task, has
   completed before the selected-bound snapshots used in this extrusion.
3. Gamma is positively visited in the same finite successful extrusion that
   reconstructs the incoming cut; no output of a discarded attempt is used.

If `effect(q) in J`, the original concrete consumer succeeds and the copied
view retains J. There is no residual q-to-gamma obligation in this case.
Otherwise `candidate_effect.rs:985–1019` forwards the identical q endpoint to
gamma. Ordinary admission makes q an exact gamma lower. Positive gamma
extrusion selects that bound and `Work::Bound` inserts q as a lower of gamma'
because a Contribution has no remapped row or view. Positive source extrusion
also preserves q. If gamma needs no copy, its already-admitted q remains.

Therefore the smallest proposed witness consisting only of this saturated
identity Contribution, a copied source and a copied open Allowance fails:
q reaches gamma' through the original residual followed by selected-lower
copying, even without executing the direct copied pair `q <= A(v')`.
This proves endpoint-level residual coverage under the three hypotheses; it
does not prove equal contextual fibers, diagnostic ancestry or full dependent
consequences. It also does not assume arbitrary models choose the least gamma.

AnnotationMember needs the additional operation-local remap argument; Support
needs member expansion plus its symbolic tail. They are not silently included
in this Contribution derivation. A negative source copy initially selects only
uppers and creates no copied current lowers by that Visit alone, so populating
it with an arbitrary pre-existing q is another invalid minimal witness. Later
admission into that row has a different replay owner.

## Later-lower and upper controls

For one later concrete lower admitted through ordinary
`candidate_apply_effect(q, s')`, with the copied Allowance already stored,
`candidate_replay_bound` enumerates that upper. Under successful relation replay
and typed drain, the actual consumer either consumes q by J or forwards it to
gamma'. This is a control on the real admission owner, not a result of merely
appending a lower to physical storage. A later lower on the original s can
also meet its retained one-sided copy link; the resulting task must still be
queued and drained before treating that route as executed.

A gamma' upper admitted after q has been copied meets the current q lower
through the same replay owner. If an upper is already stored when a forwarded
q is ordinarily admitted, the insertion of q meets that upper. Positive gamma
copying selects lowers, so it is invalid to assume that every original upper
is simultaneously installed on a fresh positive gamma' by that operation.
Where qualifying equality later introduces/combines uppers, its explicit replay
provides a separate owner. These controls do not establish that a current q
installed by bare copy initialization meets every already stored contextual
upper in all histories.

Canonical row equality cannot justify deleting either cut: the view endpoints
remain distinct. Its replay can supply a missing direct comparison only when
the actual recorded occurrence qualifies and equality really executes. A
counterexample must exclude that route, not merely omit it from a diagram.

## Exact remaining obstruction

No source-qualified witness was established. A convincing negative result
must authenticate the structural Value admission and then show, after actual
owner completion, that a necessary consequence is absent from *both* the
copied pair and all original-source/gamma/link routes. The static reading here
does not provide that completed native trace.

The first uncovered positive premise is a commuting argument for a remapped
current symbolic lower, its original residual processing, and positive gamma
copying, including the exact relation contexts and worklist interleaving. If
original forwarding is pending at the snapshot, its eventual gamma admission
may replay the retained original-to-copy link; this is a live alternative,
not a proven universal repair. If original forwarding has completed, copied
selected bounds may already carry the full consequence. Neither alternative
alone proves all symbolic/contextual cases. Transport ancestry proves neither
activation nor semantic equivalence of those routes.

Rollback/retry was not used to manufacture a witness. The derivation excludes
discarded outputs and makes no full rollback-restoration claim. All-history
memo validity, suspension resumption, publication barriers and general
termination remain unverified. No new semantic relation or source restriction
is proposed.

One recommended next action: obtain the smallest authenticated native trace
through structural Value dispatch with a remapped Support/symbolic-tail current
lower, recording original forwarding, source/copy links, gamma' lower/upper
state and actual replay receipts at drain completion. Discriminate the original
already-forwarded and pending-forwarding orders in that same owner-level
question; do not repeat the identity Contribution toy scenario as a purported
counterexample.

## Dependencies, checks and resource envelope

All semantic source reads used the pinned revision with `git show` after initial
owner discovery. Read-only `git diff --quiet` confirmed that the five code
dependencies below, the primitive note and top-level principles still match
the baseline. The H2 lineage note has a concurrent review-status-only delta:
baseline blob `9f922c2b1bbba95d69ee6c9ade87d3fddb9a92db` to inspected live blob
`391d727fc1edafba9b94e889aacbc305089947c8`. Its §6 activation statement is
unchanged. This artifact does not certify that delta or adopt another worker's
proof output.

Pinned dependency Git blob IDs:

```text
7c69b87365e9f11676b8fd6357b7dc4b0d507ece  crates/yu-solver/src/candidate_context.rs
f0536987d66b817c774dae63e51c0e7bde0ca279  crates/yu-solver/src/candidate_effect.rs
bca94731da261ec4e002a3a856e20095355c4c50  crates/yu-solver/src/candidate_extrusion.rs
168fa19bca6f12ed2d29f50242939fa4edc5fa5d  crates/yu-solver/src/candidate_intrusion.rs
7f40fc4e1aa74720ef857134412f08d3b40e633a  crates/yu-solver/src/lib.rs
45e7ea496e92145ef00e94e6adb370ebca3d7790  notes/theory/2026-10-14-native-handler-residual-cut.md
ad10d6f8188325e666121b400686e4fb5682d10f  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

Checks: bounded `rg`, `sed`, pinned `git show`, branch/HEAD reads,
`git diff --quiet`, `git ls-tree`, `git hash-object`; static text inspection.
No Cargo/build/test, probe, measurement, mutation testing, model execution,
source program, seed/range enumeration, Git mutation or child launch. Initial
overbroad context output was truncated; it supplies no claim of full coverage
of task histories. No independent executable oracle exists in this packet:
the code is the inspected operational owner, and the primitive shares its
successful-processing/context premises. CPU, peak RAM and exact elapsed time
were not measured; one static leaf under the requested 15-minute cap. Requested
role: researcher at configured normal settings, with no override. Observed
effective model/effort: unknown; no runtime metadata was exposed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-extrusion-current-cut-activation-falsifier.md`.
- Baseline SHA: `d8a6209c1dc181858948c4d811259aa20683d64e`.
- Changed dependencies: only the H2 lineage note's inspected review-status delta
  and Git blob hashes above; governing §6 and code unchanged.
- Claim/review status: fresh M2 `compiler_referee` reviewed the paired bounded
  artifacts with no findings. This remains a static characterization with
  conditional Contribution coverage; no authenticated counterexample or H2
  closure.
- Checks already run: static owner/call-path reads and narrow baseline/dependency
  checks listed above; no executable verification.
- Proposed commit: `research: bound copied Allowance activation falsification`.
- Shared deltas left for primary/curator: retain H1/H2/U OPEN and H3/P disabled;
  record rejection of the saturated identity Contribution false witness and the
  exact symbolic/contextual commuting premise. No shared records were edited.

Writes stop at handoff; primary owns review adjudication and integration.
