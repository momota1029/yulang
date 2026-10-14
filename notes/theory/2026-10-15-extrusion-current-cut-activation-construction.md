# Copied native cuts: activation and parent-link factorization

Status: reviewed bounded source derivation with an unresolved operational
lifting premise; fresh M2 `compiler_referee` found no findings on the paired
artifact. No theorem, H2/U, implementation or production promotion.
Baseline: `d8a6209c1dc181858948c4d811259aa20683d64e` on
`research/simple-sub-intrusion`. Exclusive lease: this file only. Leaf.

## 1. Frozen statement and authority

The original H2 parent still quantifies over every originally admitted shallow
Catch H and one original scoped assignment sigma, with its original scrutinee,
operation/value-arm binders, provider and dependent interfaces. Protected,
eligible consumed, unmatched, outside-arm and raw-resumed contributions retain
their original meanings and scopes. No marginal witness is chosen separately.
H1/H2/U stay OPEN; H3/P stays disabled; F5/production remains separate.

This packet asks the following narrower structural question. For every finite
successful native extrusion/capture/fresh-use/qualified-intrusion route, every
reconstructed cut `s' <= A(v')` installed by `Work::IncomingAllowance` or
`Work::Bound`, and every current physical lower `q'` of its canonical source
`s'`, does the actual owner activate `q' <= A(v')`, or establish all of that
comparison's consequences by another actual route before dependent result use
or publication? The alternatives include symbolic continuation and retained
contextual obligations, not just the nominal concrete support currently seen.
Here `A(v)` is native Allowance(view ID v); `g=t(v)` is its optional tail;
`R+(x)` and `R-(x)` denote the operation's actual level/polarity row or structural
map, with its one shared `(old view, mapped tail)` view map. They are not new
compiler relations. Distinct constructor view IDs and actual origins remain
distinct throughout this question.

Hypotheses are valid live handles, successful named operations, existing level
and genericity boundaries, only actually qualified parent/copy equalities, and
successful completion of work actually emitted. None asserts emission of all
required comparisons, a closed input worklist at extrusion entry, or a complete
source Catch correspondence. Arbitrary-context termination, rollback, suspended
continuation completeness, complete Call, full effect hygiene, soundness and
required principality are not supplied by this packet. No ordinary inference
restriction or protected-gamma exception is introduced.

Exact authority: top-level inference principles §§1–5 and §1.1; contextual
residual lineage selection, **Selected policy** and **Preserved contract and
open obligations**; attachment/admission §§3–4; intrusion value/type association,
**Approved extrusion-event qualification**. Native-handler-residual-cut §§3–4
provides the independently reviewed plain native consumer under its explicit
processing premises. Native-residual-view-lineage-lifecycle §6 fixes this seam;
its structural retention result is reused, not re-proved as operational closure.
The proof-economy audit below follows compiler-engineering, **Natural compiler
behavior and proof-obligation economy**.

## 2. Actual construction and distinct operational states

All source locators below are in `crates/yu-solver/src/` at the pinned baseline.

| State | Actual owner and what it establishes |
| --- | --- |
| Stored bound | `candidate_extrusion.rs:409–570` canonicalizes endpoints, appends one physical selected side, registers capture incidence, marks intrusion dirty and emits evidence. It does not enumerate opposite bounds. |
| Attached transported relation | `candidate_effect.rs:563–602` walks original bound fibers and origins. `candidate_context.rs:3403–3416` attaches a relation with retained post-check context/source association and Transport dependency/evidence. This does not queue its task. The separate origin table explicitly records `MissingOriginAssociation` at effect:592–598; no origin-to-fiber bijection is assumed. |
| Pending replay | extrusion:766–806 enumerates the live opposite side and calls context:3131–3213. Each new fiber quadrant retains both ordered parents and exact input BoundKeys; children belong to a retained ReplayOperation. |
| Queued activated comparison | context:3310–3325 hands a typed item with its relation/replay acknowledgement to `enqueue_item`; `lib.rs:12894–12914` transfers ownership and appends the item. Stored bounds and attached relations have no such queue transfer by themselves. |
| Executed comparison | `lib.rs:12072–12119` pops the item, transports its relation and executes its context before dispatch. Effect dispatch at 12389–12404 reaches `apply_effect_task` at 11735–11743 and native effect admission. Identity context returns to ordinary dispatch; zero-word filters have a separate executable owner at context:2964–3032. |
| Fully drained comparison/consequences | context:3331–3343 distinguishes Complete from Queued. Queued explicitly leaves completion to the outer consumer. Receipt ownership and child continuation are at context:3232–3277. No global publication proof is inferred from these local transitions. |

For a row x above target level l, Visit snapshots its selected side before
installing the one-sided link (extrusion:98–125). It allocates a fresh row copy,
records the actual occurrence parent, and maps each selected old bound through
the same polarity/l target map (126–164). In inequality notation the links are

```text
positive traversal: x <= R+(x), stored as an upper on x
negative traversal: R-(x) <= x, stored as a lower on x.
```

They are installed by `candidate_insert_bound`, not `candidate_apply_effect`.
The snapshot deliberately excludes this newly installed link from the selected
side traversal. A row already at/below l is reused without traversing its bounds
(extrusion:90–95). No endpoint canonicalizer replaces a native view ID.

Positive gamma copying visits every recorded incoming cut and visits its source
with positive polarity (extrusion:166–178). `IncomingAllowance(g',v,source_key,old)`
then installs `R+(s) <= A(R(v,Some(g')))` and transports the old cut's fibers and
origins (295–309). The ordinary selected-bound route installs its mapped bound
and transports its old evidence (310–330). Both are stored/attached states in
the table above. No replay operation is allocated there. This is an exact
construction fact, not yet a lost-effect counterexample.

`finish_candidate_extrusion` (intrusion:297–315) records output/PairGroup
association. It does not cross the copied cut with its source lowers.
Structural Value dispatch calls this extrusion on a Function-to-row or
row-to-Function comparison, then queues its rewritten **Value** comparison
(`lib.rs:12465–12512`). This reaches the production native entry seam; it is not
evidence that every internal effect cut was queued. Ordinary worklist exhaustion
calls `settle_candidate_intrusion` (`lib.rs:12047–12075`). With no pending
qualified pair, intrusion:496–498 clears dirty and returns; dirty is not an
unconditional copied-bound replay queue.

## 3. What original links actually explain

The lack of a local replay call is insufficient to refute the requested
disjunction. In particular, the following nominal subcase has a constructive
factorization through gamma's already accumulated lowers.

Fix one actual positive gamma-copy operation, one old open cut `s <= A(v)`
with tail g, and one original atomic lower q (Contribution or AnnotationMember)
whose original comparison was processed plainly and forwarded unmatched q to g.
Assume that forwarding has already physically installed q as an exact lower of
g when g's selected-side lengths are snapshotted. No claim that every original
comparison is already in this state is made.

1. The original atomic consumer uses q's resolved effect identity and the old
   view's allowed heads. Nonmembership queues **the same q endpoint** to g
   (effect:985–1014). Successful ordinary admission makes it a lower of g
   (extrusion:853–866).
2. Positive copying of g enumerates that physical exact lower, schedules
   Visit(q,+,l), and installs its result `R+(q)` as a lower of g' by Work::Bound
   (extrusion:98–164,310–330).
3. A Contribution is unchanged by structural traversal. An AnnotationMember's
   mapped view uses the operation's common view map; a source occurrence of
   that same old view and mapped tail uses the same mapped member endpoint
   (extrusion:182–209,260–293). This does not identify it with a member from a
   different old view. Thus the already forwarded lower and its copied source
   occurrence agree on the mapped atomic endpoint where their map keys agree.
4. Any subsequent ordinary upper admission on g' replays that stored lower
   against the upper (extrusion:843–866,766–806). Its actual comparison goes
   through the queue/consumer chain in §2. A qualifying equality or fresh-use
   restoration provides another explicit activation route, described in §4.

Therefore an already accumulated atomic residual lower can survive without an
explicit new `R+(q) <= A(v')` replay. Matching atoms require no residual task
in the plain consumer. This is a conditional nominal factorization, not a
complete contextual replay theorem, not proof that g was drained before
copying, and not a claim that arbitrary valuations equal a least residual.
If original forwarding is merely queued, the new upper link `g <= g'` can also
receive later ordinary lower admission on g; its consequences require that
admission's actual replay and drain. Storage of the link alone proves neither.

The universal lifting attempt stops at a different step. For a current symbolic
lower `R+(x)` of `R+(s)`, original processing may retain `x <= A(v)` rather than
an atomic lower of g. Positive copying x traverses its **lowers**, while that
Allowance is an **upper**. Incoming incidence can reconstruct
`R+(x) <= A(v')`, but reconstruction returns to the same stored-bound seam.
An original Support(w) likewise expands to all AnnotationMember(w,k) tasks and
its original symbolic tail task (effect:960–981); its mapped Support can contain
the mapped tail, whose complete future checking is not proved by copying the
currently forwarded atoms.

Neither `x <= R+(x)` nor `s <= R+(s)` reverses this direction. Merely composing
the original cut, positive source/tail links and old forwarding facts cannot
establish the operational comparison of the copied symbolic coordinate with
the copied Allowance. Even the nominal implication

```text
s subseteq J union g, s subseteq s', g subseteq g'
    implies s' subseteq J union g'
```

is false: take s=g=g'=empty, J=empty, s'={E}. This only refutes that proposed
link-only inference. It is not a valuation of the complete native graph, which
also stores the target cut, and is not an executable or source-qualified
counterexample. The missing matter is whether its obligation is activated or
otherwise fully discharged, not whether its stored syntax exists.

For nonidentity contexts, the retained original and mapped fibers must also
produce the same required ordered Replay consequences. An attached Transport
child carries `post_check_context(parent)` and source association; it is not
itself a Replay child for the new lower/upper pair (context:3407–3415 versus
3175–3191). Equating endpoint support or pointing to old Transport evidence
does not establish those contextual consequences. This is the first unsupported
transport/activation premise; no further equivalent lifting is attempted here.

## 4. Routes with an explicit activation owner, and their limit

Ordinary later lower insertion on a cut's actual source stores the lower and
calls `candidate_replay_bound`; each retained Allowance is an opposite endpoint
(extrusion:843–866). Ordinary later gamma-upper admission similarly encounters
its current lowers. This is a control for future admissions, conditional on
processing the emitted work; it does not retroactively emit a missing old pair.

Capture itself is nonexecuting: expanding local gamma follows incoming cut
incidence and enumerates both bound sides (scheme:645–695). Fresh use has a
separate owner: every captured bound goes through `begin_candidate_fresh_bound`
and `candidate_drive_bound_restoration` (scheme:993–1004,1253–1298). Restoration
records the opposite count after inserting the new bound, reads each live
opposite endpoint, starts a replay with incoming-use provenance, and requires
its completion before advancing (extrusion:662–763). For any opposite pair
present within that restoration's saved count, this is a real activation path;
which current pairs are present at a particular step depends on restoration
order and other accepted operations. It does not prove an earlier extrusion
was activated before its first dependent use. Shared old anchors and successful
later freshening must not be assumed to repair every earlier route.

Actual qualifying intrusion has another explicit owner. For distinct row
representatives it transfers both bound sides/origins, canonicalizes context
bound keys and replays every merged lower against merged uppers
(intrusion:518–609; context:3346–3364). That covers copied cuts in those merged
source rows, preserving each A(v') endpoint. Qualification is the original
source Value occurrence/SCC rule; no universal merge is assumed. Merging only
a tail establishes replay on that tail, not an unperformed Cartesian replay on
an unrelated source. The equal-representative early return at intrusion:532–534
is also not a general new replay operation. These cases retain the required
parent/copy rule without using it as an unconditional activation hypothesis.

## 5. Minimized obstruction and proof economy

Unproved premise, at its owner: after selected-side copy construction and before
dependent rewritten-Value use/publication, for every current copied-source
lower and every reconstructed Allowance, emit/complete their actual contextual
comparison **or** supply a source-established lifting argument for all its
symbolic, origin and contextual continuation consequences. The responsible
seam is `candidate_extrude`'s copied-bound initialization and its actual
dispatch/completion owner. It is not the concrete Allowance membership branch.
The proven atomic factorization explains why absence of a direct replay call
alone is inadequate evidence of failure. The all-symbolic/context lifting
premise remains unsupported in this static pass.

The previous lineage induction and this parent-link/consumer factorization are
different methods that leave that same premise open. Apply the existing audit
now: it is A/B when required for accepted inference, while inferring completed
operations from retained bound/Transport syntax would be D reconstruction debt.
The owning constructor knows exactly what it emitted; retain or observe that
operation fact there rather than add another proof-only meaning to a stored
bound. This audit neither adopts an implementation change nor reclassifies H2
away. A third equivalent conditional lemma or larger nominal case count would
not advance the premise.

One next action: primary consume its separately owned exact structural-dispatch
observation at this owner, discriminating an already forwarded atomic lower
from a current symbolic-tail lower and retaining actual Replay/queue/drain
receipts or an independently established full consequence route. Adjudicate
that evidence before authorizing any construction change. No fixture or other
worker output was read in this leaf, and no proposed probe is reported as run.

## 6. Frozen dependency/check and commit packet

Checks performed: read-only HEAD/branch/status reads; bounded rg/sed/nl/cat of
the named owner ranges and governing sources; direct-dependency SHA-256; exact
dependency diff against the pinned baseline. No code/test edits, executable
probes, Cargo/build/test processes, Git mutation, delegation or measurement.
One proof leaf; lightweight source commands only. Assigned wall cap: twenty
minutes. CPU, RSS and proof wall elapsed were not measured and are unknown.
Requested runtime: normal Sol/high leaf, no Astra escalation. Observed effective
model/effort: unknown; no runtime metadata was exposed. Configuration declares
the prover and Sol/high defaults and leaves its role model/effort unpinned;
that inspection does not establish routing, inheritance or hot reload.

The source/design dependencies below matched the pinned baseline. The live
lineage note changed only its review-status prose relative to that baseline;
§6 and its technical premises were unchanged. Baseline content is the technical
input; the delegator supplies its accepted reviewed status. No concurrent
test-only fixture or falsifier/researcher output was consumed.

```text
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 candidate_extrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 candidate_effect.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 candidate_context.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e candidate_intrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd candidate_scheme.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 lib.rs
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89 notes/design/2026-10-12-intrusion-value-type-association.md
```

Bare source filenames in this table are relative to `crates/yu-solver/src/`.
Lineage note SHA-256: pinned baseline
`49648bac23f5ad6796ce408640371839eb34258b383422568556700a12f818f0`;
live reviewed-status text
`1781952afd258038345ba2dbe5a3c425bc193a04c7d77c72b2eb52a636466822`.
Artifact trailing-whitespace search returned no matches and its terminal byte
was `0a`. Fresh M2 `compiler_referee` reviewed the paired derivation/falsifier
with no findings. The review covered bounded static claims only; it did not
inspect or certify the primary-owned executable observer.

Commit packet: exact leased path
`notes/theory/2026-10-15-extrusion-current-cut-activation-construction.md`;
baseline `d8a6209c1dc181858948c4d811259aa20683d64e`. Changed production/design
dependency hashes: none. Changed lineage dependency: review-status prose only,
as described above; technical source snapshot unchanged. Honest status:
reviewed conditional atomic factorization plus unresolved universal symbolic/
context activation bridge. Fresh M2 `compiler_referee` found no findings on the
paired bounded artifacts. The primary-owned finite structural-dispatch
observer is separate evidence and does not close the activation premise.
Checks already run: static owner/consumer trace, baseline/dependency equality
and hashes; no executable verification by the producer.
Proposed checkpoint message:
`research: trace copied-cut activation and bound parent-link factorization`.
Shared-record deltas for primary/curator: retain H2/U OPEN and H3/P disabled;
record the atomic gamma-lower factorization and the exact remaining symbolic/
context lifting premise at copied-bound initialization/dispatch. No shared
record was edited by the producer. Primary owns review adjudication and shared
synchronization.
