# Negative recipe delivery: source transport falsifier

Status: independently reviewed bounded source obstruction and conditional
delivery characterization; no theorem, implementation gate, or source admission
is closed.
Producer: primary-assigned researcher leaf; no delegation.
Baseline: `0df10df944c0289a96b6c743aee474ccd55493de`,
`research/simple-sub-intrusion`.
Exclusive lease: this file only.

## Objective, authority, and method

Attack the premise that ordinary lower × upper replay already supplies every
current/future residual-recipe delivery, with authentic admission/fiber/origin
pairing and separate constructor lineages. Static inspection follows the Effect
owners only. A proposed `RecipeId` upper endpoint is an unverified candidate,
not selected authority or an existing endpoint.

Governing contract:
[contextual attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6 (including §3.1),
[residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
“Selected policy” and “Preserved contract and open obligations”, and
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and “Authority and integration”.
Successful-path propagation and pairing remain required. No unconditional
abnormal restoration obligation is introduced.

The exact
[Oracle negative bridge](../theory/2026-10-12-oracle-negative-stack-filter-source-proof.md)
§§F/R and
[Y3 constructor bridge](../theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md)
§§4–6 delimit the input: Oracle's completed filter/lower owners establish only
their named event induction; its residual branch has two actual emissions.
Neither supplies Y3 recipe construction or its delivery. Y3's negative concrete
preflight/constructor guards and absent residual consumer remain OPEN premises.
This audit does not repeat that constructor attack, inspect the Value graph,
consume pending questions, or select language meaning.

## Decisive source obstruction: transport does not retain the pairing

The candidate claim falsified here is narrow:

> Each completed existing bound transport authenticates its destination
> origin/admission against the specific transported source fiber.

Hypotheses: an initialized candidate session, a completed call to
`candidate_transfer_bound_origins(from,to,reason)`, a source origin entry and
source relation fiber, valid IDs, and successful allocations. This is a
source-owner conditional obstruction, not a source-language counterexample.

At `crates/yu-solver/src/candidate_effect.rs:563–574`, transport visits every
source fiber and calls `candidate_context_transport_witness_with_evidence`.
At `candidate_context.rs:3182–3195`, that owner snapshots the specific source
relation, constructs a child from its post-check context, retains a Transport
dependency and a FiberTransform, and attaches the child. However,
`candidate_context.rs:589–595` unconditionally marks that transform with
`MissingOriginAssociation`.

The second loop, `candidate_effect.rs:584–598`, visits origins separately.
The code explicitly uses `relation = None`, snapshots `from`, adds
`MissingOriginAssociation`, and creates a destination admission through
`candidate_bound_origin_with_evidence`. It never supplies the transported child
or source admission ID to that call.

The exact resulting omission follows from
`candidate_context.rs:508–519`: `snapshot(from,None)` has no group, no admission
head, and no emission head. Its coverage additionally records
`MissingBoundRelation`, `MissingBoundGroup`, `MissingAntecedent`, and
`MissingPhysicalEmission`. A target admission can exist without a retained
antecedent identifying which source admission/fiber it transports.

This does **not** assert that the original information is globally destroyed.
`BoundAdmission` at `candidate_context.rs:344–347` already retains
`(bound,origin,relation,cause)`; `admit` at 530–573 groups admissions by
`(bound,relation)`. The gap is at this transport consumer, which uses the
independent origin table rather than that association. Evidence is explicitly
inert, so this finding is not a demonstrated runtime typing bug.

### Smallest witness and ambiguity enlargement

The smallest structural witness needs one admitted source bound and one
transport; no recursion, two recipes, or endpoint equality is needed:

```text
source admission A: (bound=b, origin=o, relation=f)
completed transport b -> b':
    retain f -> f' through FiberTransform (origin association marked missing)
    retain destination admission A':
        origin=o
        cause=BoundTransport(snapshot(b,None),reason)
        snapshot.admission_head = None
        snapshot.emission_head  = None
```

Thus A' does not establish “A transported with f to f'”. Choosing a context
from the current processing parent or reconstructing one from o cannot supply
that missing association. This follows directly from reached owner statements,
without assuming a checker transition system.

The smallest ambiguity enlargement uses two distinct fibers and two origins
on b. Histories pairing `(o1,f1),(o2,f2)` and
`(o1,f2),(o2,f1)` have the same two marginal collections. The transport's two
separate loops cannot choose their pairing from those collections. Original
admission records can distinguish the histories; a prospective delivery consumer
must use them or preserve an equally authentic association. This abstract
ambiguity is conditional on such histories being constructed; source reachability
of both histories was not proved.

## What ordinary replay actually covers

| Event / owner | Bounded enforced behavior | Missing premise for recipe delivery |
| --- | --- | --- |
| Physical insertion: `candidate_extrusion.rs:406–567` | Canonicalizes owner/item; creates a bound admission before physical emission; attaches the resulting relation; records exact physical slot. | Insertion alone does not call replay or install a residual consumer. |
| Ordinary effect application: `candidate_extrusion.rs:840–863` | Uses selected level orientation, inserts, then replays existing opposite physical bounds. | A live recipe upper and authentic receiver/context mapping do not yet exist. |
| Fiber-only registration: `candidate_context.rs:2776–2795` | Existing closed Allowance receives another origin/fiber followed explicitly by `candidate_replay_bound`. | This is one completed owner, not a general scheduling property of attachment. |
| Fiber attachment: `candidate_context.rs:2409–2421` | Adds a distinct RelationId to the bound's persistent prepend list; duplicate RelationId adds nothing. | No replay/worklist notification occurs in this function. Any additional caller must supply the trigger. |
| Extrusion: `candidate_extrusion.rs:121–124,293–323` | Retains actual parent/copy provenance; inserts selected copied bounds and incoming Allowances; transfers fibers and origins. | Copied-bound branches do not themselves invoke opposite replay, and transport has the pairing gap above. No all-path post-extrusion delivery result follows. |
| Capture: `candidate_scheme.rs:520–564` | Enumerates each retained relation fiber; captures a relation-specific snapshot and retains orientation/source bound. | Capturing bound fibers is not capture of an absent residual-recipe graph or authentic recipe lineage. |
| Fresh restoration: `candidate_scheme.rs:1221–1266`; `candidate_extrusion.rs:659–760` | Attaches a mapped relation/bundles, inserts the bound, retains a restoration handle, and visits saved-count/live-index opposite bounds with `incoming_use=true`. | Must establish the consumer and source/mapped admission association; `FreshUse` evidence also flags `ReplayUseAntecedentsNotRetained` at `candidate_context.rs:545`. |
| Intrusion: `candidate_intrusion.rs:477–486,548–604` | Only actual recorded parent/copy pairs in one SCC merge; transfers both physical sides; canonicalizes third-owner fibers; replays all canonical lowers against uppers. | Origin transport has the same gap; recipe identity cannot be inferred from the equal source/gamma coordinates. |

The restoration count is saved at insertion, while its indices and
representatives are read live. Later appended opposite bounds require their own
completed propagation events. Their coverage is not a consequence of that
saved count alone.

For ordinary replay at `candidate_context.rs:2911–2988`, assume persistent
prepend lists, old cursors remain reachable, valid replay heads, successful
owner completion, and an actual call after changes. If L0/U0 are old fibers and
ΔL/ΔU are newly attached fibers, the two loops generate:

```text
ΔL × (U0 ∪ ΔU), then L0 × ΔU.
```

The quadrants are disjoint and contain precisely all new pairs. Replay retains
ordered lower/upper contexts, constructs `ContextExpr::Replay` (or identity
when both contexts are identity), and records both RelationId inputs and both
BoundKeys in `Dependency::Replay`. Existing exact dependencies are suppressed
on the ordinary route. This proves finite enumeration conditional on invocation,
not future-event scheduling, authentic admissions, semantic discharge, or
recipe delivery.

With `incoming_use=true`, old cursors are deliberately reset to empty and
existing dependencies are not suppressed. Repeated pair processing for distinct
scheme-use diagnostics is therefore intentional. Do not infer “one lifetime
delivery” from ordinary dependency deduplication or classify this behavior as a
bug without specifying whether semantic consequences or per-use diagnostics
are counted.

## Identity discriminator and precise remaining gate

`RelationKey` interns only `(pair,context)`
(`candidate_context.rs:2232–2249`). `ReplayRecipeId`
(`candidate_context.rs:312,612–621`) names an inert replay-dependency record;
it is not an approved residual constructor identity. The current Effect endpoint
enum (`lib.rs:755–768`) has no residual-recipe endpoint.

Conditional mutation witness: if two separately created residual recipes are
encoded with equal endpoints and equal context, with no lineage discriminator
in their consumer identity, relation interning returns the same RelationId and
ordinary replay uses the same dependency identity. That representation cannot
establish delivery to two distinguishable recipe owners. This does not attack
a fully specified `RecipeId` proposal: a distinct recipe-bearing endpoint could
discriminate them. It still needs proved transport, capture, restoration,
intrusion and consumer behavior; a fresh numeric ID supplies none of those
premises.

The parent current/future delivery gate remains OPEN. The decisive omitted
premise is authentic delivery of each source admission/fiber to each applicable,
distinct lineage consumer on every relevant completed mutation route. This
note supplies an actual transport obstruction and a conditional finite replay
lemma; it does not prove universal completeness or refute the approved language.

## Checks, resource use, and handoff

Four lightweight command sessions total: initial rule/status/baseline read;
combined context/source locator read; narrower authority/symbol read; one
retained Python inspection session. No builds, tests, executable transition
probe, Oracle run, Git mutation, temporary files, or child workers.
The large combined reads were truncated; conclusions use subsequent bounded
owner/section reads. No exhaustive file/call-site inventory is claimed.

One static method, no seeds, enumeration ranges, runtime mutations or timing
samples. CPU/RAM were not measured; command execution was lightweight.
The original 30-minute wall budget applies; elapsed inspection-session time and
static checks are recorded in the final handoff. Only the leased note was written.
Relative file links, final newline and trailing whitespace were checked.
No independent review has occurred. Writes stop before submission.

Oracle independence: this result reads actual Y3 producer/transport statements
and the existing bounded Oracle derivation; it runs no Oracle oracle.
Its conditional quadrant argument shares the actual list/head assumptions.
Those assumptions and a future recipe dispatch are not validated by a second
model, and no source transition is proved by assumed transition rules.

Unverified: concrete negative construction, residual operation semantics,
all caller/event coverage, source reachability of the two-history enlargement,
recipe graph capture/transport, reverse gamma feedback, normal complete drain,
soundness/principality, abnormal handling, and production cutover.

One recommended next action: resolve the authentic pairing seam by deriving a
transport/delivery operation from the retained source admission group and its
specific RelationId; then require the proposed recipe consumer to name that
operation at all four lifecycle owners before treating ordinary replay as its
delivery proof. Return any implementation/design packet to the primary.

### Frozen dependency hashes

All inspected direct dependencies were initially read at the clean pinned HEAD;
unrelated pending questions were left untouched. Recheck the hashes below before
integration; a live branch move itself does not establish invalidation.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-12-oracle-negative-stack-filter-source-proof.md` | `b34465d7132259284389eb04507705239b46b40d6788f70567f3f58447689133` |
| `notes/theory/2026-10-12-y3-negative-effect-construction-bridge-proof.md` | `1a58d1134091e0b91acaf8014baca3a43f72b7764889ff15bbb3c382cd6245e6` |

## Commit packet

- Exact completed lease: `notes/progress/2026-10-12-negative-recipe-delivery-falsifier.md`.
- Baseline: `0df10df944c0289a96b6c743aee474ccd55493de`.
- Changed dependency hashes: none observed during the bounded inspection;
  final hash recheck is reported with the handoff.
- Claim/review: unreviewed bounded source obstruction; conditional replay
  characterization; compiler-referee review found no findings in the assigned
  scope. Original delivery/implementation gates remain OPEN.
- Checks: source-owner reads, dependency SHA-256 recheck, relative links,
  trailing whitespace and final newline; no tests/builds/runtime.
- Proposed commit message:
  `research: locate negative recipe delivery transport pairing gap`.
- Shared-record deltas intentionally left for primary/curator: link this
  obstruction; record MissingOriginAssociation at the transport consumer,
  distinguish inert ReplayRecipeId from residual lineage, retain the all-event
  delivery gate OPEN, and route the authentic pairing premise to its owner.
  No task, theory map, index, design, or question file was edited.
