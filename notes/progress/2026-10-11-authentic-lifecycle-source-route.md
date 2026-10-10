# Authentic lifecycle source-route search

Date: 2026-10-11
Status: exploratory, unreviewed static source correspondence; frozen for handoff
Baseline: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`
Method: one bounded static constructor/consumer search; no compiler execution
Lease: this file only

## Objective and result

Find one source-owned route for private-suspension contract §7: an initially
certified component with certificate-dependent memo/completion and a published
member graph, followed by fresh-use restoration with an accepted bound and
multiple remaining products, followed by a late unsupported Function/swap
incidence in that same component.

**Bounded obstruction:** no inspected pinned constructor supplies the initial
authentic certificate or joins the independently available restoration and
Function-port producers to its dependent observations and published member
graph. The concrete blocker is at `candidate_context.rs:958–961`: retained-input
construction unconditionally adds `FilterObligationsUnavailable`,
`ProducerReadinessUnavailable`, and `DependentObservationsUnavailable`, and
returns `InputCompleteness::Incomplete`. This is a directly observed source fact
about that constructor, not an all-source impossibility theorem. An authentic
restoration prefix exists in prior source evidence, but it supplies no traced
late Function/swap event in the selected interval.

The requested full source candidate is therefore **not constructed**. A synthetic
certificate can exercise an eventual adapter, as §7 permits, but cannot fill
this source-authorization premise. No new certificate meaning, recognizer,
source acceptance, or supported-input restriction is proposed here.

Authority is the Authoritative
[`private candidate suspension contract`](../design/2026-10-11-private-candidate-suspension-contract.md)
§7, with §§3–6 fixing continuation, ordering, withdrawal, publication and
rollback; and
[`contextual attachment/admission design`](../design/2026-10-10-contextual-attachment-admission-design.md)
§§4–6. The accepted decisions preserve the two exact cycle classes, retain late
unsupported edges and exact obligations, withdraw old observations before
reuse, suspend privately, and leave production certificate creation disabled
until genuine recognition/readiness/filter/transport/observation evidence is
supplied. This note uses those decisions without reinterpreting the language.

## Owning source routes and the missing join

All code line numbers below refer to the pinned baseline, never a live worker
diff.

| §7 premise | Pinned owner and evidence | Remaining premise |
| --- | --- | --- |
| Source action order | `candidate_source.rs:240–270,282–303,344–363,549–575` schedules initializers before local installation, then published local Name uses through `Action::Local`; module Name uses choose open/internal or incoming routing. | No action emits an authentic cycle certificate. |
| Existing member graph | `candidate_scheme.rs:767–835` runs every SCC member's source schedule, captures every member into `staged`, and then fills `GraphState.graphs` together. | No certificate-generation dependency links those slots to observations. |
| Incoming source fresh use | `candidate_scheme.rs:872–887,1186–1232` requires the target member graph, captures its current live root, freshens it, routes the resulting Value, and retains a `FreshRoute` only afterward. | A published graph is an eligibility fact, not readiness or circuit authorization. |
| Local source fresh use | `candidate_scheme.rs:1264–1295` obtains the installed local root/boundary, captures the live scheme inside a route transaction, freshens it, links the use, and retains a `LocalFreshRoute`. | A `LocalScheme` is distinct from the SCC member `GraphState.graphs` publication slot. Local installation alone does not meet the published-member premise. |
| Single fresh-use identity and retained source evidence | `candidate_scheme.rs:903,927–938,1140–1179` creates one `context_use`, maps generic coordinates per use, preserves older coordinates, transports bound relations, imports evidence, and restores each bound with `BoundAdmissionCause::FreshUse { antecedent, use_origin, source_bound, mapped_relation }`. | No certificate-dependent observation registration is supplied by these mappings. |
| Accepted bound before products | `candidate_extrusion.rs:655–674` reserves a restoration, inserts the bound with evidence, canonicalizes owner/bound, saves the opposite count, and retains the emission and source occurrence/cause. | A real source candidate must establish count ≥2 and exact product identities at this point; creating two rows directly in a unit test does not do so. |
| Sequential remaining products | `candidate_extrusion.rs:677–721` retains the original count and next index, drains the active replay before advancing, and re-reads the canonical owner and live opposite at each saved index. | Existing synchronous completion does not establish private suspension, invalidation recomputation, or resume. |
| Source-owned Function/swap | `lib.rs:12100–12147` constructs typed ports from actual Function/Function comparison; `candidate_context.rs:2351–2400` retains exact parent/child incidence, reversing argument ports with `Swap`. | Need a source-generated Value product invoking this dispatch while restoration is unfinished, with the FunctionPort dependency entering the initially certified component. Endpoint similarity does not establish that membership. |
| Admission before enqueue | `lib.rs:12243–12264` admits a port into `dispatch.pending` before enqueue and advances only after enqueue; admission order is Result, ResultEffect, ArgumentEffect, Argument because it indexes the four-port array backward. | Need a second source-owned suspension at this actual seam. A manually installed `FunctionDispatch` is only a private ownership control. |
| Genuine authorization and old observations | `candidate_context.rs:681–702,911–961` retains borrowed evidence and explicitly marks readiness/filter/observation gaps; FunctionPort incidence also marks `InertOperation`. | The initial valid-generation producer, complete dependent-observation inventory and source-recognition join are absent in the inspected route. |

Function argument incidence records `FunctionPortOperation::Swap` even when
the inherited context is identity. Only a nonidentity inherited context creates
an explicit `ContextExpr::Swap` at `candidate_context.rs:2376–2380`. Consequently
looking only for a newly allocated Swap node misses a dependency-only mutation;
conversely an identity argument port does not by itself prove that a component
is outside the selected circuit classes. That conclusion needs the exact
recognizer and full dependency set.

The source Lambda producer already retains real inferred-entry provenance:
`lib.rs:11162–11214` allocates entry/returned rows and records the slot-3 origin
before constraining entry to returned. `candidate_context_tests.rs:2966–2999`
distinguishes this origin from a written Function interface. This repairs one
historical provenance gap but supplies neither a cycle certificate nor the
required full observation witness.

## Existing authentic prefix and prior routes

The independently reviewed
[`selected-owner restore callback coverage`](2026-10-11-selected-owner-restore-callback-coverage.md)
retains this actual source at historical baseline
`064f2af2b1a49df0b332b5980cfc5a105715c353`:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); my defer u = (bridge as ((int -> ['a] int) -> ['b] int) -> [
    E
    'q
] int); defer }
```

This is useful as an authentic **restoration control**, not a proposed complete
§7 witness. The historical trace installed an incoming Allowance upper on S53
at action 48, captured it at boundary1/action57 while preserving S53/R47,
freshened q96 to q113, and restored S53/Allowance9 at occurrence27. Its saved
opposite count was six; the distinct ordered fibers were `(186,515)`,
`(253,515)`, `(187,515)`, and children were
`[516,515,516,517,517,517]`. All six drains completed with an empty worklist.
The observed callback appended a duplicate upper, preserving the old opposite
vector and fibers. No late unsupported Function/swap event or certified
generation was established in that interval. Those historical IDs are not
asserted to reproduce at the new baseline; this lane did not run the source.

The q113 distinct-owner failure/impossibility question is separate. The six
products above already execute, so this source is not an absent-child witness.
No proposed q113-to-old-parent transport, original-Y sharing, or unrescued omega
is used as a premise for §7 here.

Two other available routes do not bridge the same missing premise:

1. `candidate_context_tests.rs:1725–1791`
   (`retained_restoration_retries_saved_opposites_without_reemitting_accepted_bound`)
   creates owner/lower/two uppers directly and manually attaches Swap contexts.
   It establishes a valuable private restoration seam but not source ownership,
   initial certification, or member publication.
2. `candidate_context_tests.rs:3940–4007`
   (`owned_function_dispatch_retains_admitted_child_until_enqueue_and_rolls_back`)
   manually creates the typed frame and port array and discards the synthetic
   route. It establishes admission/enqueue ordering but not a genuine
   Function/Function source product.

These are inspected existing controls, not new experimental attempts. Combining
them into another manually prepared state would leave the source premise
untouched. The next method must inspect or retain evidence at the owning source
construction point.

The reviewed
[`recursive PUSH source invariant`](2026-10-10-recursive-push-source-invariant.md)
provides paired-ascription schemas for the approved cycle family, but its actual
derivation uses pinned Oracle annotation/propagation owners and explicitly ran
neither parser nor compiler. It does not establish a current successor
certificate or a post-publication fresh-use schedule. Importing that grammar or
its weighted ports into a synthetic candidate graph would assume the missing
source correspondence. The `EntryCertificateId` token is also distinct from a
two-cycle certificate; manually constructing that token supplies neither.
The reviewed circuit note's complete pre-generalization classification also
states that its Effect component never points back into a Value Function port;
its argument swap reaches a terminal `int`, rather than feeding right debt
back into the recursive component. Thus the exhibited circuit is not already
a late unsupported Function route. Adding a later use or changing its ports
requires a new constructor trace and cannot inherit that bounded classification.

## Minimal proposed test trace, conditional on the missing source construction

This is an event specification, not an executable or established route.
Use symbolic identities to prevent historical numeric IDs from standing in for
source evidence:

1. Execute an actual dependency-first source SCC M. Retain exact complete
   recognition witnesses for certificate C@g and dependency D, existing typed
   memo/completion O@g, and the published member slots P@g. Assert that C's
   membership was generated by source, rather than installed by the test.
2. At an actual incoming or published-local Name action U, capture/freshen once
   using fresh-use identity F. Retain source bound b and its transported
   relation. Accept emission e; save N≥2. Complete product0/child c0 using C@g,
   retaining its typed input, origin, context, and completion provenance.
3. During a remaining **Value** product that compares genuine positive and
   negative Function terms, admit the exact argument or argument-effect port
   k before enqueue. Verify D gains k and exact recognition now fails both
   approved classes. At this seam assert at least one child/product remains,
   and that O@g, c0's dependent result and P@g are withdrawn before reuse.
4. Retain e, F, b, k, source occurrence/cause, saved N/index, child list and
   popped/queued typed work in private suspension. Repeat drive without relevant
   mutation and compare state/queue/counters for stability. A failing route
   restores the entire prior generation/frame/observation/publication/accounting
   snapshot; a supported retry recomputes c0 ahead of the saved next child and
   finishes remaining products once without a second F or e.
5. At a later actual Function admission/enqueue seam suspend again and retain
   its newly admitted pending relation. Complete source/SCC execution and
   publish the full member group together. Run ordinary identity/zero-word
   controls separately.

Steps 1 and 3 contain the unresolved source join. Source restoration of an
Effect Allowance with six opposites supplies step2's multiplicity control but
does not substitute for step3's genuine Value Function comparison. Mutation
controls should remove readiness, leave one old memo, leave publication visible,
repeat F/e on resume, skip c0 recomputation, or enqueue k prematurely. No such
mutation was implemented or run here.

## Independence, coverage and resource limits

This lane reads the pinned source producers/consumers directly and shares only
the approved contract and baseline with other lanes. It is independent of the
implementation worker's live modifications and the resumed-restoration prover;
it is not independent review of either artifact. There is no executable oracle,
transition checker, random seed or enumerated input range. Historical results
are labeled by their own baseline and are not represented as new execution.

Commands used were read-only `git show <baseline>:<path>` with bounded
`nl -ba`/`sed -n` slices, `git grep -n` on that revision, `git ls-tree` for
locators, and `git rev-parse <baseline>:<path>` for blob identities. Repository
rules and the yulang-proofs skill were read; no Cargo, parser, compiler, probe,
test, formatter, child agent, Git mutation, manifest/lockfile edit, or scratch
artifact was used. One initial broad file listing and task-record read were
output-truncated; neither supports an exhaustive negative claim. Targeted reads
above supplied the stated findings.

Budget: one static pass under the assigned 20-minute wall-time envelope;
independent read commands were batched, with at most four tool command calls
in a batch, and no heavyweight process. Pipeline subprocess counts, exact CPU,
peak RSS and total wall time were not measured. No search was timed out or
killed. Excluded scope: alternate source constructors outside the inspected
routes, exhaustive source reachability, recognizer completeness, new source
grammar, runtime discharge, diagnostic closure, all-source impossibility,
soundness/principality and production cutover.

Recommended next action: give the source-recognition owner one bounded packet
to construct and retain the complete witness/dependency join for steps1–3 at
source admission; only then execute the authentic §7 regression. Keep synthetic
adapter tests explicitly classified as lifecycle controls until that join is
available.

## Dependency identities and commit packet

These are Git blob SHA-1 identities at the pinned baseline, in path order.
No dependency was changed by this worker; current HEAD/live equality is for the
primary to recheck before integration.

| Dependency | Blob |
| --- | --- |
| `crates/yu-solver/src/candidate_scheme.rs` | `93a8d2d27932dede8341b61f2940ede6fbe3e06a` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `8b525d6227684d8d68a3d2745f910e3bbb293c0c` |
| `crates/yu-solver/src/candidate_source.rs` | `dbc3ee822a61b4a861597f07654c52cacb8fb92d` |
| `crates/yu-solver/src/candidate_context.rs` | `3bc4479b0b7303b643a41705a57a6ff6c7274e8f` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `60adbbe42b223aaa25ae4f05632292fe63a9fefc` |
| `crates/yu-solver/src/lib.rs` | `8ef291234f3979bfbc163b03b3d52af338ed577b` |
| Private suspension contract | `fd92fb5c62564455cb66e19059d147dfc20985e7` |
| Contextual attachment/admission design | `c99873544ca90aa817c77941514f7868a8023d65` |
| Selected-owner restore callback coverage | `f5704736c15377f52b746610b84593323be020ed` |
| Recursive PUSH source invariant | `f9f8c529a4a177343c905fa8cae4b2df33de2412` |

- Exact leased/changed path:
  `notes/progress/2026-10-11-authentic-lifecycle-source-route.md`.
- Baseline SHA: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`.
- Changed dependency hashes: none.
- Review status: exploratory/unreviewed research checkpoint; no closure claim.
- Checks run: pinned constructor/consumer reads, bounded call-site searches and
  blob identification; no executable checks.
- Proposed commit message: `research: record authentic lifecycle source-route obstruction`.
- Shared-record deltas left to primary/curator: record the §7 source join as open;
  distinguish genuine restoration controls, synthetic adapter controls and
  authentic initial certification; keep q113 A/B status unchanged. No task,
  design, index, theory-map or question-board file was edited.
