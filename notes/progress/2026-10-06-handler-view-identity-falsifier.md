# Handler release: source view identity falsifier

Status: frozen, unreviewed research; bounded negative search and conditional
witness-preservation derivation. No theorem closure or implementation authority.
Lease: this file only. No code, tests, builds, shared records or Git mutations.
Task baseline: `121c257e78e3633fe86a9c135cd0c8662a6a892e`.
Source snapshot: `659eb05646bb95f10a991bbb9cefdee55721eea1`.
Approved crossing/lifetime decision: `handler-protection-release-crossing/q1`,
answer `d1`, integrated at `28dddc75fd598faf34dd4d069ffb231cb64a82f1`.

## Objective, method and result

Search for two admitted typed computations with identical recorded ordinary
event/path/profile/receiver evidence whose required later protection differs
because one target continues a released view and the other is fresh. Method:
inspect source introduction, binding/result transport, latent execution and
raw resumption rules; compare their full witnesses before considering any
projection that forgets identity. No supplied-predicate model was executed.

**No such source-judgment pair was found.** The inspected source candidates
already distinguish view/evidence roots, boundary introductions and tagged
transport origins. Equality of underlying closure, signature, family,
projected profile sets and receiver is insufficient to establish equality of
that full evidence. The older current-query projection argument is not
repeated here: it forgets history and does not establish full evidence equality.

This result also does not establish that current evidence determines every
approved release outcome. The exact remaining premise is a source derivation
that identifies the marked protection target and decides whether a recorded
typed transport continues that target. A missing derivation has not been
turned into a missing carrier theorem.

## Authority and direct dependencies

The approved answer clauses 2, 4 and 5 require transport of release for the
same target and live original receiver, including raw resumption and actual
deep expansion. A fresh target needs its own qualifying crossing. Clauses 6
and 7 preserve identity/path/dependency evidence and approve no new carrier or
compiler implementation. Timing and the meaning of `?` are already selected.

The callback-context source is Authoritative within its bounded scope. The
ordinary, typed-boundary, owner, role and core packages are reviewed Draft
source candidates with stated input obligations; the notation is exploratory.
Their displayed equations are used with those limits, not promoted to a
complete accepted-program semantics.

| Source / exact governing section | Pinned Git blob |
| --- | --- |
| Typed-boundary §§2, 4: structural observation and capture/re-entry; §6: views, relational transport, receipts and lifetime | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Ordinary computation §§3–5: invocation, callback incidence, raw shallow image and deep source expansion | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Callback context §§1–4: original static slot/profile, dynamic introduction, existing Pure invocation view | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| Hygiene notation: Intended reading; Small-step / relational interpretation; Open questions | `0b249e14d1ecb3bea076549b52af121478552491` |
| Typed-source-owner §§2–4: saved views, non-renaming and uniform invariant | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| Typed-computation core §§2–3, 6: derivation inputs, binding/lookup, structural source synthesis | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| Source-computation role §§3–4, 10: result paths, original annotation occurrence, typed rebind | `10775573537d8b56423f796db3c7ac6bb427e252` |
| Approved release answer, clauses 1–7 | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Approved effect-row answer, clause 6: common fiber and preserved path/attachment | `77e28d7826634421a98e556a0023b29c762420ad` |

Prior frozen release constructive/falsifier notes at the task baseline were
read only to exclude their Observe/crossing, circular-image and current-query
projection attacks from this lane.

## Where the source already records the distinction

Typed-boundary §6, lines 670–696, defines a view as `(v,t,e)` with an evidence
root `e`; aliases of the same underlying value need not have identical views.
Boundary entry introduces fresh `b=(r,a,Γ,endpoints)`. Copying a view allocates
no boundary. Thus pointer/type/receiver equality cannot identify two evidence
roots or independently introduced protection slots.

Section 6, lines 707–782, gives transport as an indexed relational image of
disjoint source view/port indices. Source witnesses and their provenance are
retained in the union. A fresh result packet receives actual-value evidence
and corresponding callee-result evidence. Creating that packet does not erase
its inputs or equate their roots. Ordinary binding uses identity; returning
and forcing map only matching result paths. A call-effect position is not a
latent-result effect position merely because their type variables coincide.

Section 6, lines 798–833, requires the executing view in `Observe` to be the
same view received in `Receive`, connected to the original profile by matching
`Flow` edges. Another alias route is expressly insufficient. Equal truth
values of existential `Path` queries therefore do not establish equality of
their underlying witnesses.

Typed-boundary §4, lines 442–462, preserves the original typed packet and port
when a saved `View` resumes, while allocating a fresh execution occurrence.
Occurrence freshness is consequently not independent protection-target
freshness. Owner §3, lines 145–177, separately forbids rewriting old boundary
receivers, receipts, profile roots and stored views. Saved entry is not replayed;
only an actually executed boundary-entry operation allocates a fresh boundary.
These owner rules close an identity distinction that cannot be inferred from
the shorter ordinary invocation equations alone.

## Conditional derivation: witness distinctions survive transport

Hypotheses:

1. A finite decorated derivation supplies original views, annotation/profile
   occurrences, tagged typed correspondences and receipts under one `ν,K,D`.
2. Every flow step uses §6's indexed image and retains its source witnesses.
3. Boundary entry is the only introduction of fresh boundary instances;
   raw re-entry preserves packets and historical boundary references.
4. Comparison includes the retained evidence graph and introduction/flow
   witnesses, with a single consistent identity renaming that also maps the
   earlier marked target. It does not compare only projected `χ` or `Inc_C`.

For an output witness at position `p'`, expand the transport definition:

```text
(p',b) in χ_out  iff  exists i,p.
  χ_i(p,b) and M_i(p,p'), with retained source witness i,p,b.
```

Induction over a flow chain preserves `b` and its original receiver and
records the chain's source roots. Composition may summarize the route, but
its existential witnesses are retained. Adding a second source with the same
projected `(p',b)` does not establish that it is the first source: its input
tag/root remains distinct. Actual fresh boundary entry instead introduces
`b'`, distinguishable from `b` even if signatures and family heads coincide.
Raw resumption changes the observation occurrence and current receipt owner,
while preserving the original saved packet; it introduces no fresh boundary
merely by resuming.

Consequently, a pair differing in **recorded** packet identity, original
boundary identity or retained source-root reachability cannot be identical
under hypothesis 4. A coarse projection can hide that difference, but then
it is not the full ordinary evidence requested by this job. This is a
conditional witness-preservation result for the stated source candidates.
It is not a theorem that all approved target continuity equals reachability.

## Search cases and why they do not supply the requested pair

| Source-rule case inspected | Discriminating existing evidence / unresolved premise |
| --- | --- |
| Bind/capture/store/read the existing callback versus receive the same closure through an independent protection slot | Identity transport retains old tagged view; real boundary entry supplies a fresh `b` and slot. Full witnesses differ. Concrete callback inequality and marker elaboration must still be derived. |
| Resume a saved crossed `View` versus execute a new callback boundary entry | Saved packet/port and original `b.receiver` are retained; new entry has a fresh boundary witness. Fresh execution occurrence alone supplies no reset. |
| Return a latent actual value versus contribute a callee-result annotation at the same target position | Both can produce equal projected profile sets; the multi-input image retains the different source tags. A newly allocated result packet alone proves neither release reset nor continuity. |
| Return latent value at a distinct nested signature path | Matching result prefix determines `Flow`; equal family/type endpoints do not equate the paths. Moving the outer call annotation to that latent port is explicitly disallowed without a correspondence. |
| Re-enter the explicit deep expansion | Actual fresh handler/owner occurrences and callback entries are recorded. Deep syntax does not copy a grant or relabel the surviving original boundary. Marker-target continuity still needs its source derivation. |

None is presented as a pair of admitted marked surface programs. The core's
§6 generates result roles for known interfaces, but its §2 and the hygiene
draft do not supply general marker attribution/attachment judgments. Assigning
those judgments by hand would create the supplied-predicate countermodel the
task specifically excludes. No smallest admitted witness was established.

## Oracle independence, mutations and failure conditions

The oracle here is the pinned source text plus the approved answer. There is
no independent executable semantic oracle, no randomized seed and no numeric
enumeration range. Search coverage is the five rule cases above over the
inspected sections, including binding, latent result and resume distinctions.
It is a bounded textual investigation, not exhaustive program search.

The derivation shares the source candidates' supplied decorations, profile
positions, correspondences and complete ownership premises. Reading another
reviewed proof of those same decorated transitions does not independently
prove raw-source elaboration or mark-specific continuity.

Named shortcuts checked against explicit source clauses: drop the evidence
root and compare pointers; identify all equal family/type paths; flatten
multi-input source tags; classify every new execution occurrence/result packet
as a fresh protection target; replay boundary entry on raw resume. Each loses
a distinction mandated by an inspected equation. No runnable mutation tests
were performed, and these objections do not prove the complete release rule.

The negative result could fail outside this search if an admitted marker
elaboration creates two unequal required target judgments with isomorphic
full recorded evidence while fixing the earlier release anchor. Conversely,
showing unequal view roots alone would not prove that their transport belongs
to different release targets. Unknown-shape inference, annotation overlap,
arbitrary imported clients, mixed-row elaboration and all marker-specific
typed source judgments remain unverified.

## Checks, resources and next action

Read-only `git show <pin>:<path>`, section-scoped `sed`/`rg`, `git grep` and
`git rev-parse <pin>:<path>` located the rules and dependency blobs. HEAD was
the assigned baseline at dependency collection. No build, compiler test,
checker execution, formatting, Git mutation or child delegation occurred.
Only the leased note was written. Lightweight processes were sequential;
CPU/RAM peaks were not measured. Work was bounded by the assigned 15-minute
wall budget; there was no uncompleted enumeration or timeout to report.

Recommended next action: derive a marker-specific judgment selecting the
full protective witness and classify its continuity through each existing
tagged typed correspondence. Start with identity binding and matching latent
result transport; preserve independent target introductions and raw-resume
packet identity. This attacks the missing source premise directly before
considering another model or carrier change.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-handler-view-identity-falsifier.md`.
- Baseline SHA: `121c257e78e3633fe86a9c135cd0c8662a6a892e`.
- Source/decision pins and direct blob hashes: recorded above; no dependencies
  changed by this worker. Primary must recheck against integration HEAD.
- Review status: frozen, unreviewed research; conditional derivation and
  bounded unsuccessful source-pair search, no independent certification.
- Checks already run: pinned section/reference reads, blob identity queries;
  no code tests, builds or executable experiments.
- Proposed message: `research: bound handler view identity falsifier by source witnesses`.
- Shared-record deltas intentionally left to primary/curator: record that full
  tagged view/boundary/transport identity is already present; retain the open
  marker-target continuity derivation. Do not close release adequacy or claim
  a missing carrier. No edits to `tasks/current.md`, `tasks/research-lab.md`,
  theory maps, design index or question bundles were made.
