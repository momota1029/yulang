# Retained lifecycle admission: exploratory architecture proposal

Date: 2026-10-11
Status: exploratory proposal; initial independent reviews found two wording
defects, corrected below; no internal representation decision, implementation
authority, §7 closure, or production approval.
Producer: primary synthesis of read-only architect analysis.
Baseline: `research/simple-sub-intrusion` at `0c7e3b423`; source dependencies
remain the committed handoff and lifecycle owners at this checkpoint.

The review inputs are pinned by current worktree SHA-256:

| Input | SHA-256 |
| --- | --- |
| Private suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Contextual attachment admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Native H3 proof | `5d238a9b4ea9b8be736d67f495fba76df7b1c3be61927716fd820e92a1352f85` |
| Native H3 source audit | `f362b08cec82dd01a105be26b9152a4cb18fdea9a7715bf6a6f5bce7e38a68f2` |
| Parsed Local witness record | `6003eb2a85db0ec5eb643032b13f445a34866591d964217f282d55019952773f` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `lib.rs` | `7ace990203b77f1b8aad185e8cdbb2cdac90b967e38479774b7081e45c9429ee` |

## Contract boundary and current gap

The approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md)
§§3–6 already selects the required behavior: retain the innermost continuation,
preserve live-index restoration with the saved opposite count, authenticate
incidence-changing mutations, withdraw invalid observations before reuse,
order recomputation ahead of a saved continuation, and journal the whole route
for rollback/accounting. This proposal does not add a language rule or reopen
those choices.

The reviewed native H3 lemma establishes ordered, sole-owned acknowledgement
intervals for native forward histories. The parsed Local test establishes one
authentic nonempty replay through Running, Ready and delivery. Neither shows
that a new route interleaved between retained child steps is authorized,
dependency-disjoint, or followed by withdrawal/recomputation.

Current ownership is split across whole-action source support checks,
synchronous Local stepping, exact dependency admission, extrusion's live
opposite lookup, intrusion's representative/canonicalization operations, and
scheme's Local/SCC publication. No single lifecycle-aware admission owner
connects those facts to a retained Local/restoration/replay/drain continuation.
The existing synthetic support registration is not a complete production
observation inventory.

## Candidate owner responsibilities

A private lifecycle coordinator could admit a proposed mutation against the
retained continuation's typed dependencies and preserve fact ownership at the
existing phases:

| Existing owner | Canonical facts used by lifecycle admission |
| --- | --- |
| Context/effect | Exact relation/context/origin/attachment, FunctionPort edge, fiber and evidence identities |
| Extrusion | Accepted emission, raw endpoints, polarity, saved opposite count and live product order |
| Intrusion | Parent/copy qualification, representative changes and transfer evidence |
| Source | Authentic action/occurrence, source cursor and construction/publication stage |
| Scheme | Fresh-use/remap, Local cursor, capture support, staged graph slots and SCC visibility |
| Route journal | Prior mutable contents, owner transfers, lifecycle dirtiness, and retained/undo bytes |

Required flow under the approved contract:

1. Authenticate the mutation against the suspended continuation. A mutation
   produced by the active child remains at its existing callback seam and keeps
   the live-index order. Defer an additional cross-component mutation that may
   alter suspended incidence before physical mutation while the §4
   replay/incidence and ownership-preservation obligation remains open. A
   lifecycle owner's acceptance or complete footprint registration does not
   discharge that obligation. Once independently established, the exact
   incidence/order correspondence must cover the proposed mutation before it
   can be admitted.
2. Before each mutation that relies on additional storage, reserve the
   mutation, observation, recomputation and undo storage it needs. Perform each
   reservation before the dependent mutation; publication remains a separate
   barrier. An exact duplicate dependency remains inert; a new incidence
   advances lifecycle state independently of intrusion equality generation.
3. Withdraw affected observation results before any dependent consumer can
   reuse them. Preserve accepted physical emissions, exact relations and
   independent support.
4. Retain the construction input and run required recomputation before the
   saved child. If recomputation suspends, both it and the saved continuation
   remain owned and the parent cursor stays blocked.
5. Resume or publish only after support, recomputation and (for SCCs) group
   completion are established. Failure restores prior frames, graph slots,
   lifecycle state, queues, diagnostic inputs and accounting as one route.

Historical acknowledgement ownership must stay distinct from recomputation
ownership. Recomputing an already-consumed child cannot create a second
acknowledgement for the original `(operation, index)` or rewind its committed
cursor. A separate recomputation occurrence linked to its invalidated
observation is a candidate representation, not a selected design.

## Unresolved internal choices and review gate

The contract does not select the representation for:

- observation records and exact support subscriptions;
- alternate-support removal and retained recomputation inputs;
- dirty-frontier ordering for cyclic observations;
- the admission certificate proving which mutation footprint is complete;
- how staged and rollback graph allocations are represented in byte accounting.

Possible approaches include an owner-local support registry with a reverse
index, or retaining an ordered observation frontier and scanning affected
records. A partial reverse index cannot imply complete registration. A global
scan may raise ordinary mutation cost. Neither approach is approved here.

These choices need independent compiler-referee and spec-auditor review before
the primary asks for a user decision. Any proposal must preserve §§3–6, expose
the full producer/consumer inventory, account for old/staged/undo storage at
once, and state exact recovery behavior. No implementation may treat partial
registration as production readiness.

## Discriminating evidence

The minimum evidence for a future bounded implementation includes:

1. A same-child callback that appends or redirects before a later saved index,
   with product order equal to uninterrupted execution.
2. A permission-qualified additional route that changes suspended incidence
   and is deferred before physical mutation, while a proved-disjoint component
   may progress.
3. A new FunctionPort edge between existing relations that invalidates exactly
   affected observations; an exact duplicate remains inert.
4. A completed sibling A invalidated while B is saved: withdraw A, recompute A
   before B, suspend recomputation again, and keep B blocked.
5. Failure at admission, withdrawal, Ready, recomputation and graph staging,
   with exact prior owner state, publication, generation and accounting
   restored.
6. The full §7 source sequence: existing certified observations/publication,
   late Function/swap invalidation, multiple products, rollback and supported
   retry, stable waits, one fresh identity/emission and atomic SCC publication.

The committed literal Local test is evidence for a nonempty native child only.
It does not satisfy the lifecycle or §7 cases above.

## Risks and status

Structural costs include support-edge storage, retained input/undo duplication,
old plus staged graph peaks, invalidation scans and repeated recomputation.
Potential use of reverse support indexing and a persistent ordered dirty
frontier is an unverified performance inference; measurement is required only
if the eventual design triggers the repository's material-risk threshold.
No numeric cap or resource policy is proposed.

No tests or measurements ran for this proposal. No language or semantic
decision is requested yet. The original H3/W/A3 theorem, incidence and
recomputation correspondence, authentic §7 lifecycle, Call/effect hygiene,
soundness/principality, production certificates and F5 cutover remain OPEN.

## Initial independent review and adjudication

The spec-auditor and compiler-referee independently reviewed the frozen
proposal against suspension contract §§3–7 and the listed source evidence.
Both identified the same major ambiguity: the original “disjoint or admitted
through the lifecycle owner” wording could authorize an incidence-changing
cross-component route without the separate §4 replay/order correspondence.
The spec-auditor additionally identified that “before publication” did not
require reservation before each mutation relying on that storage. Both
findings are accepted and repaired above. They concern proposal wording and
grant no implementation or spec-change authority. The corrected clauses keep
cross-component admission deferred while the required correspondence remains
open and distinguish pre-mutation reservation from later publication.
