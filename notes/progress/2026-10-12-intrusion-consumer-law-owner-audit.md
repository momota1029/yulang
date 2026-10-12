# Candidate intrusion equality consumer: owner audit

Date: 2026-10-12
Status: frozen, unreviewed research source characterization; approved activation
bridge absent; theorem and implementation correspondence OPEN
Baseline: `95703ee43587e68b0c508639d601bd20b1c3ef24`
Branch: `research/simple-sub-intrusion`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file only; leaf, no delegation

## Objective, authority and premise

Extract the existing candidate's equality consumer and identify the first
missing premise for applying it to the fixed native recursive core. This is
one static owner pass, without execution or a proposed replacement transition.
The fixed input is [cross-level recursive core](../theory/2026-10-12-cross-level-recursive-scc-core-proof.md),
sections 3–6: stock simplified principal interface `Top -> Bot`, actual inner
extrusion pairs `(C,B,+,1)` and `(D,R,-,1)`, and approved occurrence endpoints
origin E / receiver O. The primary supplies independently reviewed status for
the stock principal interface only; that does not certify intrusion.

Governing clauses are parent-copy SCC design **Selected operation and compiler
responsibility**, **Apply-result source-fragment ownership**, **Nested Apply
membership**, **Definition-root Value ownership**, **Retained boundary**;
value/type association **Approved extrusion-event qualification** and
**Definition-root origin for nested call-demand extrusion**; copied-row
ownership **Decision**; top-level inference principles sections 1–5. Their
selected meaning is unchanged: an actual extrusion occurrence retains its
origin/receiver Values and produced polar type pairs; equal Value SCCs qualify
those pairs. A solver row of kind Value is a type coordinate, not automatically
a source Value. Freshening alone creates no extrusion occurrence or Value edge.

The operational characterization below is conditional on a successful call to
`merge_candidate_rows(copy,parent,root,parent_index)` with valid, distinct,
same-kind canonical rows and available resources. It is not a theorem that
this call is source-qualified, preserves typing, or completes every consumer.

## Existing transition and direct consumers

All paths in this section are under `crates/yu-solver/src/`.

| Stage | Exact owner and extracted operation |
| --- | --- |
| Creation | `candidate_extrusion.rs:73–123`: canonicalize the initial endpoint; operation-local row memo uses endpoint/polarity/target. A row above target is freshly allocated at target, its actual parent is retained, then the opposite-side source link is inserted. `candidate_intrusion.rs:23–28,171–220` retains only `copy,parent,polarity,target`; it sets dirty. |
| Identity | `candidate_intrusion.rs:63–83,525–534`: follow same-kind representative forests; canonicalize copy and parent; equal representatives are a no-op. The parent representative is the destination, even when its original level is greater. `lib.rs:11440–11452` canonicalizes row endpoints only; structural Function terms remain stored identities. |
| Bounds | `candidate_intrusion.rs:548–575`: append every canonical copy lower to parent lowers and every canonical copy upper to parent uppers before forest redirection. `candidate_extrusion.rs:399–404,432–433,570–629` supplies canonical owner/item insertion and opposite-list lookup. Physical copy storage survives. Transfer origins with `ParentCopy { parent_index }`. |
| Level/metadata | `candidate_intrusion.rs:576–591`: set destination level to `min(level(parent),level(copy))`, OR `non_generic`, redirect the copy representative to parent; effects also splice capture incidence. Thus the surviving identity is the former parent, with potentially changed generalization classification. |
| Bound evidence | `candidate_intrusion.rs:593`, `candidate_context.rs:3125–3143`: visit retained bound keys, transport changed keys to their canonical coordinates, and create derived relation dependencies before replay. This is an implemented evidence operation, not proof of complete fiber coverage. |
| Invalidation/root | `candidate_intrusion.rs:530,594–598`: increment global equality generation once per distinct merge, set dirty, reopen the supplied optional Value diagnostic root. `lib.rs:11455–11460` journals/admit-diagnostics and marks that root Pending; it does not itself enqueue the root comparison. |
| Replay | `candidate_intrusion.rs:599–604`, `candidate_extrusion.rs:763–804`: enumerate all merged parent lowers; for each, enumerate canonical parent uppers and create lower/upper replay operations, with the optional root supplying diagnostic edges. `candidate_context.rs:2911–2957` tracks newly retained lower/upper fibers against prior replay heads. `:3110–3122` may return Queued; the outer worklist must complete queued children. A successful merge return alone is not proof of completed replay. |
| Pending tasks/cache | `candidate_context.rs:2711–2728` transports a task's relation when canonical endpoints change. `lib.rs:11463–11473` treats a pair as current only when its raw diagnostic key exists and the processing relation's completion generation matches current generation. `candidate_intrusion.rs:223–255` marks relation completion only for the canonical pair. `lib.rs:12349–12362` admits a raw alias for diagnostics and enqueues its canonical pair. `:12929–12957` preserves diagnostic children while replacing admission/completion data. This differs from an immutable endpoint-pair cache. |
| Settling consumer | `lib.rs:11993–12021,12225–12255` calls settling when the typed worklist is empty; dirty settlement can repeat and replay can enqueue further work. These are observed call sites, not a proof of termination or scheduling adequacy. |
| Capture/generalization | `candidate_scheme.rs:289–326` canonicalizes capture identities and records `local = level > boundary && !non_generic`. `:568–572` stops bound expansion at nonlocal anchors. `:691–758` builds the graph from the live root. `:947–960` recaptures stored root/boundary before an incoming use; `:1363–1374` recaptures a local scheme before constructing its retained use frame. |
| Fresh use | `candidate_scheme.rs:965–1019` maps each current representative once per use; fresh allocation occurs only when captured `local`, current level above boundary, and current metadata permits it. Otherwise reuse the representative. `:972–975,1221–1247` restores captured bounds through the mapped terms and drives restoration. Current representatives and current levels are therefore operational inputs to publication/use; their preservation law remains unproved. |

In list notation the successful scalar merge performs append-union
`L(parent) ++ canonical(L(copy))`, `U(parent) ++ canonical(U(copy))`, followed
by `rep(copy)=rep(parent)` and the minimum-level update. This denotes stored
list accumulation, not mathematical set deduplication or a complete quotient
of every structural node. Subsequent endpoint queries use the representative;
this audit does not claim eager rewriting of all Function ports or arbitrary
retained snapshots.

## First absent source-to-consumer premise

The boundary precedes the merge: **there is no retained approved extrusion
occurrence in this activation owner.** `Parent` contains no occurrence identity,
origin Value or receiving Value. `settle_candidate_intrusion` at
`candidate_intrusion.rs:374–474` constructs dependency adjacency from solver
rows, both bound sides, effect operands and Function ports. At `:477–486` it
tests component IDs of the canonical type copy/parent endpoints themselves.
It does not consume the approved Value-reference SCC and the actual
occurrence's origin/receiver endpoints. This is the exact stale qualification
premise; its graph cannot be adopted as the approved graph by this audit.

For the fixed core, authority qualifies both pairs together through E/O.
The live candidate's retained Parent records cannot express that reason.
Consequently the native event cannot be routed to this merge with a
source-backed justification from the inspected owners. This is an absent
bridge, not an observed wrong result, a counterexample to the approved
operation, or a proof that the candidate necessarily refuses the term.

Even if a caller separately supplied the qualified pairs, the table would
remain an extraction of candidate behavior. It would not establish that
lowering B/R to level 1, changing local/generalized status, and replaying the
merged graph preserve the stock `Top -> Bot` source conclusion or required
principality. No candidate admission or intrusive continuation is inferred
from the native trace. No claim of all-consumer reachability is made after
this first absent activation premise.

A separate directly called evidence gap is explicit at
`candidate_effect.rs:563–597`: origin-table transport lacks an origin-to-fiber
association and imports `MissingOriginAssociation`. This does not establish
a scalar typing failure; it prevents describing all provenance/effect
transport as established merely because the merge invokes that helper.

## Reference distinction and open gates

Reference `Typer.scala:100–123` inserts variable comparisons in its cache
before extrusion and recursively compares the returned demand. `:166–202`
freshens each variable above a boundary with a per-use map. `:221–227`
declares immutable variable levels and the bound-level invariant. It supplies
no parent/copy union, mutable minimum-level update, equality generation or
relation-completion invalidation. Therefore its cache/freshening law cannot
justify the candidate law by substitution of canonical names. The candidate
code is evidence that a transition exists; it is not an independent oracle
for that transition's source typing meaning.

The original soundness, required principality, normal-progress and termination
theorem remains OPEN. Approved occurrence construction/transport, complete
Call, effect hygiene, Yulang source/generalization correspondence, production
implementation correctness and F5 cutover remain OPEN. The finite stock
principal-interface result retains its narrower scope. No production authority
or new language meaning is supplied here.

Recommended next action: the primary should give the constructive proof lane
this extracted mixed-level merge law as an explicitly candidate hypothesis,
with the fixed E/O occurrence and C=B,D=R supplied separately by authority;
require its source-typing preservation judgment before an implementation
packet for occurrence retention and activation. Keep activation correspondence
OPEN until the real constructor/consumer certificate exists.

## Checks, coverage and resource envelope

One static pass of the named three files and directly called identity,
bound/evidence, replay, drain/cache and scheme consumers; narrow Scala windows;
required rules, authority and fixed proof note; relevant task/index locators.
No tests, builds, probes, mutation runs, seeds/ranges, benchmarks, Git mutations,
production edits, questions or delegation. No independent executable oracle
was used. Shared assumptions are the fixed native derivation and approved
occurrence contract; candidate code was not assumed correct. Some combined
reads truncated; decisive windows were reread narrowly. Stop condition was the
activation boundary identified above. At most four lightweight read commands
were issued together; exact CPU/RAM and wall time were not measured, with a
20-minute assignment ceiling and zero heavyweight processes or measurements.

Omitted: arbitrary histories and continuations, all stale snapshot/replay
states, failure/rollback paths, structural-port closure, effects beyond direct
helper coverage, source admission and semantic preservation. Resource failure
can interrupt this fallible transition; successful-path extraction does not
prove publication safety after such interruption. Top-level principles do
not impose complete rollback as a general gate.

Direct inputs below byte-match the pinned repository baseline; reference HEAD
matches its assigned revision. No dependency was modified by this leaf.

| Direct input | SHA-256 |
| --- | --- |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| fixed recursive-core note | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-intrusion-consumer-law-owner-audit.md`.
- Baseline: `95703ee43587e68b0c508639d601bd20b1c3ef24`; reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none; hashes above freeze the audited inputs.
- Claim/review: frozen unreviewed source characterization, first absent
  activation bridge identified; no independent review or theorem closure.
- Checks already run: narrow source/rule reads, SHA-256, baseline byte equality,
  reference HEAD, artifact whitespace/scope integrity; zero tests/builds.
- Proposed checkpoint: `research: audit candidate intrusion equality consumer owners`.
- Shared deltas left for primary/curator: record the existing merge/cache/use
  law as candidate behavior, the missing occurrence-qualified activation owner,
  and the direct origin/fiber coverage gap; preserve all parent theorem,
  source/implementation and cutover gates OPEN. No shared record was edited.
