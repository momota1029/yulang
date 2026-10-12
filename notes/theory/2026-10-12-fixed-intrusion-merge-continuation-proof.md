# Fixed intrusion merge: scalar prefix and continuation obstruction

Date: 2026-10-12
Status: frozen unreviewed conditional scalar derivation; complete candidate
continuation unconstructed; original parent and implementation gates OPEN
Assigned baseline: `53915a1a5e3ddf246c1a07824fbf3c182ea01c53`
Branch: `research/simple-sub-intrusion`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen question and distinctions

Fix the exact pure-core term and original binders:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

`odd` is monomorphic during its initializer. The separately scoped `even`
root is allocated before its initializer and is generalized at boundary 1.
Its initializer does not use that root. `n_outer` and `n_inner` remain distinct.
Outer `odd` publication has boundary 0. Source Value roots O/E are separate
from solver variables o/e. No root is identified with a Function port or
Apply result.

The question is existential and finite: starting at this term's authentic
inner extrusion, with the approved E-to-O occurrence and its **joint** pairs
`(C,B,+,1)` and `(D,R,-,1)` supplied, does the extracted candidate merge and
its real continuation consumers give a complete continuation whose simplified
external interface is the stock principal `Theta = Top -> Bot`? Both pairs
must be applied to the same history; separate marginal witnesses do not answer
the question. The activation hypothesis is supplied by the assignment; the
candidate's stale type-coordinate SCC test is not used as its justification.

Three claims remain distinct:

1. **Mathematical candidate-transition claim.** The successful scalar
   projection of the two existing merges has the determinate prefix in
   section 3. This conditional calculation does not construct a complete
   candidate session or continuation. The requested finite existential
   conclusion remains unresolved at the bridge in section 4.
2. **Original stock source claim.** The supplied independently reviewed
   fixed-term result in the [native core note](2026-10-12-cross-level-recursive-scc-core-proof.md),
   sections 3–5, gives the unmodified native interface Theta and its
   fixed-term declarative principal judgment: for every derivation of this
   exact source at type tau, `Theta <= tau`. This packet imports that result;
   it does not certify it again or extend its quantifiers to intrusive runs.
3. **Approved Yulang implementation claim.** Actual Yulang source
   constructors, occurrence retention/activation, processing, publication
   and fresh use implement the approved equality and preserve soundness,
   required principality and natural inference. This remains OPEN. Neither
   a scalar candidate calculation nor the stock theorem establishes it.

Hypotheses for the scalar calculation: the frozen native prefix, the supplied
joint event, and successful application of the extracted candidate law to
distinct same-kind row representatives with sufficient resources. This does
not hypothesize the missing initial session correspondence. No policy for
levels, metadata, cache reset, structural rewriting or scheduling is added.

Exclusions: other terms or histories; literal/conditional Yulang odd/even
admission; effects, complete Call, attachments/providers/witness/residual
adequacy; abnormal paths; general soundness/principality/termination; production
or F5 cutover. The full parent retains its original supported source scope and
quantifiers. This note does not narrow it or claim that the selected operation
must preserve every arbitrary pre-intrusion scalar assignment.

## 2. Exact authority, owners and initial cut

Governing sources are the parent-copy SCC design's **Selected operation and
compiler responsibility**, **Apply-result source-fragment ownership**,
**Nested Apply membership**, **Definition-root Value ownership** and
**Retained boundary**; value/type association's **Approved extrusion-event
qualification** and **Definition-root origin for nested call-demand extrusion**;
copied-row ownership's **Decision**; and top-level inference principles
sections 1–5. These approve actual type equality qualified by an occurrence's
Value endpoints; they do not choose a Scala-to-candidate representation or
pending-cache adapter. Description copies do not inherit Value incidences.

The [consumer-owner audit](../progress/2026-10-12-intrusion-consumer-law-owner-audit.md)
supplies the candidate law as conditional source characterization. The original
sources and direct candidate owners were also read, rather than assuming that
the audit proved their correspondence:

| Responsibility | Owner |
| --- | --- |
| Recursive roots, original scopes, generation | reference `Typer.scala:48–83` |
| Cache before extrusion; recursive returned-demand insertion | reference `Typer.scala:88–127` |
| Actual polar copies and one-sided links | reference `Typer.scala:134–157` |
| Original fresh-use map | reference `Typer.scala:166–202` |
| Immutable variable levels; cached structural level | reference `Typer.scala:209–227` |
| Parent retention and canonical row equality | `candidate_intrusion.rs:171–220,515–604` |
| Canonical endpoint insertion/opposite-list queries | `candidate_extrusion.rs:399–404,432–433,570–629` |
| Scalar comparison insertion and replay | `candidate_extrusion.rs:808–837` |
| Actual replay operations and queued-child consumer boundary | `candidate_context.rs:2911–2965,3110–3122` |
| Bound evidence transport | `candidate_context.rs:3125–3143` |
| Pending relation transport/completion | `candidate_context.rs:2711–2728`; `candidate_intrusion.rs:223–255` |
| Canonicalization, root reopening and generation-sensitive admission | `lib.rs:11440–11473,12349–12375` |
| Live recapture, anchor classification, mapped fresh use/restoration | `candidate_scheme.rs:301–326,567–572,947–1019,1221–1255,1363–1374` |

Reference files are under
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/`;
candidate files are under `crates/yu-solver/src/`.

The native note summarizes the state **after** returned-demand insertion:
`U(o)=[F(C,D)]`. To locate the literal activation point precisely, let sigma_X
be the earlier cut immediately after `extrude(F(B,R),false)` returns its
Function and before `Typer.scala:123` executes `constrain(o,F(C,D))`.
Let sigma_I be the summarized post-insertion cut. This is a distinction
between actual adjacent native control states, not a new scheduling choice.
The obstruction below occurs at either cut.

At sigma_X, the rows are:

| Row | Level | Lower list | Upper list |
| --- | --- | --- | --- |
| o | 1 | empty | empty |
| A | 1 | empty | empty |
| e | 2 | empty | empty |
| B | 2 | empty | C |
| R | 2 | D | empty |
| C | 1 | empty | empty |
| D | 1 | empty | empty |

Here A is the outer formal and B the inner formal. R is the inner App result.
The open recursive e was allocated before B. The in-process native cache
already contains `k=(o,Q)`, where `Q=F(B,R)`: `constrain` inserts k at lines
100–102 before testing levels or extruding. That test has forced Q's lazy
level to 2. Extrusion creates the distinct structural demand `Qc=F(C,D)`.
The continuation at sigma_X must still insert Qc at o, then return from the
inner App, complete `F(B,R) <: e`, publish/use even, complete odd, and
publish/use odd. At sigma_I, Qc has been inserted and the recursive comparison's
cache also contains `(o,Qc)`; every other displayed row/bound is unchanged.

## 3. Derived successful scalar prefix

The candidate's copy-to-parent merge destination is the **parent**
representative. Apply `(C,B)` then `(D,R)` as the two operations for the
single supplied event; retain both polarities and parent indices. No use or
publication is inserted between them in this calculation.

For C-to-B, canonical C/B are distinct. C has zero lowers and zero uppers,
so both append loops have zero iterations and no copy-bound origin transfer
is called by those loops. B's existing upper is the physical endpoint C.
The law changes B's level to `min(2,1)=1`, ORs its non_generic metadata with
C's, and redirects C's representative to B. Thus a canonical upper query of
B returns B itself. Physical C storage remains intact. Context bound
canonicalization changes the retained scalar key `(B,-,C)` to `(B,-,B)` if
that key/fiber exists in the supplied candidate session; it does not establish
that such evidence was constructed from the Scala link. Generation increases
once and dirty is set. Optional root reopening follows the supplied root.
B has no lower, so merge replay has zero outer iterations.

For D-to-R, D likewise has zero bounds to append. R's existing lower is the
physical endpoint D. The law lowers R to 1, ORs its metadata with D's, and
redirects D to R. Canonical lower queries return R itself; context transport
would change `(R,+,D)` to `(R,+,R)`. Generation increases once more. The
merge replay visits this one lower but R has no uppers, so its opposite-list
loop is empty and creates no replay child. No worklist completion assumption
is needed for these **empty** merge-induced products.

The derived canonical row projection, at sigma_X, is therefore:

| Representative | Level | Canonical lower queries | Canonical upper queries |
| --- | --- | --- | --- |
| o | 1 | empty | empty |
| A | 1 | empty | empty |
| e | 2 | empty | empty |
| B, also representing C | 1 | empty | B |
| R, also representing D | 1 | R | empty |

At sigma_I the sole difference is o's upper containing the **stored
structural identity Qc**. `lib.rs:11440–11446` canonicalizes row endpoints;
it does not replace Qc with Q or eagerly rewrite its ports. Writing this
upper as `F(B,R)` without an explicit port consumer is already an additional
bridge assumption. Physical B/R links still name C/D; the table describes
canonical query results, not an invented eager quotient of all storage.

The two successful distinct merges give generation `g+2`, rather than a new
single-generation event operation. Their scalar projections commute here
because C/B and D/R are disjoint and both products are empty; this says
nothing about commuting retained evidence, diagnostics or partial failures.
The law's metadata OR is recorded symbolically, since Scala has no
non_generic field. A candidate capture at boundary 1 would classify B/R as
nonlocal regardless of those flags (`level > boundary` is false). Claiming
that e is local and is freshly mapped would additionally require its actual
constructor metadata. No B'/R' identities from the **stock** continuation
are imported into the intrusive history.

This prefix proves neither a final result nor equality preservation. In
particular, its empty replay products cannot supply the pending Function
demand insertion or its later Function comparisons.

## 4. First missing application premise

The first unsupported judgment is:

```text
the native sigma_X (or sigma_I), including its live comparison/cache,
has a source-constructed candidate session representation in which
the joint merges and the same outstanding continuation are consumable.
```

The frozen Scala state is not itself an argument to `merge_candidate_rows`.
Its Variable has immutable `val level` and no representative forest. Its
comparison cache is a set of SimpleType pairs; it has no admitted RelationId,
post-check context, completion generation, diagnostic child or replay
acknowledgement. The candidate requires those retained objects in addition
to levels and bound lists. No inspected constructor maps this exact paused
Scala comparison into them. Thus the scalar table alone does not instantiate
the successful-session hypothesis of the actual candidate consumer.

The decisive localized component of that missing premise is the pending
original demand **k=(o,Q)** and its already-produced transformed demand
**Qc**, before publication of e. This premise remains after the assignment
has supplied the approved occurrence's activation; it is not the earlier
missing Value-SCC qualification repeated under a new name.

The candidate contains relevant machinery, but its preconditions are real:

* `candidate_context_transport_task` needs a pre-existing parent relation;
  `None` returns `None`. It derives a child only for a changed canonical
  endpoint pair. Scalar representative changes do not change a Function
  endpoint's structural identity.
* `candidate_reopen_root` marks an optional supplied root Pending; it does
  not enqueue that comparison. Generation invalidation changes whether an
  **admitted processing relation** is current. It does not reconstruct an
  absent comparison or its relation from a Scala cache key.
* The actual worklist at `lib.rs:12364–12375` can reenqueue a previously
  extruded structural comparison's retained diagnostic children, avoiding
  a new copy graph. That branch needs the old admitted root and its actual
  children. The Scala stack/cache does not retain that candidate certificate.
* Bound canonicalization visits retained candidate bound keys and transports
  their existing witnesses. It is not a producer of the omitted initial
  bound/relation fibers. A stored physical link or successful merge is not
  evidence of complete replay or consumer coverage.

The native structural level is another concrete part of the same initial
representation seam: Q's lazy level has already evaluated to 2, whereas the
candidate law would give its canonical B/R ports level 1. Scala cannot have
its immutable B/R levels updated by this law. Recomputing Q's cached level,
rebuilding structural nodes or replacing raw cache entries would be extra
operations; none is supplied by the extracted merge. This observation is
not a proof that Q's historical level causes an incorrect final result. It
shows why a claimed continuation must name its structural consumer and
cannot simply substitute B for C in the native trace.

Consequently this pass stops before asserting completion of the pending
comparison, e's publication/fresh use, or the final external interface for
the candidate history. It establishes neither impossibility of such a
representation nor a counterexample to approved intrusion. It identifies
the exact unestablished operational premise required to construct it.

For orientation only, the sources show the later consumers that any valid
bridge must reach: e's live root is captured at boundary 1; capture halts
expansion at nonlocal B/R; use preparation maps current representatives once
per use; captured bounds are physically restored and their replay is driven;
odd's live root is later recaptured at boundary 0. These are obligations,
not steps of a constructed run. No stock simplification proof is applied to
an unconstructed candidate output graph.

## 5. Obligation economy and next evidence

The earlier ground-store/quotient calculations and native source trace left
equality/continuation/generalization transport unresolved. The consumer audit
then localized activation as absent. This packet explicitly grants activation,
derives its two scalar merges, and reaches the distinct pending-state seam.
It does not launch a third reconstruction model or change the parent status.

Under `compiler-engineering.md`, preservation and lawful completion remain
required A/B obligations. The initial comparison/child/fiber correspondence
is reconstruction debt D where the generation/extrusion owner already knows
the original comparison and transformed demand. Retaining that actual output
is preferable to recovering it from levels, names or a quotient. Existing
candidate diagnostic-child and relation owners are relevant retained evidence,
but their existence in this exact source history must be established at
construction. The classification is an economy audit, not a proof or authority
for a new adapter or semantic restriction.

One next action: assign the owning App-demand/extrusion lane a bounded
source-to-operational construction for **this sigma_X comparison k and Qc**,
including its admitted relation, actual transformed child, bound evidence,
metadata and continuation root. Require it to demonstrate consumption by the
existing generation-sensitive worklist after the two joint merges, or return
the first incompatible owner. Then resume the finite proof from that concrete
representation. Keep complete Call/effects and the original Yulang theorem
separate and OPEN; fresh independent review belongs to the primary.

## 6. Dependencies, checks and limits

All repository dependencies below and the six read rule files plus prover
configuration byte-match the assigned baseline. Observed HEAD during the pass
advanced to `933f588b344efe424c98a08c83a35e550edf7bdc`; this did not change
those inputs. Reference HEAD equals the assigned reference revision. No
dependency was edited by this leaf.

| Direct input | SHA-256 |
| --- | --- |
| native core note | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| candidate consumer owner audit | `f4b5dfebe1eff301f248279e4d52a4234e17a6f7d1fb0b904f44b7055dc646cb` |
| parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| solver `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference `TypeSimplifier.scala` | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |

Checks: static rule/authority/source reads; narrow line-numbered owner reads;
`sha256sum`; read-only Git baseline/reference/status queries; byte comparison
of 20 assigned repository inputs against baseline; final leased-file whitespace
and dependency checks. Initial combined reads truncated; decisive rules and
source windows were reread. One missing speculative `candidate_value.rs`
locator was discarded; the actual scalar owner is in `candidate_extrusion.rs`.
No test, build, Scala execution, executable transition probe, benchmark,
Git mutation, question edit, external contact or delegation was performed.

One pass under the 30-minute ceiling; at most four lightweight read processes
concurrently, no heavyweight process and zero measurement samples. Exact
CPU/RAM were not measured. Primary retains verification and integration.
Requested assignment settings: normal `gpt-6.1-sol` / high; observed runtime
model/effort: unknown. The prover role omits pins and project defaults request
Sol/high; no effective override or hot reload is claimed. No Astra escalation.

Unverified: a constructed candidate representation of the native cut, complete
continuation, final candidate output, source preservation/principality,
source-wide activation, all effects/Call consumers, rollback/resource failures,
termination and production/cutover. The proof artifact awaits independent
review and is not self-certified.

## Commit packet

- Exact changed lease: `notes/theory/2026-10-12-fixed-intrusion-merge-continuation-proof.md`.
- Baseline: `53915a1a5e3ddf246c1a07824fbf3c182ea01c53`; reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none; frozen direct hashes above.
- Claim/review: unreviewed conditional scalar prefix and minimized operational
  obstruction; complete finite continuation and original parent remain OPEN.
- Checks already run: static owners/rules, SHA-256, baseline/reference/byte
  comparison, leased-file whitespace and dependency recheck; zero tests/builds.
- Proposed checkpoint: `research: derive fixed intrusion scalar merges and pending continuation seam`.
- Shared deltas left for primary/curator: record the granted-activation scalar
  prefix, empty merge replay products, level-1 inner anchors, and exact
  pending k/Qc source-to-session premise; preserve the stock reviewed theorem
  at its existing scope and leave candidate/Yulang/parent gates OPEN.
