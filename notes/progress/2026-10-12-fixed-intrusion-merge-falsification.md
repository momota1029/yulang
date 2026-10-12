# Fixed intrusion merge: bounded adversarial consumer discriminator

Date: 2026-10-12
Status: frozen unreviewed research; conditional scalar characterization and
first continuation bridge identified; no counterexample or theorem closure
Baseline: `53915a1a5e3ddf246c1a07824fbf3c182ea01c53`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; leaf, no delegation

## Objective, method and exact premises

Attack the claim that the extracted candidate merge law, applied jointly to
the actual fixed E-to-O event `(C,B,+,1),(D,R,-,1)`, can continue through inner
publication/use and outer publication/use while retaining `Theta = Top -> Bot`.
The method is an independent hand table of the scalar event, followed by a
comparison of the owning fresh-use predicates. It does not repeat the stock
typing/principality derivation or construct an invented intrusive continuation.

The fixed term and native store are inputs from
[`cross-level recursive core`](../theory/2026-10-12-cross-level-recursive-scc-core-proof.md)
sections 3–6. The candidate operations are inputs from
[`consumer-law owner audit`](2026-10-12-intrusion-consumer-law-owner-audit.md),
checked against the directly named source owners. The accepted event qualifies
both pairs together; type(O)=type(E) is not imposed. Freshening contributes no
new extrusion event or Value incidence.

Governing sections: parent-copy SCC design **Selected operation and compiler
responsibility**, **Apply-result source-fragment ownership**, **Nested Apply
membership**, **Definition-root Value ownership**, **Retained boundary**;
value/type association **Approved extrusion-event qualification** and
**Definition-root origin for nested call-demand extrusion**; copied-row
ownership **Decision**; top-level inference principles sections 1–5.

The scalar table is conditional on successful candidate merges of valid,
distinct, same-kind canonical rows, sufficient resources, and the exact
listed cut store with no other scalar bounds. Candidate row metadata is
initially `non_generic=false`, as for its fresh row allocator
(`lib.rs:10156–10173`). This is not a claim that Scala rows have been translated
into a valid candidate session: that session also requires structural terms,
bound evidence, relations and active tasks. The absent activation owner from
the input audit is supplied hypothetically by the assigned qualified event;
it remains absent in production.

## Event table: no lost scalar fact at this cut

At the completed inner demand, before inner recursive completion, the relevant
stock bounds are `U(o)=[F(C,D)]`, `U(B)=[C]`, `L(R)=[D]`; all bounds of C,D,A,e
are empty. o,A,C,D have level 1; e,B,R have level 2. F denotes Function.

Candidate `merge_candidate_rows` (`candidate_intrusion.rs:515–604`) appends
both copy bound sides, redirects the copy to its parent, lowers the parent to
the minimum level, transports bound evidence, increments equality generation,
and replays the parent's lower/upper cross-product. Endpoint queries use
representatives (`candidate_extrusion.rs:570–629`).

| Operation | Surviving row / level | Canonically queried bounds | Immediate merge replay |
| --- | --- | --- | --- |
| Before either merge | B / 2 | L empty; U=[C] | none at this cut |
| Before either merge | R / 2 | L=[D]; U empty | none at this cut |
| Merge C into B | B / 1; rep(C)=B | L empty; U=[B] | zero lower/upper pairs |
| Merge D into R | R / 1; rep(D)=R | L=[R]; U empty | zero lower/upper pairs |

Each copy has zero bounds on both sides, so these two transfers append zero
scalar entries. Neither pre-existing link is discarded: `B <: C` becomes a
canonical self-upper and `D <: R` a canonical self-lower. Reversing the two
merge calls gives the same scalar row representatives, levels and lists here;
this says nothing about intermediate relation generations or provenance.
Both distinct calls increment generation. o,A,e retain their levels and
scalar lists. The structural bound `F(C,D)` on o remains a stored structural
identity: canonical row queries alone do not eagerly replace it by a new
Function. Its ports require their own consuming operations.

This table defeats a simple lost-bound attack on this cut. It does not defeat
later replay/completion or structural-port attacks. In particular, a merge
return does not imply every active task is complete. The inspected candidate
has relation transport and generation-aware completion
(`candidate_context.rs:2711–2728`, `candidate_intrusion.rs:223–255`,
`lib.rs:11463–11473`); no operational trace of those relations was supplied by
the frozen scalar store. There is no immediate nonempty merge replay in this
table with which to falsify their completion law.

## First discriminating continuation consumer

Stock inner recursive completion stores `L(e)=[F(B,R)]`, then publishes
`PolymorphicType(1,e)` (`Typer.scala:48–55`). e is still level 2. This is the
next scalar state needed to compare the two consumers, rather than a proved
translation of candidate publication.

| Consumer and exact premise | e mapping at the outer inner-definition use | B/R mapping at boundary 1 |
| --- | --- | --- |
| Frozen Scala: `Variable.level` is immutable; `freshenAbove` tests `ty.level <= lim` and otherwise copies a variable once using its per-use memo (`Typer.scala:166–202,209–227`). Stock e,B,R have level 2. | e becomes fresh e' at use level 1 | B and R become distinct fresh B',R' at level 1; the original level-1 C,D are retained |
| Candidate: assume a valid captured graph for live e at boundary 1 with the scalar merge above. Capture canonicalizes row keys; `local = level > boundary && !non_generic` (`candidate_scheme.rs:289–326`). `expand_row` stops at nonlocal anchors (`:568–572`). Fresh use canonicalizes once per use and allocates only when `row.local && current_level > boundary && !non_generic` (`:965–1019`). | With e still level 2 and generic, e becomes fresh e' | rep(C)=B and rep(D)=R are level 1; B/R are nonlocal anchors and are reused, with no fresh B'/R' |

For the candidate row predicate, B/R reuse follows even if their non_generic
flag were true. e copying requires its stated generic premise. No global
generalization or source admission is inferred from these scalar predicates.

The earliest new continuation seam is therefore **transport of inner
publication and freshening across the changed B/R levels**. The stock
post-event continuation in the frozen note cannot simply be reused after
substituting representative names. Its B'/R' allocation premise is gone on
the candidate side. Conversely, retaining Scala's immutable B/R objects does
not implement the candidate minimum-level update: the stock freshener still
reads level 2. Frozen Scala supplies no representative forest, mutable level
override, or relation-generation transport with which to implement that update.

The accepted parent/copy operation requires equality to affect actual solving
and later use. The governing approved clauses do **not** select a minimum-level
update, a surviving-row freshening predicate, or a source theorem that these
changed local/anchor classifications preserve publication and typing. The
candidate code selects those operations as observed implementation behavior;
its own selection is not an independent semantic justification.

The allocation discrepancy is a discriminator, **not a counterexample**.
Equivalent algorithms may allocate different rows and still publish Theta.
No accepted rule here requires retaining every stock internal assignment or
every fresh identity. Proving or refuting the continuation requires a bridge
from the candidate anchor reuse to the original source typing conclusion, not
an assertion that the two stores must be isomorphic. That bridge was not
established by this pass. Work stops before the outer App, outer publication
and final display; no hypothetical result for them is reported.

## Evidence quality, coverage and resources

No executable inference model, Scala run, candidate run, tests, builds,
mutation runs, benchmark samples, seeds or search ranges. The table contains
one assigned event, its two actual pairs, and both scalar merge orders. The
finite conclusion assumes the extracted transition law; it does not prove
that source law or source-wide adequacy.

The independently grounded comparison is direct reading of two different
consumer owners. Both sides share the assigned fixed store and event. The
candidate is not an independent oracle for its semantics, and stock Theta is
an accepted dependency rather than re-proved here. No semantic oracle validates
an intrusive result. Relevant combined output that truncated was reread in
narrow windows. Exact source admission, structural Function encoding/port
transport, complete Call, effects, arbitrary histories, stale captures, pending
task completion, abnormal routes and final interface preservation remain
unverified. Resource failure is excluded by the table's successful-call premise.

Commands/checks: narrow `cat`, `rg` and `sed` reads of the named inputs and
direct owners; Python SHA-256 plus `git show <baseline>:<path>` byte equality;
reference `git rev-parse HEAD`; artifact whitespace check and leased-path
status inspection. All direct repository dependencies byte-match the baseline.
One leased note was written. No Git mutation, production edit, question edit,
shared-record edit or delegation. At most four lightweight read commands were
issued together, within the 20-minute ceiling; CPU/RAM and precise elapsed time
were not measured. Zero heavyweight processes or performance measurements.

Recommended next action: the primary should assign the constructive lane the
exact boundary-1 anchor-reuse bridge above, with candidate mutable levels as a
candidate premise, and require a source typing/interface preservation argument
before continuing the stock outer trace. Keep the parent theorem, activation,
source correspondence and implementation/cutover gates OPEN.

## Frozen dependency hashes

| Input | SHA-256 |
| --- | --- |
| fixed recursive-core note | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| candidate consumer-law owner audit | `f4b5dfebe1eff301f248279e4d52a4234e17a6f7d1fb0b904f44b7055dc646cb` |
| parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-fixed-intrusion-merge-falsification.md`.
- Baseline: `53915a1a5e3ddf246c1a07824fbf3c182ea01c53`; reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none; direct inputs match the pinned baseline.
- Review status: frozen, unreviewed research; conditional table and consumer
  discriminator only; no source-qualified counterexample or theorem closure.
- Checks already run: named source reads, input hashes/baseline byte equality,
  reference HEAD, artifact whitespace and leased-path inspection; zero tests/builds.
- Proposed checkpoint message: `research: isolate fixed intrusion fresh-use level bridge`.
- Shared deltas left for primary/curator: preserve the exact two-pair cut table
  as bounded evidence; route boundary-1 anchor-reuse/source preservation to its
  constructive owner; retain all parent, source/activation, implementation and
  cutover gates OPEN. No shared records were changed.
