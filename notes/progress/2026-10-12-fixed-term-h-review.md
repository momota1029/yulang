# Fixed-term H: integration verdict and independent review

Date: 2026-10-12
Branch: `research/simple-sub-intrusion`
Status: independently reviewed fixed-term research construction; production correspondence and general gates OPEN

## 1. Verdict and reading order

For the exact term below, H now has a finite executable construction and a
field-by-field refinement proof. H is not an assumed oracle in this result.
The construction is a **proposed research machine** with explicit live type
cells. Unchanged Simple-sub cannot perform its live-object transition, and
the current candidate has not been proved to simulate it.

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

The occurrence is exactly `(E,O)); its two actual pairs are
`(C,B,+,1)` and `(D,R,-,1)`. Source Values, raw allocations, live type
classes and cache identities remain distinct domains. No equality of o and e
is introduced.

Read the artifacts in this order:

1. [Executable H construction and original obstruction](../theory/2026-10-12-fixed-term-h-state-construction.md),
   especially sections 2, 6 and 8.
2. [Explicit-state machine](../../tools/research_fixed_term_h_machine.py).
3. [Replay evidence](2026-10-12-fixed-term-h-machine-evidence.md), including
   every final store/map and the two state-level discriminators.
4. [Current candidate consumer audit](2026-10-12-fixed-term-h-candidate-audit.md),
   including its conditional parent-representative interpretation.
5. This integration/review record.

The source typing/principal-interface theorem for this one term remains the
separate argument in [the stock proof](../theory/2026-10-12-cross-level-recursive-scc-core-proof.md).
The computed interface is `Top -> Bot`. Neither that source theorem nor the
checker result is a theorem about all source terms, independent clients,
complete Call, effects, general termination or the current compiler.

## 2. Native source and latest-HEAD reconciliation

The user-designated
[conditional H note](../theory/2026-10-12-fixed-term-intrusion-quotient-proof.md)
was read first at the initial live HEAD
`5e7ffb735fc1a829d03890ebfd353e17ad7ca342`.

Original Simple-sub is pinned to
`LPTK/simple-sub@9bae772624c23b52a93c1b226157e16898b4d9db):
[Typer.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala)
and
[TypeSimplifier.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/TypeSimplifier.scala).
Their downloaded `reference/` copies are retrieval scratch and are excluded
from the commit.

The remote advanced during work. At
`d12c80b0bf5ea1c55eb24b27fc1de0dfe9b6706a`, the new
[finite Q proof](../theory/2026-10-12-fixed-term-quotient-transition-proof.md)
and [constructor census](2026-10-12-fixed-term-quotient-transition-falsification.md)
already supplied a symbolic construction. They were read and the new producer
was redirected to concrete code/field refinement, rather than counting that
same abstract calculation as a new result.

The latest substantive research reconciliation base is
`2654f22056b8ba0acba86bfa0c8d850b5a25142c`, tree
`f2807578032edab7fd0dd74ba06549cad66678dc`.
The additional remote research includes the
[ALG solution correspondence](../theory/2026-10-12-quotient-solution-correspondence-proof.md),
[its allocation boundary](2026-10-12-quotient-solution-correspondence-falsification.md),
[nested registration audit](2026-10-12-source-registration-owner-audit.md),
and [publication classification attempt](../theory/2026-10-12-source-publication-classification-proof.md).
Their scope and remaining producer/interpretation boundaries were reconciled.
ALG's explicitly interpreted monomorphic presentation does not itself prove
H's generalization or full-source preservation; this packet does not use it
as such a premise. The helper-publication artifacts concern a different
source witness and do not change the fixed odd/even calculation.

The final checked integration parent is
`8a59878fa3ab203a0ddcf6619880ff3b4859ffb4`, tree
`5c1bed8cbeb4a898966684da77c12be0a8e83e6d`. Its only changes from 2654 are
independent-review metadata on those two helper-registration/publication notes;
both shared task records and every direct source dependency are unchanged.

A full tree comparison through d12 and a complete commit/file comparison
through 2654 show only those six added research notes and appended
`tasks/current.md` records. **No original compiler, authority, reference or
direct proof dependency changed.** The latest shared task contents are
preserved before adding this packet's record. The final branch update uses
the exact parent and expected ref; any intervening movement must be
reconciled before updating it.

## 3. What was constructed and proved

The reference obstruction is local and exact: `Typer.scala:65–72` retains
the same B/R constructor references, while `:209–227` makes their levels
and structural children immutable. Legal bound, cache and memo mutations
cannot make that suspended Lambda construct `F(C,D)`. This is a proof of
nonreachability of H's representation postcondition in the unchanged
reference, not a source typing counterexample.

The research implementation supplies the missing capability explicitly.
Its `h` body at `research_fixed_term_h_machine.py:235–279`:

- transfers both parent bound sides to the existing copy anchor;
- clears the retired parent lists, retaining original IDs and levels;
- structurally rewrites both bound lists of every row;
- structurally rewrites every type cell, including cells read by the
  environments and suspended Lam/App/Let/constraint handlers;
- leaves raw comparison keys, polar memo keys/copy identities and source
  occurrence provenance outside that traversal.

Each scan is finite. Structural rewriting descends finite tuple children
without unfolding cyclic bounds. The two actual classes have empty
lower/upper products, so their replay work at union is exactly empty.
This is a proved fact of the source-derived prefix, not a skipped generic
propagation obligation.

The field census includes the raw parent/target ordinals in
`copy_bounds_return`: at these two calls the popped handler has finished
all raw-row reads, and no future frame targets a retired B/R row.
The future semantic reads therefore receive transported operands. Diagnostic
`live()` displays show selected cells only; the coverage proof uses the
actual all-cell traversal and exhaustive handler census.

The actual implementation is pairwise: it acts after each selected-bound
copy and before that branch returns. The first action cannot change the
pending R extrusion's level, memo test or empty selected bound list. The
two disjoint substitutions commute and agree with the batch Q cut for this
prefix. This is not a general scheduling law.

Immediately before native retry:

```text
q(B)=C, q(R)=D
U(C)=[C], L(D)=[D]
inner Lam formal=C; inner App argument=C and result=D
n_inner:Mono(C)
K={(o,F(B,R))}
M={(B,+)->C,(R,-)->D}
```

The returned comparison uses `F(C,D)`. The old raw key remains different,
so native retry adds `(o,F(C,D))` and inserts `F(C,D)` into U(o).
The historical B/R allocation levels stay 2, while live C/D remain their
original level 1.

The ensuing native comparisons are A<:C, D<:S, its cache-stopped self-lower
replay, C<:A and S<:D. E publishes at boundary 1 and its use copies e alone.
O publishes at boundary 0 and its distinct use map copies precisely
o/A/C/S/D. The proof checks actual live operands, levels, bounds and map
sharing through these operations.

## 4. Finite execution evidence and falsifiers

The exact frozen script ran successfully in all four modes:

| Mode | Steps | Allocated rows | E-use copies | O-use copies | Actual inner Lambda | First U(o) |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| Stock | 72 | 17 | 3 | 6 | F(B,R) | [F(C,D)] |
| Complete H | 65 | 14 | 1 | 5 | F(C,D) | [F(C,D)] |
| Bounds-only mutation | 69 | 17 | 3 | 6 | F(B,R) | [F(C,D)] |
| Canonical pending-cache mutation | 53 | 13 | 1 | 4 | F(C,D) | [] |

All four displays simplify to `Top -> Bot`. Therefore final-interface
agreement alone does not certify H. The bounds-only mutation violates live
constructor transport. The cache mutation violates the required native
transformed-bound insertion. Neither is presented as a source soundness
counterexample or as a refutation of the complete H construction.

Portable reproduction from the repository root, using only Python's
standard library:

```sh
python3 -B tools/research_fixed_term_h_machine.py --json /tmp/yulang-fixed-term-h.json > /tmp/yulang-fixed-term-h.stdout.json
```

The optional JSON retains every comparison, cut, cache, event, final store
and map, plus selected before/after Lam/App cell values, all changed cell
indices, suspended frame/environment metadata and allocation levels.
The script's per-run report status is deliberately research evidence; the
external review applies to the exact frozen byte hash below.

## 5. Parent representatives and the current missing operations

For the exact scalar cut, **conditional on the same two qualified unions
actually being supplied**, candidate B/R can represent H's C/D at level 1.
The live interpretation I maps the canonical B/C and R/D classes to H's
anchors. A separate injective historical map J keeps the original B/C and
R/D allocation identities distinct. No global raw-state alpha-renaming
preserves both interpretations: candidate mutates surviving parent levels,
while H retains raw B/R at level 2.

Direct source inspection supports that limited representation calculation:
`candidate_intrusion.rs:525–604` performs the parent-directed minimum-level
union and replay; canonical child consumers and current-level capture/fresh
maps observe the classes. The exact union products are empty, and insertion
of the transformed o upper commutes with these unions at this scalar cut.
The Scala lazy-Function-level objection and literal-cache mutation cannot
simply be assigned to candidate's different structural and completion owners.

The first missing current transition is source qualification itself.
`candidate_extrusion.rs:21–26,73–123` and
`candidate_intrusion.rs:23–28,171–220` retain no occurrence identity/E/O
pair group. The actual settlement graph at `:375–486` uses type bounds
and ports. On the source-derived scalar prefix, that graph does not make
B/C or R/D strongly connected, while the approved source O/E graph
qualifies both. This is a graph-consumer discriminator, not a complete
four-port candidate execution.

The minimum responsibilities still needing actual production owners are:

| Responsibility | Fixed research result | Remaining production/design obligation |
| --- | --- | --- |
| Event and eligibility | Resolved fixed AST constructs E/O and actual polar pair records | Connect actual Apply/call-demand provenance to extrusion; consume the approved Value graph |
| Live type references | Explicit cells and full finite traversal realize H | Select and prove an actual constructor/context/queued-work representation; include candidate facades and all ports |
| Bounds, levels and propagation | Both lists transported; both exact union products empty | Prove nonempty products, mixed-level descendants, delayed work and completion handling |
| Historical identity | Raw K/M/event identities stay distinct from live classes | Prove candidate relation-generation/diagnostic-child lifecycle under the chosen observation relation |
| Publication and fresh use | Original boundaries 1/0 and maps 1/5 preserved here | Prove source eligibility, complete effects/contexts and transport of already created use frames |

These are obligations, not a newly approved sufficient contract. The actual
candidate full source trace and final interface remain unproved. The next
useful evidence is the source-owned event plus the real first-App candidate
store and continuation, including facades, four ports and contexts.

## 6. Independent review, corrections and frozen identities

One fresh read-only referee-equivalent agent, `h_referee`, reviewed the
frozen four-artifact component. It reconstructed the original sources,
actual H loop, raw/live field separation, exceptional row ordinals,
pairwise timing, resumption, fresh maps, compact result and conditional
candidate consumers. It reported **PASS within the fixed proposed-machine
scope, no BLOCKING or major findings, and one minor finding**.

The minor finding at the reviewed proof's line 462 was “six Names”.
There are five Name occurrences and six source Value vertices. The primary
changed it to “five Name occurrences”. The reviewer explicitly required no
further execution or proof review for that textual correction. The primary
also synchronized review status, links, next-owner metadata and the companion
evidence hash; no semantic code or argument changed after review.

| Artifact | Reviewed SHA-256 | Released SHA-256 after stated textual/metadata edits |
| --- | --- | --- |
| Construction proof | d88db7df86e57180589d9f018000c5c0a93fde9fc02e0e0d3d7e6f2530205bf5 | 45dd099daa2a1d92ffb39a99d732024eb57a3d84bce63eaef5c4cff19f2e864c |
| Checker | 9d08adba56e2bc48a834821b1fe434ce6e39f8d7d90c08ebefd83846d352e50d | unchanged |
| Evidence | 477904f5b0a44aab0aee329a21eda236ca1b08ff0be42051713331043a8604b6 | 150c4972da8103ea2a2462288307863fe712393154db61b330cec2d491877c3f |
| Candidate audit | 1d9de57674f3156ca040d2968d83ae5e81ce0b17a9b46c918822d483e8c215e9 | 0a3a46f1d4e5103886484bd1b62af168c8eb8632326d9b5d26c266fabc4a1e98 |

Original Typer SHA-256:
`f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.
Original TypeSimplifier SHA-256:
`618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b`.
All direct design/compiler hashes are in the respective artifacts.

Verification budget: four development executions of these same four modes
(one initial new cardinality assertion failed and was corrected from 5 to
the derived stock count 6), one primary execution, and one referee execution;
all final frozen executions exited 0. Primary detailed report SHA-256 is
`29a957e5210b034c021b825d9006d36e883ba695b054333338a3d082fd85dcaf`.
No random enumeration, dependency installation, Scala/Rust build, compiler
test, benchmark or production edit occurred. CPU/RSS were not measured.

Routing followed the applicable role pins: three bounded producer packets
requested Sol/high, one independent referee requested Sol/medium. Effective
backend model/effort telemetry was unavailable; these are requested settings,
not a runtime certification. Maximum active team size was four including
the primary. Producers had disjoint leases; primary alone owns integration.
The source snapshot is partial and has no Git index; immutable Git data and
explicit path/blob comparisons replace working-tree staging inspection.

The commit contains only this packet's four research notes, one research
checker, and concise updates to `tasks/current.md` and
`tasks/research-lab.md`. It preserves the pre-existing conditional and Q
artifacts and concurrent remote work. No authority, question, compiler,
existing test, manifest, configuration or retrieved reference file is included.

General qualified-equality preservation, arbitrary source/use histories,
source-wide soundness and required principality, complete Call/effects,
normal progress/termination, actual Yulang correspondence, adoption and F5
cutover remain OPEN.
