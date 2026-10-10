# One mixed-annotation incoming use: conditional source trace

Date: 2026-10-10
Status: independently reviewed bounded source characterization; static conditional trace; no execution, supported-input certification, counterexample, or R closure
Baseline supplied by primary: `d7ccbd6f7849d6b2b029fd2028383ebc938a9d09`
Branch supplied by primary: `research/simple-sub-intrusion`
Producer: `/root/restore_replay_source_witness`, leaf; no descendants
Exclusive lease: this file only; frozen on handoff

## Objective and source envelope

Trace one authentic repository source fixture through HIR action collection,
levels, annotation construction, capture, freshening, and every restore callback.
Test whether this particular use supplies the shared-owner/nested-merge seam
left open by the previous source-owner audit. The source is exactly the initial
source-only block of `candidate_effect.rs:2566–2637`:

```yulang
act E
act F
my left x: 'a -> [E, 'e] 'a = x
my first = left
my second = left
```

The authored test calls the real parse/LocalSource/collection path through
`make_session` (`candidate_effect.rs:1441–1465`), then
`execute_candidate_graph_plan`. Its later API-injected extrusion/rollback setup
is excluded. The test was **not run**. Its presence identifies an intended
candidate source fixture, not execution evidence for the current baseline.

Authority remains contextual attachment/admission design §4 (bound storage,
ordered opposite replay, capture/freshening, recorded parent/copy intrusion,
rollback), §3.1 attachment grouping, and `tasks/current.md:8170–8205`. The old
absent `BoundKey(O,+,b)` claim remains withdrawn. The previous source-witness
note and its review are frozen and were not edited.

Hypotheses for the static derivation:

1. Parsing and HIR formation successfully yield the retained source structure
   exercised by the authored fixture, with resolved E and module names. No
   parser, lowering, solver, or source-support result is claimed from inspection.
2. The normal candidate-only source schedule begins from its fresh session,
   with successful allocation/admission, no failure injection, and no external
   graph/vector/metadata mutation.
3. The inspected source/design hashes identify the compiler used in the trace.
   The primary supplied the Git baseline; this worker did not query Git.

These conditions do not assume a parent record, shared owner, or missing pair.
The actual constructors below determine whether those objects exist.

## HIR shape, action order, and levels

The annotation belongs to the complete binding interface. HIR obtains it through
`source_annotation::form` on the binding header Pattern
(`yu-hir/src/module/source_annotation.rs:307–330`), and stores it separately as
`LocalSource.annotation` (`local_source.rs:383–388`). Bare x becomes a Lambda
parameter and the body Name resolves to that parameter (`local_source.rs:289–321`).
This source does not generate a `FormalAnnotation` action for x; that action is
reserved for `parameter.annotation` (`candidate_source.rs:251–257`).

Symbolic row names avoid pretending that dense runtime ordinals were observed:

| Symbol | Row/endpoint role | Level |
| --- | --- | --- |
| D | collected definition root of left | 1 |
| L | collected Lambda expression Value row | 1 |
| P | collected parameter x Value row | 1 |
| B | Name x computation Effect row | 1 |
| Q | Lambda evaluation Effect row | 1 |
| I, R | Lambda entry and returned Effect rows | 1 |
| a | scoped annotation Value variable `'a` | 1 |
| t | scoped annotation Effect variable `'e` | 1 |
| C, S | checking and exposed Effect ports for `[E, 'e]` | 1 |

Collection visits a top-level body at level 1 (`candidate_source.rs:229`). Lambda
parameters and their body retain that same level (`245–261`). There is no Block
initializer to increment it. Session startup sets collected components and
parameters to 1, then installs the source level maps (`lib.rs:9952–10008`,
`candidate_source.rs:507–517`). Lambda I/R and scoped a/t/C/S constructors use
that level (`lib.rs:11158–11160`; `candidate_effect.rs:823–862,1304–1433`).
All these rows start with `non_generic = false`.

The left schedule is, in order:

1. `Fact`: BottomEffect <: B, then B <: EmptyEffect; Name lookup is pure
   (`candidate_source.rs:344–355`). Its Value endpoint is P, not the otherwise
   allocated Name Value facade (`186–192`).
2. `Fact`: BottomEffect <: Q, then Q <: EmptyEffect; these precede Lambda
   admission (`candidate_source.rs:420–434`; `shadow_apply.rs:974–983`).
3. `Lambda`: allocate I/R; admit I <: R, then B <: R; construct the positive
   native Function and admit it to L (`lib.rs:11121–11249`).
4. `Annotation`: construct the negative checking interface, then the positive
   exposed interface; check L against the former; admit the latter to D
   (`candidate_source.rs:452–464`; `candidate_effect.rs:1094–1130`). There is no
   root computation-effect annotation here (`1185`).

Each use definition has BottomEffect <: its Name computation row, then that
row <: EmptyEffect, then `Module(left)`, then its final `Link` to its definition
root (`candidate_source.rs:344–354,467–469`). The incoming use level is 1
(`lib.rs:1317–1322`). Dependency-first graph planning completes and captures
left before executing its external use schedules (`candidate_scheme.rs:681–756`).
The relative scheduler order of first versus second is not asserted; either
use has the same trace below with a distinct fresh map.

## Constructed views and physical source bounds

Write the Function ports in argument Value, argument Effect, result Effect,
result Value order. The native Lambda has ports

```text
F_native+  = (P-, I-, R+, P+).
F_check-   = (a+, BottomEffect+, C-, a-).
F_exposed+ = (a-, EmptyEffect-, S+, a+).
```

Whole-annotation construction starts at positive variance. Argument variance
reverses; its omitted Effect row produces the indicated Bottom/Empty leaves.
The covariant result row creates one view v with allowed nominal set `{E}` and
tail t. Negative construction installs `C - Allowance(v)`; positive construction
installs `S + Support(v)`, reusing a/t/v through their scoped maps
(`candidate_effect.rs:1212–1433`). Its source attachment has positive composed
polarity and Definition(left) scope. Because t exists, v has no `closed_weight`
(`598–635`). These are constructor records, not a claim about an inferred type.

The body purity facts and I <: R/B <: R establish `R + BottomEffect` by ordinary
opposite replay: B already has BottomEffect as a lower when B <: R installs its
upper R. Comparing F_native against F_check emits, in port order:

```text
a <: P; BottomEffect <: I; R <: C; P <: a.
```

All row levels are equal, so row/row application stores negative bounds on the
lower endpoint (`candidate_extrusion.rs:702–709,736–743`). Consequently a has
upper P and P has upper a. R <: C installs `R - C` and replays its existing
BottomEffect lower, installing `C + BottomEffect`. This meets the constructor's
Allowance(v), producing BottomEffect <: Allowance(v), which returns successfully
without another physical bound (`candidate_effect.rs:758–759`). The exposed
Function is stored as `D + F_exposed`.

All retained bound contexts used in this captured fragment are IDENTITY:
the source wrapper function reads only closed allowances
(`candidate_context.rs:1601–1612`), v is mixed/open, Function swap preserves
IDENTITY (`1694–1714`), and identity/identity replay stays identity (`1968–1973`).
The Lambda entry origin retains its certificate without introducing a
`BothFromRight` context here. Relation interning and bound attachment deduplicate
the same pair/context (`1418–1435,1546–1557`). Thus the source bounds listed next
have one relation each; repeated endpoint admissions do not add another fiber.

## Exact capture and restoration order

The published graph is captured from D at boundary 0
(`candidate_scheme.rs:730–737`). Incoming routing recaptures that live root at
the stored boundary before freshening (`786–802`). Capture expands only outgoing
owner vectors plus Effect incoming allowance incidence. It does not traverse
ordinary direct bounds backwards.

All reached rows have level 1 and are eligible generic coordinates. The capture
row order is `[D, a, S, P, t, C]`, derived from the pending-endpoint LIFO traversal
and the row cursor (`567–604`): F_exposed interns its four ports in order
(`385–397`), so result a is expanded before S; a's upper reaches P; S's Support
reaches t; t's incoming incidence reaches C. C's ordinary upper Allowance is
already recorded by the incidence step and is deduplicated by `Capture::bound`
(`408–434`). Native L/I/R/B/Q are not reached from this exposed capture root.

The captured BoundKey sequence is:

| Position | Exact physical key | Discovery | Opposite count when restored |
| --- | --- | --- | --- |
| 1 | `BoundKey(D,+,F_exposed)` | D's exact lower | 0 |
| 2 | `BoundKey(a,-,P)` | a's direct upper | 0 |
| 3 | `BoundKey(S,+,Support(v))` | S's exact lower | 0 |
| 4 | `BoundKey(P,-,a)` | P's direct upper | 0 |
| 5 | `BoundKey(C,-,Allowance(v))` | t's incoming incidence | 0 |
| 6 | `BoundKey(C,+,BottomEffect)` | C's exact lower | 1 |

The key sequence uses one fiber per key under the successful-route hypotheses.
The Value cycle a→P→a contributes two negative bounds, so it creates no opposite
lower for either row. It does not supply recorded parent/copy provenance.

Freshening maps each of the six rows to a fresh level-1 identity
`D_u,a_u,S_u,P_u,t_u,C_u` (`candidate_scheme.rs:841–852`). Support and Allowance
share the same newly allocated view `v_u` with tail `t_u`, because both remap the
same `(v,t_u)` in one use-local map (`879–889`; `candidate_effect.rs:697–711`).
The source's nominal E identity is retained. No captured row maps to a shared
older owner. Context payload roots are IDENTITY, so they add no further view/tail
capture records. The reconstructed positive Function uses `a_u` and `S_u`.

Fresh relation transport precedes each physical restoration
(`candidate_scheme.rs:1019–1032`). The first five restores have no opposite
bounds and publish no callback. At position 6 the only upper of C_u is
Allowance(v_u). Restoration forms the one ordered Cartesian pair

```text
lower input: BoundKey(C_u,+,BottomEffect)
upper input: BoundKey(C_u,-,Allowance(v_u))
task:        BottomEffect <: Allowance(v_u)
context:     IDENTITY
```

Its callback owns the use occurrence/cause and calls `constrain_live_item`
(`candidate_extrusion.rs:611–640`). Operand checking returns without adding a
row bound. The restored owner/vector/fibers remain unchanged during that drain.
No contextual or nominal Effect conflict is introduced by this Bottom case.
This is a static transition derivation, not an observed callback count.

## Why this source cannot provide the assigned witness

Every structural Value comparison in this source extrudes at a receiver level
of 1. Its reachable ports are also at level 1, so `candidate_extrude` takes the
`original_level <= target` branch (`candidate_extrusion.rs:81–94`) and allocates
no row copy or parent record. Freshening allocates generic coordinates directly;
it does not call `retain_extrusion_parent`. Effect application does not add a
separate extrusion route. Under the normal fresh-session trace, the parent
record list therefore stays empty.

The nested Bottom/Allowance callback reaches the empty-worklist settlement
boundary, but `settle_candidate_intrusion` finds no parents and clears dirty
state (`candidate_intrusion.rs:370–372`). It cannot replace C_u or grow its
opposite vector through a parent/copy merge. Ordinary insertion replay is also
irrelevant inside this callback because the operand case inserts no bound.

After all six restorations, route/link comparisons can add outgoing row bounds
and replay F_exposed_u into the use facade and use definition root. These are
later admissions, with level-1 ports and no copy creation; they do not change
the already completed restore-loop trace. The fresh coordinates are not
connected back to source D/a/S/P/t/C by physical constraints, so the other use
recaptures the same left interface with another independent map.

The precise failed source step is **shared-owner capture**: incidence is real,
but its C is local at boundary 0 and freshens to C_u. This program also never
creates actual copy provenance. It therefore cannot test R under nested
representative changes. No conclusion about arbitrary source R, lifecycle,
nonidentity fibers, diagnostics, or publication follows from this negative
case. Allocation failure and rollback/retry were not explored.

Recommended next action: use this source as an exact exclusion and return to
the primary for a source whose normal construction actually creates level
separation and a shared incoming-allowance owner. Do not substitute API-injected
copies or another flat-use variant for that missing source step. Keep R open.

## Checks, budget, and dependency snapshot

Checks: bounded sequential `rg`, `nl`/`sed`, and `sha256sum` source reads; clock
read at start `2026-10-10 11:56:11 UTC`. No Git commands, parser/solver execution,
tests, builds, probes, mutations, benchmarks, or descendants. One command ran
at a time; zero heavyweight processes and zero measurement samples. CPU/RAM
totals are unknown. The 45-minute wall budget was not approached. There are no
seeds, search ranges, executable oracle, or omitted executable shards.

The method shares the compiler transition implementation with the constructive
lane. It independently targets one source schedule, but it is not an independent
review or an independent semantic oracle. Success of the actual fixture and
the claimed runtime sequence remain unverified without execution. No broader
source-program search was attempted after this source failed the shared-owner
condition. Only this new leased note was written.

## Independent review

The independent compiler-referee delta review found no BLOCKING or major
mismatch. It accepted the six level-1 captured rows, capture order, single
Bottom/Allowance restore comparison, and absence of extrusion copies/parent
records as a bounded static derivation. It confirmed the note leaves R open.
All eleven current dependency SHA-256 values match the frozen note. Review did
not independently check Git membership or branch identity, and did not execute
the authored fixture. Parser/HIR success, callback counts, supported-source
certification, rollback/retry, arbitrary witnesses, nonidentity contexts, and
general R/lifecycle closure remain unverified.

Direct dependencies were hashed on first read and rechecked unchanged before
writing:

| Dependency | SHA-256 |
| --- | --- |
| HIR `module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| HIR `module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| solver `lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| contextual attachment/admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

## Commit packet

- Exact lease: `notes/progress/2026-10-10-canonical-bound-fiber-within-use-trace.md`.
- Baseline: `d7ccbd6f7849d6b2b029fd2028383ebc938a9d09`.
- Changed dependency hashes: none observed; no dependency edited by producer.
- Review status: independent compiler-referee review found no BLOCKING/major
  mismatch; bounded source characterization only, with no R closure
  or supported-source certification.
- Checks already run: static source/HIR/call-order reads and dependency hashes;
  no executable verification.
- Commit: `dfeb75cca research: trace mixed effect capture without shared owner`.
- Shared deltas left for primary/curator: the exact six-key trace, fresh checking
  owner, single Bottom/Allowance callback, absence of parent records, and the
  remaining source requirement for level separation/shared-owner capture.
  No shared task/index/theory/question records were edited.
