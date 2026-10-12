# Odd/even intrusion: independent bounded declarative check

Status: unreviewed research checkpoint; conditional structural characterization.
Parent soundness/principality and exact-source correspondence remain OPEN.
Baseline supplied by primary: `316227ff18a50fdae3f3fb523bf694bd2295bd24`.
Branch supplied by primary: `research/simple-sub-intrusion`.
Lease: this file only. Method: manual constraint elimination and minimized
model witnesses; no compiler implementation or semantic decision.

## Objective, authority and independence

The assigned question is whether the approved Value-SCC-qualified parent/copy
equalities preserve soundness and required principality for the exact source:

```text
my odd n =
  my even n = if n <= 0 { true } else odd(n - 1);
  even(n - 1)
```

Governing locations are:

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  §§1–3 and Evaluation: retain ordinary deterministic Simple-sub structure;
  soundness/principality/termination/progress need proofs, with implementation
  derived from those proofs.
- `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, Direct decision,
  Selected operation and compiler responsibility, and Value-reference SCC
  clarification, read through the later association clarification.
- `notes/design/2026-10-12-intrusion-value-type-association.md`, Direct
  clarification, Approved extrusion-event qualification, Definition-root
  origin for nested call-demand extrusion, Qualification, and Implementation
  and proof boundary.
- `notes/design/2026-10-12-value-reference-copied-row-ownership.md`, Decision
  and Scope and proof boundary.
- `notes/theory/2026-10-12-odd-even-copy-qualification-proof.md`, §3's finite
  native construction, with its earlier copy-vertex qualification argument
  read subject to the later association clarification.

Accepted qualification: an actual extrusion event retains its actual polar
pairs, origin Value E and receiver Value O. O and E have the approved root
references in both directions, so their Value SCC qualifies that event's
pairs. The equality acts on types. Its antecedent does not require the type
copies themselves to be Value vertices or to acquire incoming incidences.
Copies inherit no Value incidence, and Names keep original binder targets.
This note does not recompute the Value SCC, use a type-bound graph as that
graph, or propose a permanent Value owner for every type endpoint.

The method is independent of the earlier copy-vertex argument: eliminate
generalized variables from ordinary Function-subtyping judgments and compare
the resulting observable type constraints. Its input allocation trace is the
finite history in the pinned note, rather than an independently executed
reference. Consequently it cannot validate that history's source producers.
There is no executable oracle. The two compared systems share the displayed
trace, ordinary structural Function subtyping, and the stipulated ordinary
bounded generalization. Neither supplies complete Yulang Call or effects.

## Structural input and explicit hypotheses

Use the deliberately smaller native term:

```text
let rec odd = lambda a.
  let even = lambda b. odd b
  in even a
in odd
```

This changes the original computation. It removes Branch, `true`, `<=`, and
`-`; no translation or admission theorem is claimed.

Hypotheses of the characterization below:

1. Types form a preorder with reflexive/transitive `<:`. Function subtyping
   satisfies `(X -> Y) <: (U -> V)` iff `U <: X` and `Y <: V`.
   Equalities fix the same type, or its equivalence class under mutual
   subtyping. The concrete witnesses below use distinct ground classes.
2. The recursive outer occurrence is monomorphic while its body is inferred.
   A is its parameter at level 1. The inner even parameter B and the inner
   odd Call result R are at level 2.
3. The inner demand on the outer recursive root is `B -> R`. Negative
   extrusion to level 1 creates the actual polar copies C of B and D of R,
   leaving `B <: C` and `D <: R`, and demands `C -> D` of the outer root.
   At this finite cut there are no other selected bounds on B or R.
4. Ordinary inner publication at boundary 1 quantifies B and R; C and D are
   fixed anchors. A use coherently creates its own B_i and R_i, retaining
   `B_i <: C` and `D <: R_i`. This is the structural analogue's generalization
   premise, not a proof of full Source Generalize registration.
5. B appears only negatively in the scheme body and through its displayed
   upper anchor bound; R appears only positively and through its displayed
   lower anchor bound. No extra constraint, effect interface, shared witness
   or correlated observation mentions these generalized rows.

Ordinary App for the existing outer `even a` creates S and gives
`A <: B_0`, `R_0 <: S`. Recursive completion compares `A -> S` against
`C -> D`, giving `C <: A`, `S <: D`. Thus the finite pre-equality system is

```text
B <: C        D <: R
B_0 <: C      D <: R_0
A <: B_0      R_0 <: S
C <: A        S <: D
```

This follows directly by Function variance once hypotheses 2–4 supply the
construction. In particular, completion's argument constraint is `C <: A`;
reversing it would change the check.

## Quantifier elimination and the fresh-use check

At the publication boundary, inner even has the bounded structural scheme

```text
forall B,R. (B <: C and D <: R) => (B -> R)
```

For fixed C,D, every allowed instance satisfies

```text
(C -> D) <: (B -> R).
```

The anchor instance B=C,R=D is itself allowed. Therefore C->D is the least
arrow instance in this particular bounded family. This conclusion uses
ordinary Function variance; it does not follow from Value SCC membership.

More explicitly, for any finite number m >= 0 of independent simple App uses
with argument types X_i and demanded result types Y_i, each fresh frame adds

```text
X_i <: B_i <: C       D <: R_i <: Y_i.
```

Eliminating that frame gives exactly

```text
X_i <: C             D <: Y_i.
```

Necessity is transitivity. Sufficiency chooses B_i=C and R_i=D independently
for every i. The existing outer use additionally gives

```text
C <: A <: B_0 <: C    D <: R_0 <: S <: D,
```

so its projection is exactly `A` mutually subtype-equivalent to C and S to D.
The original initializer rows B,R can also be eliminated by choosing C,D.

Now add the approved finite pairs `B=C` and `R=D`. These equalities do
collapse the generalized parameter and result rows with their fixed anchors.
If established before publication, they remove B/R as independent generic
coordinates. If faithfully retained by a scheme/frame representation later,
they likewise fix those coordinates wherever the equation is transported.
The candidate compiler's actual recapture/transport is not assumed here.

In the resulting structural system, the inner function has type C->D.
Its Apps require exactly `X_i <: C` and `D <: Y_i`; the existing outer App
and completion require exactly the same mutual-subtyping constraints on
A,C and S,D. Consequently, for every fixed valuation of the anchors, outer
ports, and the finite simple-App observations, there exists a pre-equality
extension iff there exists a post-equality extension.

Claim class: conditional projection-equivalence theorem for this displayed
type-only system, for all m >= 0 and all preorders satisfying hypothesis 1.
It rules out a fresh-frame principality counterexample using only these
ports and bounds. It is not an established source principality theorem or
an independent review. Arbitrary complete Calls, effects and additional
scheme relations are outside its quantifiers.

## Smallest model discriminator and a premise mutation

Raw valuations are not preserved by equality. In the usual strict lattice
fragment `Bottom <: Int <: Top`, `Bottom <: Bool <: Top`, choose

```text
A=C=B_0=Int      D=R_0=S=Bool
B=Bottom        R=Top.
```

All eight pre-equality inequalities hold, but both proposed equalities fail.
This is a concrete countermodel to the stronger assertion that every old
satisfying valuation already obeys the equalities, or remains unchanged by
them. It is not a counterexample to projected acceptance or principality:
changing only B to Int and R to Bool supplies the post-equality extension
without changing the public ports. The witness needs no extra source term,
primitive interpretation, execution, or copy-vertex assumption.

The one-polar hypothesis is a real limitation. As a discriminating mutation,
replace the inner scheme body with `B -> B`, keeping only `B <: C`, and set
C=Top. One Call with argument Int and demanded result Int is satisfiable
before equality by B=Int. After `B=C`, it requires `Top <: Int`, which fails
in the strict lattice above. This one-call type-level witness attacks precisely
the shortcut "all anchored generalized coordinates may be equated". It is
not an inferred source program, not the odd/even scheme, and not an additional
counterexample to the approved source rule. No claim is made that this mutated
scheme can arise at a qualifying occurrence.

Only one fixed history, one old-valuation witness, and one named scheme-body
mutation were examined. There are no random seeds, sampled ranges, or
exhaustive enumerations. The all-m statement is a symbolic elimination, not
experimental coverage.

## Exact-source boundary and next action

In the unchanged source, the inner demand's argument is the result T of
`n - 1`, not necessarily the inner formal B. A ground T would not introduce
the analogue's C/B pair. Other wrong-level variables inside T or selected
bounds may introduce different actual pairs. The result R is still a fresh
Call result, but it appears inside the Branch and the complete function
description. Its constraints cannot be replaced with the lambda-only
description by assumption.

The first unavailable exact-source derivation is the typed primitive Call for
the inner condition `n <= 0`, before assigning a Branch rule. The arithmetic
argument of the original `odd(n - 1)` then requires its own actual primitive
Call and type T. No rule for those primitives, Branch, source admission,
empty effects, complete four-port Call, or faithful source/native map was
supplied by this calculation. Complete Call/effects and original-source
preservation therefore remain OPEN. O/E root SCC eligibility is accepted;
it does not prove the one-polar structural premise or complete registration.

No source-qualified counterexample was constructed. Another lambda-only
probe would leave the same premise untouched. One recommended next action:
derive the complete original inner even description at its owning primitive,
Branch and Call constructors, retaining the actual extrusion pairs and
publication/frame coordinates; check whether each equated generic coordinate
has only the one-polar anchor use proved above. Any extra correlated or
shared occurrence must be tested directly rather than eliminated by this
lemma. Keep the original parent A/B gates OPEN during that action.

## Checks, dependencies and resource accounting

Three short, sequential read processes ran: `cat` for the three required
rules; a Python file read for the skill/tasks/index/governing notes; a bounded
Python read/hash capture for governing designs, the qualification note and
reference-source location. Two captures were oversized/truncated. Relevant
missing governing locators, decisions and hashes were then supplied by the
primary through internal messages. Full task/index material and direct Scala
or compiler correspondence were not independently established by these reads.

No tests, builds, executable experiments, network calls, Git operations,
formatters, child agents, or writes outside this lease. No parallel local
processes. Reported read-process elapsed times sum to about 3.14 seconds;
CPU time, peak RSS and total reasoning wall time were not measured. The packet
has a 35-minute wall limit and a three-process limit; no further process is
run for this artifact. The note was created with `apply_patch`; automated
whitespace/link checks were not run. Primary owns final dependency recheck,
scope inspection and any independent review. Writes stop at submission.

Direct dependency snapshot (only parent-copy hash was visibly captured by
this worker; the other current hashes below were supplied by the primary):

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/theory/2026-10-12-odd-even-copy-qualification-proof.md` | `efffb130ce708d6cbe89a42a0b482d62c9dd93dceedb345fd084ad6370cc3bae` |

No dependency was edited by this worker. Equality-satisfaction, incidence
coverage, source registration, faithful frame transport, complete Call,
effect hygiene, global soundness/principality and production cutover are not
verified by the artifact.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-13-odd-even-intrusion-falsification.md`.
- Baseline SHA: `316227ff18a50fdae3f3fb523bf694bd2295bd24`.
- Changed dependency hashes: none caused by this worker; current snapshot
  above requires primary comparison with the pinned revision before integration.
- Review status: unreviewed, research-only; no self-certification or gate closure.
- Checks already run: three static read processes; manual variance/quantifier
  derivation; explicit pre-equality model and one-polar mutation calculation.
  No tests/builds/runtime/automated artifact checks.
- Proposed one-line checkpoint commit message:
  `research: characterize odd-even fresh-frame equality by declarative elimination`.
- Shared-record deltas intentionally left for primary/curator: record bounded
  projection equivalence under the five explicit premises; distinguish raw
  generalized-frame collapse from lost observable instantiations; retain exact
  primitive/Branch/complete Call and source-to-frame correspondence OPEN.
  No shared record modified; artifact frozen at submission.
