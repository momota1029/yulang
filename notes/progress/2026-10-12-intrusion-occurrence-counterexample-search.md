# Extrusion-occurrence intrusion: correlated helper counterexample search

Date: 2026-10-12
Status: frozen unreviewed research; conditional native-source counterexample,
not an established refutation of the complete Yulang inference contract
Baseline: `c15ecbaa32c3d681162e85dd6643ae3af8f8b53c`
Lease: this file only; no delegation, compiler changes, builds, tests or Git mutations
Budget: one reasoning lane, at most 30 minutes; no executable search

## Objective, authority and result

Test the approved rule: an actual extrusion occurrence retains its origin
Value, receiver Value and generated polar parent/copy pairs; if its Values
share a component in the approved actual Value-reference graph, equate every
retained pair of that occurrence. Type copies do not inherit Value incidences;
freshening alone is not extrusion.

Governing sections are:

- [Parent-copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md):
  Selected operation; Value-reference SCC clarification; Apply-result source
  ownership; Nested Apply membership; Definition-root Value ownership.
- [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md):
  Approved extrusion-event qualification; Qualification; Implementation and
  proof boundary; final source/generalization preservation requirement.
- [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md):
  Decision and Scope and proof boundary.
- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md):
  §§1–5 and Authority and integration.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md):
  §§2–3, selecting construction §§3–5. Native levels below do not establish
  correspondence to its complete scoped Yulang package.

The read-only native algorithm reference is original Simple-sub revision
`9bae772624c23b52a93c1b226157e16898b4d9db`, in
`/home/momota1029/rust/simple-sub-reference`. Its `syntax.scala` constructors
and `Typer.scala` rules are evidence for the original algorithm, not semantic
authority for missing Yulang Call, effects, source admission or Generalize
bridges. No current Yulang compiler code was inspected to choose a meaning.

**Result:** the native source term in §1 has a complete successful original
Simple-sub derivation. Its two helper uses independently refine one returned
argument under a shared upper bound; this independence follows from the actual
`freshenAbove` rule, rather than being assumed. If the qualifying argument
equality is enforced in that helper's template before these uses, or transported
into their instantiated equality clauses, the term fails with `bool <: int`.
This is a conditional source counterexample to that equality/generalization
combination. The approved occurrence rule does not select scheduling or the
transport of a newly added equality into already-created frames, so the result
does not establish failure for every possible implementation of that rule.
The complete Yulang source-qualified refutation remains OPEN.

## 1. Source witness and approved graph

Use these original-reference AST constructors, written as a term rather than
as an untested parser string:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

All constructors occur in the original grammar: recursive/nonrecursive Let,
Lambda, App, Record, Var and integer Lit. `succ : int -> int` and `true : bool`
are original builtins. No handwritten client constraint, annotation, custom
primitive or modified helper transition is introduced. The two applications
of g, the integer consumer and boolean argument are source syntax. The source
may diverge through recursion; termination of its evaluation is not a premise
of the original typing rules. No successful runtime execution is claimed.

Let F and G be the distinct definition-root Values for f and g, and Y the
formal y. Definition ownership gives F→G from both uses of g, and G→F from
the direct `f y` in G's initializer. The nested g initializer's Names belong
to G. Thus F/G share a nontrivial SCC; source levels do not filter that cycle.
References to y and builtins add outgoing incidences without removing it.
Apply ownership also supplies inner-result references to F/Y; it does not
identify that result with G or contribute a containment edge.

The negative demand extrusion caused by the direct `f y` is the same owning
G-to-F call seam as the approved nested discriminator. Subject to faithful
occurrence construction on this term, its origin is G and its receiver F.
The wrapper returns y but does not erase the call or its actual source
incidence. The approved rule then qualifies both actual pairs `(C,B,+,1)`
and `(D,R,-,1)`. No type-copy vertex, bound edge or provider edge is used to
establish qualification.

This is a small exhibited witness, not a globally smallest AST theorem.
Removing the recursive call removes the forced extrusion; returning its
result directly removes the independent input/output correlation used by the
separator; removing either heterogeneous use or the integer consumer removes
the shown contradiction. A Record/Selection wrapper can replace the ignoring
Lambda/App, but that alternative is not needed for the derivation.

## 2. Exact successful native generation and replay

Use o for f's recursive placeholder and A for unused outer formal x, both at
level 1. Native `typeLetRhs` infers g's initializer at level 2 and publishes
it at boundary 1. B types y, Z types z, R is the inner `f y` result, and S
is the wrapper App result; all four are initially level 2.

1. Recursive registration allocates o at level 1; the outer Lambda allocates
   A at level 1. Monomorphic lookup f returns the same o.
2. Lambda z.y returns `Function(Z,B)`. The argument `f y` generates
   `o <: Function(B,R)`.
3. The demand has level 2, so direct insertion on level-1 o fails its level
   guard. Negative Function extrusion to level 1 creates positive copy C of
   B and negative copy D of R, in one polar memo. It records the constraints

   ```text
   B <: C       D <: R       o <: Function(C,D).
   ```

   Specifically U(B) receives C, L(R) receives D, and U(o) receives the
   copied Function. C and D start with empty copied selected lists. Their
   levels are 1. These are actual created copies, not fresh-use rows.
4. The wrapper compares `Function(Z,B) <: Function(R,S)`, generating
   `R <: Z` and `B <: S`. Since both sides have level 2, the left-variable
   branch records these in U(R) and U(B), respectively. There is no equality
   B=R and no type relationship from the discarded result back to B.
5. Publish g as `PolymorphicType(1,Function(B,S))`. Its reachable graph has
   B with upper bounds C and S. R/Z/D are not reachable from this returned
   Function graph. B/S are above boundary 1; C is retained at level 1.
6. The first g lookup invokes one coherent `freshenAbove(1,...)` map at level
   1. It creates B0/S0 with `B0 <: C` and `B0 <: S0`, retaining C. The App
   `g 0` creates V0 and generates `int <: B0`, `S0 <: V0`. Actual replay
   adds int to the lower lists of C, S0 and V0.
7. The source `succ (g 0)` generates `V0 <: int` and `int <: W0` for its
   App result W0. V0's existing int lower replays successfully against int.
8. The second g lookup uses a new coherent map, creating distinct B1/S1
   while retaining the same C. `g true` creates V1 and generates
   `bool <: B1`, `B1 <: C`, `B1 <: S1`, `S1 <: V1`. Replay adds bool to C,
   S1 and V1. C has no upper bound to B0, S0 or V0: sharing the upper
   approximation does not reverse either inequality or merge the instances.
9. The outer formed type is
   `Function(A,Record(a:W0,b:V1))`. Recursive completion places it below o
   and replays o's upper `Function(C,D)`, generating

   ```text
   C <: A
   Record(a:W0,b:V1) <: D.
   ```

   A has no upper constraint, so C's int/bool lowers propagate to A without
   failure. D has no upper constraint, so the record lower is accepted.
10. Publish f at boundary 0. The final Name f uses ordinary coherent
    freshening. It imposes no extra consumer, so no new error is introduced.

Each potentially failing primitive check in this trace is int against int.
The complete recursive demand replay does not produce bool against int.
The original recursive root is monomorphic throughout; that fact constrains
both helper argument instances below one C/A, without equating them.

An explicit solution of all generated inequalities is:

```text
T = {a:int,b:bool}
A = top                   o = top -> T
C = int | bool            D = T
B = bottom                S = bottom
R = T                     Z = T
B0 = S0 = V0 = W0 = int
B1 = S1 = V1 = bool.
```

Top/bottom/union here are semantic algebraic types, not invented internal
SimpleType constructors. In particular `top -> T <: (int|bool) -> T` is the
correct contravariant Function judgment. This assignment illustrates the
successful derivation; the replay steps, not the assignment alone, establish
success of the original algorithm.

The corresponding ordinary algebraic source checking derivation can fix f
to `(int|bool) -> T`. Under `beta <: int|bool`, f y returns T; `lambda z.y`
can accept T and returns beta. Hence g has the bounded relationship
`forall beta <: int|bool. beta -> beta`. Its int and bool uses check the
two displayed fields and reconstruct T, satisfying the recursive assumption.
This fixes f's argument contract throughout: no polymorphic recursive f or
independent choice of f's root is used. A proof that this is the principal
public Yulang scheme is not claimed.

## 3. Discriminating equality and the precise remaining premise

Suppose actual occurrence equality C=B is enforced before g publication, or
the complete equality clause is included in each lawful g frame while C stays
the original native boundary-1 anchor. It is immaterial whether an encoding
canonically lowers B to C or keeps two IDs with enforced equality.

The first frame then has `B0=C`, so `B0 <: S0 <: V0 <: int` gives C<:int.
The second source use gives bool<:B1=C. Transitivity requires bool<:int,
which the original distinct primitive constructors reject. Equality D=R
does not cause this particular conflict: both can already have type T in the
successful assignment. Equating only that result pair misses the witness;
the approved rule selects every pair of this qualified occurrence.

The fault is not that native recursion supplies no common argument contract.
It does supply C/A. The fault in this conditional combination is replacing
each fresh beta *below* that contract with the contract itself, when beta is
also returned by the helper. Two independent uses are decisive because their
returned types must retain separate correlations with their supplied arguments.

The distinction between early and late settlement is material. The approved
document leaves SCC scheduling and transport unspecified. If C=B is added
only after B0/S0 and B1/S1 have already been allocated, and their independent
descriptions are left intact, equality between original B and C alone need
not relate B0/B1. The immediate failure above does not follow for that history.
The original g scheme's later uses would nevertheless need a justified
interpretation of its newly equated template. This note does not choose or
validate a delayed policy, identify old frames with new ones, or assert that
all old frames must be rewritten.

Exact premise for the conditional refutation:

```text
The qualifying G→F occurrence imposes C=B in the original g description;
g uses enforce that equality with the fixed native boundary-1 C anchor.
```

What remains unestablished is whether the approved complete Yulang
Generalize/Call and occurrence transport construction imposes precisely that
premise on this admitted source. Original Simple-sub has no intrusion owner or
scheduling rule. Selected Source Generalize retains complete clauses and
original scopes, but the correspondence of the native C anchor and g/f source
components is not established here. Value SCC membership alone is not a
generalization-component declaration. No alternative graph or source scope
has been selected to remove the issue.

## 4. Other attacks and coverage

- Bare `id x=x`: ordinary coherent freshening gives one type variable per
  independent use; there is no extrusion pair. Equating those fresh-use rows
  by the present rule would be a mutation, not an attack on the approved rule.
- Bare `konst x=0`: its result is the ground int type; the unconstrained formal
  creates no bare-definition extrusion. `konst 1` references konst even though
  its returned provider is 0. Provider identity cannot suppress that edge.
- Direct nested `g y=f y`, including the recorded f/g discriminator: the
  result has the shared lower approximation D, rather than returning a
  correlated independent argument beta. Heterogeneous arguments alone do
  not produce the separating primitive conflict used in §3. No general
  safety theorem for this candidate is claimed.
- Exact `my odd/even`: retain the accepted cross-level O/E SCC and original
  arithmetic/conditional source. This pass does not supply its missing exact
  Call/Branch/admission derivation or replace it with the pure witness above.
  No counterexample is asserted for its natural int/bool behavior.
- Repeated and memoized extrusion: the witness has one actual negative
  demand extrusion, with two keys `(B,+)` and `(R,-)`. Opposite polarities are
  preserved, not collapsed. It needs no memo collisions, reused occurrence ID
  or fabricated provenance. Additional repeated/memoized occurrences,
  same-parent opposite-polar copies, mutual recursive groups and effect ports
  are not exhaustively covered.

No seeds, random ranges, enumeration counts or mutation executions exist:
this was a finite source derivation, with two independent g instantiations,
one qualifying occurrence and two retained polar pairs. The first direct-call
attack lacked returned-input correlation; the second changes that mechanism.
Further toy variants would leave the equality/generalization transport premise
untouched, so no third equivalent probe is proposed.

## 5. Checks, resources, dependencies and next action

Checks: read-only original constructor/rule inspection, hand derivation of
all native generated constraints and recursive completion, authority reads,
SHA-256 snapshots/recheck, and note whitespace check. No executable checker,
tests, builds, Oracle run, parser execution, timing measurement, compiler edit,
child launch or Git mutation. No claim of independent review or production
conformance. One lightweight read/hash process at a time after initial batched
reads; no heavyweight process. CPU/RSS and exact reasoning time were not
measured. The single pass remained within its assigned 30-minute cap.

Oracle independence: the direct source typing judgment and exact native replay
are two arguments, sharing primitive, subtype, recursive-binding and native
generalization rules. They are not independent empirical oracles. The typing
argument does not establish missing Yulang local laws; no checker assuming
transitions was offered as proof of their source generation.

Direct dependency SHA-256 snapshots:

| Dependency | SHA-256 |
| --- | --- |
| Parent-copy decision | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Occurrence qualification | `0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Source Generalize decision | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Original Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Original syntax.scala | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |

Recommended next action: the primary's constructive lane instantiates the
complete approved occurrence/generalization transport on this exact source,
determining whether C=B is required in the two g-use frames. That single
premise distinguishes the shown native rejection from delayed histories;
increasing a model's search range cannot settle it. Keep the parent equality,
source correspondence, soundness/principality and cutover gates OPEN.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-12-intrusion-occurrence-counterexample-search.md`.
- Baseline SHA: `c15ecbaa32c3d681162e85dd6643ae3af8f8b53c`; original reference
  baseline `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none caused by this worker; final dependency
  recheck matches the snapshots above. Primary owns comparison against pinned
  Git blobs and any concurrent baseline movement.
- Review status: frozen unreviewed conditional native-source research;
  no complete-Yulang refutation or theorem closure.
- Checks already run: exact native manual generation/replay and source
  solution derivation, dependency hashes and document whitespace integrity.
  No executable or production verification.
- Proposed one-line research-checkpoint message:
  `research: expose correlated helper boundary in occurrence-wide intrusion`.
- Shared-record deltas left to primary/curator: record this conditional witness
  and its equality/frame-transport premise; retain native and full Yulang
  claims separately and keep the parent gate OPEN. No shared file was edited.
  Writes stop at submission for frozen review.
