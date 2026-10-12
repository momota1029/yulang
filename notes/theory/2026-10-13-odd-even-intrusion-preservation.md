# Odd/even: finite intrusion calculation and exact-source boundary

Status: unreviewed research checkpoint; no theorem or implementation gate closed
Claim class: finite algebraic derivation and bounded source characterization
Baseline: `316227ff18a50fdae3f3fb523bf694bd2295bd24`
Branch assigned by primary: `research/simple-sub-intrusion`
Output lease: this file only; leaf assignment, no delegation

## 1. Frozen original claim and authority

The requested source is exactly:

```yulang
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

Keep the two `n` binders distinct: `n_O` belongs to `odd`, and `n_E`
belongs to `even`. Let `O,E` denote the **source definition Values**. They
are not Function ports, native type coordinates, or Lambda/Apply roots.
The approved definition-root incidences are `O -> E` and `E -> O`.
The inner call `odd(n_E - 1)` belongs to `even`; its approved extrusion
origin is `E` and receiver is `O`. Thus an authentic extrusion occurrence
with those endpoints qualifies its actual retained polar pairs. For its
argument-type parent `T` and result parent `R`, the selected equalities are
`C=T` and `D=R`. In particular, `T` is not silently identified with the type
of the formal `n_E`.

The parent claim is preservation of the original declarative typing and
required principal result by adding those qualified equalities to the actual
finite native derivation, at the original source scopes, with the original
operators, Branch, complete Call, effects, annotations and world assumptions.
It quantifies over the actual lawful typings/instantiations of this source,
not over independently chosen argument/result witnesses or a substituted
lambda program. None of those original obligations is narrowed here.

Governing sources and exact sections:

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
  §§1–5 and Authority and integration: native generation, accumulation,
  propagation, levels, extrusion, intrusion and generalization; necessary
  abnormal-path safety; no ordinary-inference restrictions for proof convenience.
- [Parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
  Selected operation and compiler responsibility, Value-reference SCC
  clarification, and Definition-root Value ownership: actual Value references
  supply `O -> E -> O`; subtype/bound edges do not supply that graph.
- [Value/type association](../design/2026-10-12-intrusion-value-type-association.md),
  Approved extrusion-event qualification and Definition-root origin for nested
  call-demand extrusion: select only the retained pairs of the actual E/O
  occurrence. This decision expressly leaves preservation and transport open.
- [Copied-description ownership](../design/2026-10-12-value-reference-copied-row-ownership.md):
  copying a type description does not copy incidences or retarget resolved Names.
- [Earlier qualification note](2026-10-12-odd-even-copy-qualification-proof.md):
  its type-copy-vertex application was withdrawn by the association decision;
  it supplies no nonqualification argument for this task.
- [Ordinary Simple-sub import](2026-10-11-parreaux-simple-sub-proof-import.md),
  §§2–3 and 6: original generation/replay/coalescing, theorem quantifiers,
  and the exclusion of let polymorphism from the paper's §5 proof scope.
- [Pinned odd/even native derivation](2026-10-12-odd-even-parent-copy-scc-derivation.md),
  §§2–4: ordinary reference derivation and candidate producer/consumer prefix.
- `rules/compiler-engineering.md`, Natural compiler behavior and
  proof-obligation economy; `rules/design-authority.md`, Authority order;
  `rules/agent-orchestration.md`, Proof delegation and decomposition and
  Model routing and Astra escalation; `rules/research-lab.md`, Compact
  assignment packet and Commit conveyor; `rules/git-concurrency.md`,
  Disjoint-file mode. These govern process, not a new semantic premise.

## 2. Exact-source stop: the original argument judgment

For the selected inner call, the smallest child judgment needed before using
the known native demand is the authentic whole argument construction:

```text
original scope Γ_E and world W_E, with the actual n_E registration
actual resolved subtraction reference/contract and literal 1 introduction
-----------------------------------------------------------------------
Γ_E; W_E ⊢ n_E - 1 : Comp(E_arg,T),
with its whole delayed argument and original Call/source interfaces
```

This packet does not establish that judgment. Its owner is the actual
operator/literal source introduction and complete operator Call construction.
An unconstrained parameter, numeric native level, or retained Value incidence
does not provide the subtraction contract or its world/effect interpretation.
The approved E/O qualification does not manufacture this antecedent.
Consequently this packet stops the **exact-source** derivation there.

Additional missing inputs remain explicit: resolution and typing of `true`;
the literal `0`; the resolved `<=` contract and condition computation; the
actual Branch rule joining the two arm computations; complete inner and outer
Calls, their argument receipts, providers, result/future interfaces and ordered
suffixes; authentic recursive introduction and world; applicable annotation
and effect laws. Absence of explicit annotation syntax in this spelling does
not establish the absence of inherited annotation/protection obligations.
Nothing here assigns empty effects, an `Int -> Bool` scheme, or a completed
recursive semantic world.

The admission observations in the pinned native derivation §2 distinguish
its ordinary Y3 route from a structural analogue. They do not reject the
language-wide source or justify removing its conditional/arithmetic. No
source-qualified counterexample is established. No claim is made that a
primitive contract has no definition elsewhere; the necessary original
judgment has not been constructed in this packet.

The primary explicitly authorized the independent calculation below using
only the effect-free original arrow core. It does not continue a conditional
Yulang theorem beyond this missing leaf.

## 3. Frozen finite structural analogue and actual reference schedule

Use the following original Simple-sub grammar term solely for comparison:

```text
let rec odd = lambda n_O.
  let even = lambda n_E. odd n_E
  in even n_O
in odd
```

`even` is a **nonrecursive** local binding here. This is not the exact user
source: its two operator computations and Branch have been removed. No Yulang
effect port or complete Call interpretation belongs to this analogue.

The reference pin is `9bae772624c23b52a93c1b226157e16898b4d9db`.
The producer/consumer locators below are supplied by the independently
reviewed ordinary import and the pinned native derivation §3; the original
`Typer.scala` checkout was not found by this worker's final targeted lookup.
They are inherited source evidence, not a claim of a fresh raw-file inspection.

Freeze boundary 0 for the outer binding, boundary 1 for `even`, and fresh
empty-bound coordinates: recursive placeholder `o` and outer formal `A` at
level 1; inner formal `B` and inner App result `R` at level 2. Native type
coordinate `o` is distinct from the source Value `O` above.

1. `typeLetRhs(true,...)` allocates `o`, and Lam allocates `A`; the local
   nonrecursive RHS runs one level deeper and Lam allocates `B`
   (`Typer.scala:48–67`). Monomorphic Name lookup returns `o` itself.
2. App allocates `R` and submits `o <: Fn(B,R)` (`:62–72`). Negative
   extrusion of this high-level demand to level 1 flips argument polarity
   and preserves result polarity. The actual copies are `(C,B,+,1)` and
   `(D,R,-,1)`; their links are `B <: C` and `D <: R` (`:134–159`).
3. The rewritten demand `o <: Fn(C,D)` is admitted on `o`'s upper side.
   There is no lower provider yet, so no arrow child replay occurs at this
   insertion (`:115–123`). The inner Lam returns `Fn(B,R)`.
4. `even` publication stores `PolymorphicType(1,Fn(B,R))`. Its one later
   Name uses one shared `freshenAbove` map, producing `B',R'` at level 1
   and keeping low anchors `C,D` fixed. It restores `B' <: C` and
   `D <: R'` (`:55,:81–83,:166–207`). These are use copies, not new
   extrusion occurrences or qualifying E/O events.
5. Outer App submits `Fn(B',R') <: Fn(A,S)`. The same arrow consumer emits
   **both** `A <: B'` and `R' <: S`; installing the latter replays the
   retained `D` lower, giving `D <: S` (`:106–120`).
6. Outer Lam completion inserts `Fn(A,S) <: o`. This actual lower insertion
   replays the stored `Fn(C,D)` upper, and the same arrow comparison emits
   **both** `C <: A` and `S <: D` (`:52,:106–120`).

Thus all four original scalar port constraints, including their activation,
are:

| Role | Ordinary constraint | After qualified quotient `C=B,D=R` |
| --- | --- | --- |
| Positive argument extrusion link | `B <: C` | `B <: B` |
| Negative result extrusion link | `D <: R` | `R <: R` |
| Completed provider/demand argument replay | `C <: A` | `B <: A` |
| Completed provider/demand result replay | `S <: D` | `S <: R` |

These are four **scalar arrow obligations**, not four Yulang Function ports.
Argument and result come from one retained demand and one provider comparison.
No argument witness is independently recombined with a result witness.

## 4. Finite projected solution equivalence

This is an algebraic statement about the displayed finite systems. Quantify
over every subtype preorder with reflexivity/transitivity and an arrow
constructor contravariant in its argument and covariant in its result, and
every **joint** assignment of its types to these coordinates. Write `X ≃ Y`
for `X <: Y` and `Y <: X`. No operational progress or source realization is
assumed by that quantification.

The ordinary system has the links and child comparisons from §3:

```text
B <: C                 D <: R
B' <: C                D <: R'
A <: B'                R' <: S
C <: A                 S <: D
Fn(A,S) <: o           o <: Fn(C,D)
```

Its replayed `D <: S` is included by transitivity. The argument cycle gives
`C <: A <: B' <: C`; the result cycle gives `S <: D <: R' <: S`.
Consequently `A ≃ B' ≃ C` and `S ≃ R' ≃ D`. The original high-level
`B,R` have only their one-sided links; they are not identified by these cycles.

In the structural intruded calculation, quotient the actual `(C,B)` and
`(D,R)` pairs **before local publication**. Its stored inner arrow is
`Fn(C,D)`. Reference use-time freshening retains these level-1 anchor
coordinates, and outer App generates `A <: C` and `D <: S`. Completion
generates `C <: A` and `S <: D`. Thus it has the same boundary equivalences
`A ≃ C` and `S ≃ D`, and the same two constraints on `o`.

For every ordinary solution, keep `A,S,C,D,o` fixed and set `B:=C,R:=D`.
The two original extrusion links become reflexive, and the outer boundary
conditions just proved satisfy every intruded constraint. Conversely, extend
every intruded solution by `B:=C,R:=D,B':=C,R':=D`. Every ordinary inequality
then holds. This is one simultaneous extension; it chooses no unrelated
marginal witnesses.

Therefore the two finite systems have **exactly the same projections to
`(A,S,C,D,o)`**. Arrow congruence gives `Fn(A,S) ≃ Fn(C,D)`, and the
two constraints on `o` give `o ≃ Fn(A,S)` in every such joint solution.
The systems do not have identical solutions on all private coordinates:
intrusion constrains previously unilateral `B,R`. The proved statement is the
specified boundary projection, not that stronger false equality of full stores.

This calculation treats equality as a quotient of the actual retained
coordinates. It does not certify a particular candidate union implementation,
equality scheduling point, or source-generalization allocation. In particular,
it does not replace intrusion by repeatedly extruding newly submitted subtype
edges, nor use type-bound cycles as the approved Value SCC.

## 5. Publication, coherent uses and bounded scheme order

At the original local publication cut, the stored inner type is `Fn(B,R)`
with `U(B)=[C]`, `L(R)=[D]`; `C,D` have no own bounds yet. Original
polarity-sensitive coalescing therefore gives the relative scheme

```text
Σ(C,D) = ∀B,R. (B ∩ C) -> (R ∪ D)
```

`C,D` are fixed captured anchors in this **local** scheme, not two additional
independently quantified local parameters. This formula is for that cut; it
does not assert that later live-anchor coalescing ignores new bounds.

For every joint substitution for `B,R`, lattice rules give
`B∩C <: C` and `D <: R∪D`. Arrow variance then gives

```text
C -> D <: (B∩C) -> (R∪D).
```

The single substitution `B:=⊤,R:=⊥` makes that instance exactly `C -> D`.
Hence the family of typings obtainable by instantiation and subsumption from
`Σ(C,D)` equals the family obtainable from `C -> D`. This proves equivalence
in the required scheme order for this relative finite arrow signature; it is
stronger than merely exhibiting one successful instance.

After intrusion the inner signature is `C -> D`, with the same captured
anchors. Each original fresh use restores **both** links using one map; at
the actual outer use, the cycles in §4 force `B' ≃ C,R' ≃ D`. In the
quotient, those two ports are already shared anchors. Multiple genuine uses
of this particular inner arrow would each allocate their own `B_i,R_i` in
the ordinary system, while retaining the same `C,D`; each relative scheme
still has the equivalence above. This does not authorize assuming that an
unconstructed Yulang source clause has those incidences.

If equality is represented relationally rather than by that quotient,
the corresponding generalization calculation must retain the **whole**
equations `B=C,R=D`: fresh frames satisfy `B_i=C,R_i=D`. Dropping the
equations while freshening `B,R` is a different system and is unsupported.
This observation specifies the mathematical dependency to preserve; it does
not claim that source publication or the current candidate produces it.

There is also a direct declarative check of the changed inner arrow in the
ordinary non-let fragment. Under the original captured assumption
`odd : A -> S`, the finite constraints give `C <: A` and `S <: D`.
For `n_E:C`, subsumption supplies `n_E:A`; T-App gives `odd n_E:S`, and
subsumption gives result `D`. T-Abs derives `lambda n_E. odd n_E : C -> D`.
The same derivation with `B <: C` and `D <: R` gives the original inner
type `B -> R`. These use one callee and the same argument/result derivation.

These facts establish finite boundary equivalence and relative scheme
equivalence. They do **not** establish universal principality or semantic
soundness for the recursive-let term, its final outer freshening, recursive
coalescing/alias simplification in every store, or the original Yulang source.
The original paper's §5 proof scope excludes let polymorphism; its stated
principality theorem cannot close that gap. A syntactic raw-store coalescing
calculation is not silently replaced by the joint-solution argument above.

## 6. Native/source bridge and omissions

The pinned native derivation §4 traces the actual candidate prefix: source
Apply retains callee/argument/result and Effect endpoints
(`candidate_source.rs:394–411`); `shadow_apply.rs:1331–1383` admits the
negative **four-port** Function; opposite-bound replay
(`candidate_extrusion.rs:809–841`) activates the open root's demand;
`lib.rs:12412–12454` and `candidate_extrusion.rs:94–163,:224–249`
perform polar extrusion; `candidate_intrusion.rs:23–28,:171` retains the
actual parent records. Publication and coherent Name use are at
`candidate_scheme.rs:1316–1338,:1356–1382,:981–1019`.

Those are actual native construction/consumer owners, with inherited source
evidence from that pinned note. This packet did not complete a fresh raw-code
audit of them. Their native coordinates do not establish the missing argument
judgment in §2 or its complete Call interpretation. Both Effect ports remain
in the actual candidate Function. The scalar table and effect-free relative
scheme proof do not derive either Effect comparison, an empty effect, licensed
subtraction, provider/attachment identity, residual lineage, or world adequacy.

For the original source, the necessary bridge is: construct the authentic
`n_E-1` computation and complete inner Call; relate their actual scoped native
argument/result occurrences to `T,R`; retain the approved E/O event and its
actual polar pairs; retain its complete clause and fixed dependencies through
actual `even` publication and each coherent use; prove equality's action on
that complete judgment, including the Branch and surrounding computations.
No independent argument/result marginals, source-copy vertex test, or
reclassification supplies this bridge.

Under the existing proof-obligation-economy rules, the missing original
operator/Call law and equality preservation are A/B obligations. Recovering
lost source incidence from endpoint IDs, numeric levels or bound adjacency
would be D; constructors should retain their authentic evidence when it
already exists. This packet constructs no extra relation or source restriction.
It is a new finite calculation for the selected example, not another claim
that the earlier c1/publication obstruction audit is proof progress.

Original soundness, required principality, complete Call, effect hygiene,
source adequacy, ordinary progress, combined termination and F5/cutover gates
remain OPEN. Their statuses and shared records are owned by the primary.

## 7. Evidence, resources and commit packet

Checks performed: three short read processes for skill/rules/authority/source
notes; one additional targeted read explicitly authorized by the primary for
the native derivation §§2–4 and reference lookup. The first three captures
truncated; the decisive ordinary finite schedule was recovered in the bounded
fourth read. The reference lookup found zero `Typer.scala` copies under `/tmp`,
so no direct reference-file reread is claimed. No parser/native execution,
checker, enumeration, tests, builds or measurements ran. No Git mutations,
child jobs, shared-record writes or compiler edits occurred.

Observed baseline dependency snapshots:

```text
top-level principles    edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
parent-copy decision    6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b
value/type association  28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775
native odd/even note    238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830
```

Each displayed dependency compared byte-equal to its working-tree copy at
its read. Truncated captures prevent claiming a complete observed hash report
for the other dependencies; the primary should recheck the full dependency
set before integration. The branch and SHA above are the primary's assigned
baseline; no claim is made that unrelated later HEAD movement was inspected.

Resource use: one leaf; four sequential lightweight read commands including
the primary-authorized exception; zero heavyweight processes and zero samples.
CPU/RSS unmeasured. Assigned wall cap is 35 minutes. Requested routing is
normal `gpt-6.1-sol/high` under the unpinned prover role and configured defaults;
observed effective model/effort metadata is unavailable and **unknown**.
No Astra request or configuration reload occurred.

Next action: the primary assigns the original subtraction/literal and complete
operator Call owner to construct the authentic `n_E-1` argument judgment;
then use that judgment to instantiate the existing E/O occurrence, without
repeating the scalar arrow calculation as source proof.

### Commit packet

- Exact leased/changed path:
  `notes/theory/2026-10-13-odd-even-intrusion-preservation.md`.
- Baseline SHA: `316227ff18a50fdae3f3fb523bf694bd2295bd24`.
- Changed dependency hashes: none observed for the four snapshots above;
  remaining baseline/live dependencies require primary recheck.
- Review status: unreviewed research checkpoint; no self-certification,
  source theorem, or parent-gate promotion. Writes stop on handoff.
- Checks already run: bounded documentary/source-note reads, four reported
  pinned-byte/hash comparisons, manual finite constraint and scheme derivations;
  no executable validation or independent review.
- Proposed checkpoint message:
  `research: derive odd-even arrow intrusion projection and scheme equivalence`.
- Shared-record deltas left to primary/curator: record the finite boundary
  projection and relative local-scheme equivalence as separate unreviewed
  results; record the authentic `n_E-1` argument judgment as the immediate
  source frontier; retain every original A/B and complete-Call/effect gate OPEN.
  No shared record was edited.
