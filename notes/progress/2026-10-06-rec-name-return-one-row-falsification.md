# Falsification boundary for the recursive one-row valuation bridge

Date: 2026-10-06
Status: independently reviewed research-only countermodels and reduced proof obligation
Pinned baseline supplied by primary: `1e49e88f07fa8ceb0b05d109bab6c6a1f23d8d87`
Exclusive write lease: this file only
Method: adversarial hand construction; narrow replay-owner source read
Implementation authority: none

## Objective and authority

Attack the remaining one-row valuation premise in
`2026-10-06-rec-name-return-purefun-production-reduction.md`, rather than
repeat the member theorem's H1–H4 witness shifts. The proposed exact relation
for one incoming use is

```text
P(U) = ∃ρ. F²(ρ) ≤ ρ ∧ F²(ρ) ≤ U,
F(t) = Fun(Top,t).
```

The governing inputs are the redesign charter §§1–4, the concrete
compatibility boundary §§1 and 3, the member-scheme bridge's hypotheses and
scope, and the production reduction's exact incoming obligations, live replay
example, diagnostics, availability, and residual valuation premise. The three
research/design/concurrency rules were read in full. The charter's named
sections and concrete boundary §3 were read narrowly after an initial
combined capture was truncated; concrete boundary §1's basic inequality and
pure/compound Function direction were captured. No whole-document audit is
claimed for that large boundary document.

Accepted decisions remain fixed: candidate RecGroup is not intended Yulang
authority; F5 is comparison material; general concrete-resolution successes
cannot be composed as a preorder. Every preorder below is a deliberately
supplied mathematical candidate. None is inferred from concrete solver
success. No approval bundle, Oracle behavior, or new source meaning is used.

## Claim classes

1. **Countermodels to weaker candidate premises:** separate positive/negative
   values for one row, and an additional caller lower bound on its hidden
   witness, can invalidate the proposed projection. These models satisfy the
   complete total Function variance law and greatestness of Top. They do not
   refute the exact same-carrier, no-hidden-obligation premise.
2. **Conditional characterization:** shared targets, arbitrary caller
   inventories, and transitive replay alone cannot invalidate the projection
   when each row denotes one carrier value, caller constraints remain
   explicit, and replay adds only entailed inequalities.
3. **Reduced unproved condition:** the actual live-row transition/observation
   semantics must admit precisely that contextual interpretation, including
   cyclic replay and diagnostic policy. This remains open.

No established source-denotation, solver-completeness, acceptance, independent
review, or production-authority result is claimed.

## A nontrivial carrier satisfying the full Function law

Let `S={L,R}*` contain finite words, including the empty word `ε`. Put

```text
D = P(S),        A ≤ B iff A ⊆ B,
Bottom = ∅,      Top = S,
LX = {Lw | w∈X},    RX = {Rw | w∈X},
Fun(A,T) = {ε} ∪ L(S\A) ∪ RT.
```

This constructor is total on all pairs of subsets. Its three regions have
disjoint first-letter shapes. Thus

```text
Fun(A,T) ⊆ Fun(A',T')
iff S\A ⊆ S\A' and T ⊆ T'
iff A' ⊆ A and T ⊆ T'.
```

The order is reflexive/transitive and Top is greatest. In particular

```text
F(T) = {ε} ∪ RT,
F²(T) = {ε,R} ∪ RRT.
```

If `F²(ρ)⊆ρ`, then `ε,R∈ρ`; repeated application of `RRρ⊆ρ`
forces every `R^n` into `ρ`. Consequently every `R^n` also belongs to
`F²(ρ)`. Conversely `Q={R^n | n≥0}` satisfies `F²(Q)=Q`. Therefore,
in this candidate carrier, the exact projection has the particularly useful
characterization

```text
P(U) iff Q ⊆ U.
```

This is a hand-derived carrier fact used to falsify shortcuts, not a proposed
Yulang type denotation. It uses an infinite set carrier with a regular witness;
no finite-domain enumeration is implied.

## Small witness: interpreting the two row polarities independently

Consider the weaker interval interpretation with a positive row value `p`,
a negative row value `n`, and only `p≤n` connecting them. Translating just
the initial three tasks under this interpretation gives

```text
F²(p) ≤ n,       p ≤ Top,       F²(p) ≤ U.
```

Choose

```text
p=∅,       n=Top,       U₀={ε,R}.
```

All three clauses and `p≤n` hold. The exact one-value formula `P(U₀)`
fails because `RR∈Q` but `RR∉U₀`. This is one recursive row, one target,
and the least target by inclusion in this carrier admitting the relaxed
initial predicate: `F²(p)` contains `{ε,R}` for every p. No additional
caller constraint, second incoming use, nontransitive relation, or fixed-point
equality is needed.

The arbitrary-ground-target caveat can be narrowed. The negative pure shape

```text
N₀(Bottom+, N₀(Bottom+, Bottom−))
```

can be assigned the candidate carrier value

```text
V = Fun(Bottom,Fun(Bottom,Bottom))
  = {ε} ∪ LS ∪ {R} ∪ RLS.
```

It contains `F²(p)={ε,R}` but excludes `RR`, so the same separation holds
with this polarity-correct finite negative syntax. This statement assigns
its Bottom endpoints the candidate Bottom; it does not establish production
or source denotation for that syntax.

The production reduction's task law decomposes the comparison with this
negative shape into two terminal Bottom/Top argument tasks and `ρ+ <: Bottom−`.
The latter installs an upper on the recursive row. The row already contains
the Function lower `Lρ=F²(ρ+)`; actual replay then schedules
`Lρ <: Bottom−`, a Function/Bottom mismatch. The narrowly read
`apply_value_task` row/atom branch replays every stored exact lower against
the inserted upper, and its atom/row branch does the converse. Hence the
interval valuation above satisfies an incomplete initial-task interpretation
while failing the replay obligation `F²(p)≤Bottom`.

This directly discriminates two premises: `p≤n` is insufficient; either
one shared row value or a stronger interpretation proving all recursive
lower/upper coherence is required. It does not show a production bug. The
actual replay exposes precisely the information the relaxed interpretation
omits. Requiring pairwise inventory coherence alone is also not asserted to
construct a single carrier valuation for arbitrary cyclic, non-lattice domains.

## One additional caller bound can destroy projection

In the same carrier, `P(Q)` holds with `ρ=Q`. Add exactly one hidden lower
bound from a caller anchor:

```text
{L} ≤ ρ.
```

No witness survives the three-clause relation with target `U=Q`: `L∈ρ`
implies `RRL∈F²(ρ)`, but `RRL∉Q`. Thus

```text
P(Q) = true,
∃ρ. F²(ρ)≤ρ ∧ F²(ρ)≤Q ∧ {L}≤ρ = false.
```

This witness is minimized by added obligations: zero extra clauses is the
exact relation; one nonempty singleton lower suffices. It targets loss of a
caller-to-local dependency, not transitive replay itself. The target Q is an
abstract carrier value, not shown realizable by a production negative term.

The named production scheme has no free anchor and initially allocates a
fresh recursive row. The reduction reports no direct `ρ→c` row edge.
No read here establishes that the actual incoming route emits `{L}≤ρ`
or any equivalent caller lower. This is therefore a failure condition for
extending the theorem to coupled witnesses, not an attack on the exact audited
initial graph. A bridge must prove such extra coupling absent, entailed, or
retained explicitly; fresh identity allocation alone proves none of those
semantic facts.

## Shared targets and transitive replay: exact reduced premise

Let `σ` assign all existing caller variables, let `E(σ)` include their complete
lower/upper/edge inventory, and let incoming occurrences have distinct fresh
rows `ρ_i`. Multiple occurrences may share the same target row c. With
`U_i(σ)` denoting each target's assigned carrier value, the required valuation
set before hiding fresh rows is exactly

```text
E(σ) ∧ ∧i [F²(ρ_i)≤ρ_i ∧ F²(ρ_i)≤U_i(σ)].
```

The target's positive and negative handles must refer to the same assigned
value, or have an independently proved interpretation with this exact
projection. E must contain every caller obligation but cannot silently depend
on hidden `ρ_i`. Distinct `ρ_i` must range independently over the admitted
carrier. The conditional characterization then extends pointwise at each
fixed σ; existential hiding of independent rows distributes over this finite
conjunction. Shared target state alone introduces no counterexample. Checking
each use under a separately chosen caller valuation would be a different and
insufficient observation.

In this precise interpretation, a lower `ℓ≤c` and upper `c≤u` entail
`ℓ≤u`. An edge `c≤d` similarly transports lowers forward and uppers
backward. Full Function variance makes structural decomposition an equivalence.
These facts cover nonempty and transitively connected inventories at the
relation level. They do not establish that a live worklist realizes the
relation, terminates for admitted cyclic inputs, or reports its failure
correctly. Conversely, adding one unentailed coupling is exactly the failure
demonstrated above.

The remaining sufficient bridge condition is now local and contextual:

* For this exact scheme and any declared admissible caller state, successful
  bound restoration and predicate routing extend its valuations by precisely
  the displayed existential formula, with the row's polarity coherence fixed.
* Every extrusion, memo skip, structural decomposition, and bound replay
  preserves that valuation set. Extra fresh carriers must have a stated
  elimination law; row-level bookkeeping must not silently restrict witnesses.
* Completion has a specified observation: absence/presence of a relevant
  completed incompatibility diagnostic must correspond to the claimed
  satisfiability test. If that equivalence is not claimed, the bridge must
  remain a relation-only statement.
* Availability failure is a separate observation with a declared successful
  envelope. `Ok` is not diagnostic freedom; satisfiability is not a resource
  guarantee. Neither a mismatch nor later accounting failure can be hidden by
  the existential formula.

This is an exact reduced unproved condition, not a derivation of the source
rules. A transition checker supplied these assumptions would test consistency
of that checker, not establish them for source semantics.

## Independence, coverage, checks, and resources

The countermodel is mathematically constructed independently of the solver's
transition implementation. It shares the expressly assumed Function law and
Top with the member theorem; it changes the row interpretation or inserts a
named extra bound. Its independence does not make the changed premises source
rules. The narrow source read independently identifies the replay task that
the interval shortcut omits. No Oracle or executable checker was used.

Coverage: one carrier with all subset valuations characterized symbolically;
one recursive row; the least relaxed target; one polarity-correct negative
target; one singleton hidden lower; fixed caller valuations; independent fresh
rows with possibly shared targets; and conditional inventory entailment.
Mutations are the two named logical changes, analyzed by hand. No seeds,
ranges, executed mutations, probes, tests, builds, formatters, or Git commands
were used. No search was started, timed out, or left running.

Unverified scope: actual source/admitted-target denotation, arbitrary cyclic
inventory valuation construction, recursive memo/diagnostic completeness,
extrusion preservation, source contextual equivalence, final acceptance,
availability and publication guarantees, effects beyond the fixed pure leaves,
general SCCs, outer anchors, and runtime observations. The exact premise is
not refuted. Both mutations leave its source/live-row justification open; a
third equivalent toy probe would not reduce that blocker.

Commands: `cat` for the three rules; bounded `sed` reads of named governing
sections and both progress dependencies; `rg` to locate boundary §3;
`sed -n '12065,12345p' crates/yu-solver/src/lib.rs`; `sha256sum` for inputs;
and the final dependency/text integrity check recorded below. Initial combined
output captures were truncated; narrow reads supplied the used sections.

Budget: hand derivation and lightweight source/hash reads only, one output
path, no computation processes. At most four source-read shell commands ran
concurrently. No numerical CPU, RAM, or wall-time cap was supplied; CPU time,
peak RAM, and total wall time were not instrumented. No children were spawned.

Recommended next action: independently audit the contextual valuation
preservation condition for this exact cyclic row and negative target class,
starting with lower/upper replay and polarity coherence. Do not increase finite
tree comparison counts to stand in for that proof.

## Independent review

A read-only compiler-referee review found no blocking, major, or minor findings.
It checked the carrier's total Function variance law, the separate-polarity
witness and polarity-correct negative-target replay, the one-extra-lower
coupling witness, and the conditional distribution across independently fresh
rows at fixed caller assignments. The review confirms only countermodels to
weakened premises; the exact one-row premise, production realization, and
source semantics remain open.

## Frozen dependency snapshot

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  notes/design/2026-10-03-concrete-compatibility-boundary.md
fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e  notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md
f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779  notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

## Commit packet

* Exact leased path:
  `notes/progress/2026-10-06-rec-name-return-one-row-falsification.md`.
* Baseline SHA: `1e49e88f07fa8ceb0b05d109bab6c6a1f23d8d87`, supplied by primary.
  No Git command verified the object or compared files against it; the primary
  must revalidate the pinned dependencies before integration.
* Changed dependency hashes: none observed; the eight hashes above pin the
  actual read inputs and were rechecked at freeze.
* Claim/review status: independently reviewed research-only countermodels to
  weakened premises, conditional inventory characterization, and open
  contextual preservation condition. The exact one-row premise remains
  unrefuted.
* Checks already run: narrow source/authority reads, dependency hashes, and
  final read-only dependency stability/newline/whitespace/conflict-marker
  integrity check. No executable semantic verification.
* Proposed research-checkpoint commit message:
  `research: falsify weakened recursive one-row valuation premises`.
* Shared-record deltas intentionally left for primary/curator: record that
  positive/negative interval interpretation without recursive inventory
  coherence fails; one unrecorded caller lower can break projection; shared
  targets and entailed replay alone do not. Keep contextual row valuation,
  diagnostic correspondence, admitted-target realization, and availability
  scope open. No task/index/authority/theory/question file was edited.

Writing and review are complete for this bounded counterexample artifact;
any semantic expansion requires a new lease.
