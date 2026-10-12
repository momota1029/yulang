# Qualified intrusion: monomorphic counterexample search boundary

Status: frozen unreviewed research; bounded analytical characterization,
no source-qualified counterexample, theorem closure or implementation authority.
Baseline: `bf0420584b190654eca081257c9d7698361210f0`.
Branch: `research/simple-sub-intrusion`.
Lease: this file only; researcher leaf, no delegation or Git mutation.

## Objective and method

Seek a genuine source witness where one actual occurrence, qualified by its
origin/receiver Value SCC, loses an original typing upon equating its retained
polar parent/copy pairs. This lane uses original-rule inspection and one
monomorphic source discriminator. It does not repeat the earlier correlated
helper's two independent instantiations or the fixed odd/even bound calculation.

Governing sections: parent-copy decision's Selected operation, Value-reference
SCC clarification and Definition-root Value ownership; value-to-type
association's Approved extrusion-event qualification, Definition-root origin
for nested call-demand extrusion and Implementation/proof boundary; copied-row
ownership's Decision and Scope and proof boundary; top-level principles §§1–5;
Source Generalize §§2–3 and its construction §§3.3, 5.1–5.2.

Original implementation: `/home/momota1029/rust/simple-sub-reference`, revision
`9bae772624c23b52a93c1b226157e16898b4d9db`, `Typer.scala:48–83,88–188`.
Original paper: local `simple-sub-reference-paper.pdf`, §3.5, Fig.7 and Fig.8.
These independently supply native generation and polar approximation rules;
neither supplies a Value SCC intrusion transition or its Yulang source bridge.

## One distinct discriminator

Use original-reference AST constructors, rendered here as a term:

```text
let rec f = lambda x.
  let g = lambda y. {local = succ y, recurse = f y}
  in {left = g 0, right = f true}
in f
```

This is an admitted original Simple-sub term: Let/Lambda/App/Record/Var/Lit,
with original builtins `succ:int->int` and `true:bool`. Parser execution was
not performed. It is not a derivation of the complete Yulang Call/effect
meaning. Divergent evaluation does not invalidate its native static typing.

Definition-root references give `F->G` and `G->F`. The inner `f y` therefore
has approved occurrence endpoints `(G,F)`, independent of type bound storage.
Native levels put recursive placeholder o and outer formal A at 1, inner
formal B and recursive App result R at 2. Negative extrusion of
`o <: Function(B,R)` creates the actual pairs `(C,B,+,1),(D,R,-,1)`.
The local `succ y` contributes `B <: int`. Extrusion of B positively copies
its lower list, not this upper bound. The retained links are `B <: C`,
`D <: R`, and `o <: Function(C,D)`.

The attempted attack is to obtain `bool <: C`, so equality `C=B` would replay
against `B <: int` and fail. The second recursive demand does not produce
that constraint. `f true` produces `o <: Function(bool,W)` at level 1.
At recursive completion, the actual outer Lambda lower bound
`Function(A,T_rhs) <: o` replays both demands and produces

```text
C <: A       bool <: A       T_rhs <: D       T_rhs <: W.
```

There is no `A <: C`, so the Boolean lower bound of A is not a Boolean lower
bound of C. Function argument variance is decisive. Replacing the recursive
placeholder by its demand argument coordinate would fabricate a source rule.

This is a failed attack with a concrete satisfying separator. Define regular
algebraic types

```text
T = mu t. {left:{local:int,recurse:t}, right:t}
H = {local:int,recurse:T}.
```

The source checking assignment `f:Top->T`, `g:int->H` checks every source
call: `f y:T`, `succ y:int`, `g 0:H`, and `f true:T`. It reproduces the RHS
record T. For the generated coordinates choose `A=Top`, `o=Top->T`,
`B=C=int`, `D=R=T`, `W=T`; instantiate g's surviving result descriptions at
H and its argument at int. The remaining local `succ` result is int.
This satisfies the native directional links *and both proposed equalities*.
In particular `Top->T <: int->T` and `Top->T <: bool->T` use correct
contravariance. No assertion of a principal type or general equality
preservation follows from this one assignment.

The assignment is a semantic witness against this attempted contradiction,
not execution of an intrusive algorithm. It does not prove that every original
typing of the term survives. It shows exactly why this local primitive-conflict
attack cannot establish rejection: its missing `bool <: C` is not generated.

## Fixed odd/even and the remaining source obstruction

Preserve the user's fixed source:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Its approved root edges `O->E` and `E->O` qualify the inner call-demand
occurrence `(E,O)` and its *actual* retained pairs `(C,T,+),(D,R,-)`.
T is the type of `n-1`, not automatically the formal B. Reuse the existing
cross-level derivation: its integer reference extension is a conditional
source correspondence result. No operator, Branch, complete Call or effect
law is inferred here. Its native int/bool behavior is not a counterexample.

The already recorded correlated-helper rejection depends on independent
published helper uses being equated to one fixed low-level anchor. This pass
does not count that conditional result again. Original Simple-sub's Fig.7
explains why later instantiations can refine each parent independently within
the approximation; the approved SCC event selects equality but does not
establish the lawful source publication allocation for a concrete helper.

The precise missing source record is the actual publication p_g, validating
component K_g, Parameter/Desc telescope, recursive Internal dependency and
the scoped clause generated by the demand/extrusion/equality occurrence.
Source Generalize uses those records to determine fixed closure and whole
frame allocation. Value SCC membership does not itself register K_g; native
numeric levels cannot substitute for that registration. Without this bridge,
the old conditional helper witness cannot be promoted to a full Yulang
refutation, and an assumed freshening checker cannot settle the premise.
Stop here rather than adding another equivalent two-use model.

## Coverage, resources and dependencies

One analytical pass: one source term, one actual high-to-low recursive demand,
two retained polar pairs and a separate same-level Boolean recursive demand.
No random seeds, enumeration range, executed mutations or executable oracle.
The native rule inspection and semantic assignment share arrow variance,
primitive distinctions and recursive-type laws; they are not two independent
empirical oracles. Omitted: all-typing preservation, principal schemes,
alternative settlement schedules, repeated/memoized occurrences, other source
constructors, effects, full Call and authentic Yulang admission/registration.

Commands: bounded `cat`, `rg`, `sed`, PDF-to-stdout extraction, read-only
revision queries and SHA-256 snapshots. Zero Cargo, builds, tests, benchmarks,
child agents or compiler edits. No executable model was run. One lightweight
process per command; exact CPU/RSS and reasoning wall time were not measured;
the pass completed within the 45-minute allowance. Requested role: researcher;
role configuration does not pin model/effort. Actual tool response supplies no
effective model/effort metadata, so both remain unknown.

Direct dependency SHA-256 snapshots:

```text
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b parent-copy decision
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 value-to-type association
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd copied-row ownership
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 top-level principles
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 Source Generalize decision
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 Source Generalize construction
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 original Typer.scala
f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f original syntax.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 original paper PDF
ef308b68e967d916278b2d6e106731c723368f0477ecc947a12eb99c7f17a956 earlier correlated-helper search
5a4d89e1c22b553767a6e6789199ec7ef54cafd96216bd1c6b00147d1a1672ad cross-level odd/even derivation
```

Recommended next action: supply the construction-owned p_g/K_g/Desc/Internal
and scoped occurrence clause for the existing correlated helper, then apply
Source Generalize to decide its actual equality/frame allocation. Keep the
original parent theorem OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-13-intrusion-counterexample-search.md`.
- Baseline SHA: `bf0420584b190654eca081257c9d7698361210f0`; reference SHA above.
- Dependency changes: none by this worker; snapshots above use the pinned
  current baseline, including the integrated nested-origin clarification.
- Review status: frozen unreviewed bounded research; no independent review.
- Checks run: manual source constraint direction/assignment inspection,
  original revision and dependency hashes; zero production verification.
- Proposed checkpoint message: `research: bound monomorphic intrusion counterexample attack`.
- Shared-record deltas left to primary/curator: record the failed monomorphic
  argument-copy attack and its missing direction; retain p_g/K_g and scoped
  equality allocation as OPEN. No shared records changed. Writes stop here.
