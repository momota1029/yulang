# Contravariant annotation hygiene: minimized shortcut falsifiers

Date: 2026-10-10
Status: reviewed research checkpoint; conditional algebraic countermodels
Review: compiler-referee PASS, 2026-10-10
Method: static minimization; complementary falsification, not the main constructive proof
Source baseline: `32c65f07671b9de7b05ece3044a714c4d8d0e61b`
Lease: this new note only; source, tests and shared records are read-only

## Authority and claim boundary

The governing selected policy is
[annotation effect hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1: negative `[E]` permits function-local subtraction at the actual effect
position; positive `[E]` is an allowance; nested Function variance composes;
concrete identities are resolved. Omitting variables from concrete atom
collection preserves their connections and existing/future concrete checks.
§§2–5 supply the Oracle inspection, retained proof limits and construction
obligations. The withdrawn §6 callback result is not an oracle here.

The [concrete implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md)
requires actual contribution attachment for source subtraction and separates
annotation support from emitted contributions. Its implemented covariant
slice does not establish source contravariant subtraction. No parameterized
effect variance, handler-selection rule or new source meaning is selected here.

All witnesses below are conditional detached algebraic witnesses. None is an
actual source counterexample, compiler failure or independently reviewed
theorem. Their purpose is to reject stronger shortcuts once the stated
premises hold. They do not establish that source produces those premises.

## A. One attached removal cannot erase independent same-point support

Fix one semantic fiber `(nu,K,D)`, one active local annotation boundary `b`,
and one resolved nominal support point `p` (a nullary identity suffices).
Let `C` be a finite set of contribution identities, `point : C -> Points`,
and `R_b` the subset actually licensed and removed at this boundary. Assume:

1. `R_b` contains only genuinely attached, removable contributions at `b`.
2. The complete residual image is `C \ R_b`; this supplied image accounts for
   every independent surviving contribution relevant to the observation.
3. Public support is the set projection `S(X) = {point(q) | q in X}`.

The overstrong shortcut is the universal implication

```text
for all C,b,p:
  (exists q in R_b. point(q)=p) => p not in S(C \ R_b).
```

Smallest witness:

```text
C = {q0,q1}, q0 != q1
point(q0) = point(q1) = p
R_b = {q0}
C \ R_b = {q1}
S(C \ R_b) = {p}
S(C) \ {p} = {}
```

`q1` has independent origin/attachment evidence and survives. Removing `q0`
does not confer removal authority over `q1`. The shortcut disagrees even when
both contributions have the same resolved family *and* type point, so no
argument-variance premise is needed. Two identities and one support point are
minimal under these hypotheses: zero/one contribution cannot contain both a
removed contribution and a distinct survivor. Duplicate identities do not
create duplicate public support members.

This is the minimized witness already retained by the
[attachment playground](2026-10-05-effect-attachment-subtraction-playground.md),
not a new bounded search. That record enumerated 256 attachment/output pairs
and reported 12 sibling-survival histories; those historical checks were not
rerun here. Its consumption/reachability flags were supplied. The
[capture-profile derivation](2026-10-05-concrete-capture-profile-derivation.md),
“Conditional concrete-item corollary” and “Separate subtraction obligation”,
likewise establish eligibility only given profile/incidence/activity premises.
Eligibility alone supplies neither `R_b` nor complete residual-image adequacy.

## B. Concrete collection says nothing about an omitted variable's value

Separate concrete collection `collect` from symbolic denotation `eval_v`.
For a symbolic row coordinate `alpha`, assume

```text
collect(alpha) = {}
eval_v(alpha) = v(alpha)
```

The first equation classifies syntax into concrete atoms; the second uses a
valuation or future lower information. The false emptiness claim is

```text
for every alpha and v:
  collect(alpha)={} => eval_v(alpha)={}.
```

Smallest witness has one variable and one resolved concrete point:

```text
v(alpha) = {p}
collect(alpha) = {}
eval_v(alpha) = {p} != {}
```

No annotation concrete member or contribution identity is necessary for this
collection/denotation separation. With no symbolic coordinate or no concrete
point there is no nonempty omitted denotation. In a temporal presentation,
`L0(alpha)={}` and later `L1(alpha)={p}` separate “no lower known yet” from
“necessarily empty”. The transition is an explicit premise, not a source
reachability claim.

### Future-check exemption is a separate mutation

To falsify an exemption, a rejecting retained check must exist. Fix a predicate
`K_b` belonging to boundary `b`, with the concrete premise `K_b(p)=reject`.
Assume `alpha` remains connected to the checked boundary and concrete arrivals
through that connection must invoke `K_b`. Then compare:

```text
t0: collect(alpha)={}; L0(alpha)={}; retain connection and K_b
t1: one later concrete arrival p; L1(alpha)={p}
retained-check observation: K_b(p)=reject
exemption mutant: skip K_b because alpha was omitted at t0; accept
```

One variable, one concrete point, one rejecting predicate and one arrival
suffice. Without a rejecting case, accept/skip observations cannot discriminate
this mutant. Two time states are necessary to express a *later* lower.

The rejection premise is deliberately explicit. `collect(alpha)={}` alone
does **not** prove that a concrete `p` is forbidden by a source annotation.
A symbolic tail may have constraints relevant to its admission; this note
does not derive `K_b` from `[alpha]`, choose a closed-row interpretation, or
infer rejection of any particular source program. An accepting check still
must be retained, but acceptance alone would not expose the exemption.

For a subtraction view the same separation applies: omitting a variable from
grant collection neither deletes its lower contributions nor creates grants
for them. Which later contribution is removed additionally needs the genuine
attachment and boundary premises from A. A set filter that assumes those
premises cannot prove them. The selected policy permits local subtraction;
this note does not strengthen permission into universal mandatory consumption.

Integration §2 locates Oracle's variable-preserving lowering and future-lower
filters; §4 requires executable retained checks. This is recorded source
inspection evidence, not independently repeated inspection or Oracle execution
in this lane. Obtaining a particular source-generated rejecting `K_b` is the
precise remaining premise for a source counterexample to exemption.

## C. Nearest-port polarity loses enclosing Function variance

Use only the selected Function composition rule. Assign root sign `+`,
argument-value and argument-effect edges sign `-`, and result-value and
result-effect edges sign `+`. For a port path `w=(s1,...,sn)`, composed sign is
`pol(w)=root * s1 * ... * sn`. The shortcut uses only `sn`.

Two smallest discriminating structural paths are:

| Root | Outer Function edge | Inner Function effect edge | Composed | Nearest |
| --- | --- | --- | --- | --- |
| `+` | argument value `-` | argument effect `-` | `+` | `-` |
| `+` | argument value `-` | result effect `+` | `-` | `+` |

In each path the outer Function argument is itself a Function, and the inner
effect port contains a concrete `[E]` occurrence. For the first path, the
selected classification is positive allowance, while the shortcut assigns
negative subtraction permission. The second reverses the misclassification.
These are abstract Function-port trees, not parser fixtures or asserted
inferred schemes. `E` stands for one resolved nominal identity.

With the fixed positive root, a path containing only one Function edge has
`pol(w)=sn`; no nearest-edge disagreement exists. Two Function nodes and two
port edges therefore minimize structural depth. One concrete occurrence is
enough to distinguish the policy categories. A negative root could disagree
with one edge, but is outside this minimization's explicit positive-root
premise. Source lowering must retain the actual root sign and every ancestor
edge, including when it forms checking and exposed targets.

Integration §2 records Oracle's `lower_pos/lower_neg` reversal/retention rule;
the current concrete implementation gate reports nested Function checks.
Neither report alone turns this port-tree calculation into a source subtraction
test. No withdrawn callback output is used.

## Evidence, omissions and next action

There is no executable oracle in this artifact. All observations above are
direct evaluations of explicit set, predicate and sign premises. Their
agreement with retained artifacts is shared-assumption evidence. Historical
playground differential checks also share transition assumptions; they do not
independently validate source rules. The attacked mutations are support-wide
deletion, symbolic emptiness, later-check bypass and nearest-port sign choice.

Coverage is exactly the displayed finite witnesses. There are no seeds,
random ranges, enumeration, compiler runs, Cargo processes or measurements.
Handler ordering, activation, resumption, raw profile construction, attachment
formation, full Call meaning, equality transport, rollback and production
reachability are unverified. No source/test/manifests/lockfiles/questions or
shared task/theory/index files were changed. CPU, peak memory and elapsed
wall time were not measured; work used bounded static reading and one note
write, with no heavyweight process.

Recommended next action: obtain one source-construction artifact retaining the
exact annotation position, composed sign, symbolic connection and genuine
contribution attachment; use it to discharge the source-premise gap before
promoting any detached witness to a compiler regression obligation.

## Dependency snapshot and commit packet

All dependencies below matched the pinned source baseline when read; no changed
dependency hashes were observed. SHA-256 values identify the frozen inputs:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `4477be1344edb73e2873f94233d760c9a600bee6adbaaff3ec812a49c5219e7b` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/progress/2026-10-05-effect-attachment-subtraction-playground.md` | `7a831a5068d1fcc61a5ed350acce7b32822757c99e1ae778775ef80f0c52e0b6` |
| `notes/progress/2026-10-05-concrete-capture-profile-derivation.md` | `a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79` |
| `notes/progress/2026-10-05-handler-protection-filter-derivation.md` | `82402427727102e9afdf3065da4f6b6e2e836b4571b1355ece088dbda36f1cc1` |

The protection-filter input is retained context only: its witness-local `'e?`
operation is separate from `[E]`; no release premise is used in A–C.

Exact leased path: `notes/progress/2026-10-10-contravariant-effect-falsifiers.md`.
Baseline SHA: `32c65f07671b9de7b05ece3044a714c4d8d0e61b`.
Review: independent compiler-referee PASS on minimized premises, witnesses,
polarity composition and claim boundaries; research-only.
Checks before freeze: baseline dependency path comparison and SHA-256 snapshot.
Post-freeze check/result is returned in the handoff; no edits follow that check.
Proposed commit message: `research: minimize contravariant annotation hygiene shortcut falsifiers`.
Shared-record deltas left for the primary/curator: link this conditional
falsification note, retain the source attachment/check construction gate as
open, and record no theorem, runtime or source-reachability status promotion.
