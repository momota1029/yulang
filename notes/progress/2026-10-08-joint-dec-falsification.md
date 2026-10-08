# JOINT-DEC: exact pair decisions do not amalgamate original witnesses

Date: 2026-10-08
Baseline: `87467e190cff6a8c208d07c1b1f0a1769e81389e`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research checkpoint; frozen on submission
Claim class: bounded characterization and conditional counterexample derivation
Implementation/semantic authority: none
Exclusive lease: `notes/progress/2026-10-08-joint-dec-falsification.md`
Independent review: pending; producer checks are not independent review

## Objective, authority and method

Attack only JOINT-DEC's candidate effective residual decision route. The
specific mutation replaces one original shared witness by independently
chosen witnesses for each primitive pair. The experiment exhaustively checks
all unary predicate tables on at most three witnesses and three predicates.
It finds a minimal failure even when every pair decision is exact. This is
stronger local checking than the familiar separate singleton-marginal test.

The governing gate is successor-proof-obligations **JOINT-DEC**, at baseline
lines 874–883: construct effective candidates/quotient with preservation and
reflection for every actual active primitive and *simultaneous original-witness
completeness*, or an exact effective residual decision route. This note tests
a weaker candidate shortcut; it does not refute that stated sufficient route.

Exact governing sections and dependencies:

- SCC intrusion redesign charter §§1–2: preserve meaningful joint constraints;
  final well-typed acceptance is the compatibility target, and F5 internal
  presentation is not the successor meaning.
- Open residual factorization §§2–4: `C = Eq ∧ B ∧ Perm ∧ Guard ∧ Phi`, one
  shared `eta_hat_Q`, original guard outcomes, and exact constrained
  factorization. Finite residual presentation does not claim decidability.
- Source-context finite closure §§2–3, especially premise 6: multi-parent rules
  use one shared assignment. Finite context closure does not establish that
  semantic premise or effective residual satisfiability.
- Pure structural effective-decision corollary, **Claim and input boundary**,
  **Proof of the decision claim**, and **Boundary**: the reviewed pure `8^N`
  bound excludes joint `Guard/Phi/K,D`, effects and source admission.
- Effective projection round 2 §4 and round-2 review **Result and exact gate
  accounting**, item 3: the established Record-chain halting extension already
  refutes the general implication from pure FMP, finite syntax and individual
  candidate decidability to a computable joint bound. That attack is reused as
  a boundary result, not rerun or reproved here.
- `rules/design-authority.md`: **Authority order**, **Natural compiler behavior
  and proof-obligation economy**, **Approval and implementation gate**;
  `rules/research-lab.md`: **One semantic baseline**, **Evidence quality and
  stopping unproductive loops**, **Commit conveyor**;
  `rules/git-concurrency.md`: **Disjoint-file mode**, **Integration ownership**.

The laboratory seed and current task's **Open gates at this snapshot** agree
that finite contexts do not prove finite worlds or effective joint solving.
No pending question bundle was consumed. All source interpretations, original
quantifier positions and accepted ordinary language behavior remain inputs.

## Candidate assumptions and minimized witness

Fix a nonempty concrete witness set `W`, a singleton context carrier `J={j}`,
and unary primitives `P_0,...,P_(m-1)` on the *same* original witness. There
are no names, worlds, effects or transition rules in this model. Candidate
membership is supplied by explicit finite tables, hence decidable.

For a nonempty index set `S`, define the exact local decision

```text
E(S) = exists w in W. conjunction_(i in S) P_i(w).
```

The mutation is

```text
PairAccept = conjunction_(1 <= |S| <= 2) E(S).
JointAccept = exists w in W. conjunction_(0 <= i < m) P_i(w).
```

Every local `E(S)` is genuinely exact, including both predicates sharing one
witness inside each pair. PairAccept silently chooses that witness again at
the next pair; it has no common-family lifting certificate.

The smallest failure has three witnesses and three predicates:

| Original witness | `P_0` | `P_1` | `P_2` |
|---|---|---|---|
| `a` | true | true | false |
| `b` | true | false | true |
| `c` | false | true | true |

Each singleton and pair is satisfiable. The pair witnesses are respectively
`a` for `{0,1}`, `b` for `{0,2}`, and `c` for `{1,2}`. No witness satisfies
the triple, so PairAccept is true and JointAccept is false. Deleting any
predicate removes the mismatch.

Minimality is not inferred merely from an enumeration cutoff. For at most two
predicates, the checked pairs include the whole conjunction. For one witness,
singleton truth already supplies the common witness. For two witnesses, if a
nonempty pairwise-intersecting family has empty total intersection, some set
excludes the first witness and some set excludes the second. Nonemptiness
forces these sets to be the two opposite singletons, contradicting pairwise
intersection. Thus no smaller witness domain works, even with arbitrarily
many predicates. The three-by-three table attains both minima.

## Relation to the pure structural fiber and finite quotients

This table can be embedded in a *mathematical extension* of the existing pure
mandatory Record grammar. Let `C_n=Record{f:...Record{}...}` have `n` nested
`f` fields, and take the pure clause `B(X) := X <= Record{}`. Use

```text
P_0(X) := X = C_0 or X = C_1
P_1(X) := X = C_0 or X = C_2
P_2(X) := X = C_1 or X = C_2.
```

Equality is equality of regular-tree unfoldings. Each predicate is decidable
on a supplied finite regular graph and has empty nominal support. All three
listed chains satisfy `B`; all other assignments fail every predicate.
The pure package still has its tiny empty-Record witness and its established
FMP result. No actual Yulang primitive is claimed to have these definitions.

For the deliberately coarse quotient `q(a)=q(b)=q(c)=star`, each singleton
existential image and each pair existential image at `star` is exact and
true. Their conjunction has no lifting to an original witness. Consequently
exact local image decisions do not imply exact image of conjunction:

```text
image_q(P_0 intersect P_1 intersect P_2)
  != image_q(P_0 intersect P_1)
     intersect image_q(P_0 intersect P_2)
     intersect image_q(P_1 intersect P_2).
```

The left side is empty; the right side is `{star}`. This quotient does *not*
satisfy pointwise truth preservation/reflection for each original primitive:
the three witnesses have different predicate vectors. It therefore cannot
be a counterexample to a quotient that already has those stronger laws and
supplies a coherent lift. Retaining the full vectors or directly checking the
original intersection decides this finite example exactly.

More generally, for any fixed `k >= 1`, take `k+1` witnesses and `k+1`
predicates with `P_i = W minus {w_i}`. Every set of at most `k` predicates has
a common witness; the full conjunction has none. This conditional family
shows that replacing simultaneous completeness by any fixed checking arity
requires an additional proved intersection/amalgamation property. It is not
a lower bound against algorithms that retain correlations or inspect every
active conjunction.

## Exact result class and residual blocker

The bounded experiment and the derivation reject **local decision plus
pairwise compatibility implies joint decision**. They do not establish
unbounded noncomputability. Indeed this example has a computable finite joint
domain and an immediate complete decision procedure. The no-computable-bound
statement is the separately reviewed halting-extension result cited above;
the present table must not be substituted for its proof.

The actual unproved premise remains a source-justified law that a chosen
regularization, residual calculus or primitive decision procedure preserves
and reflects the *whole* original witness fiber under conjunction and the
original quantifiers. Arbitrary decidable predicate images cannot supply that
law. This note closes no Yulang gate, adopts no primitive, and supplies no
admitted source counterexample. No further equivalent toy probe is recommended.

## Experiment, independence, coverage and resources

One standard-library Python process enumerated all ordered unary predicate
tables for `1 <= |W| <= 3` and `1 <= m <= 3`: 682 profiles total, no random
seed. The oracle enumerates one witness satisfying all predicates; the
mutation enumerates each singleton/pair independently. Both share only the
supplied finite predicate table, Boolean semantics and the explicit witness
domain. The distinct quantifier order discriminates the shortcut. Neither
implements source transition rules or validates source semantics. This is
not independent mathematical review or independent Yulang oracle evidence.

Reproduction of the enumeration core of the executed `python3 - <<'PY'`
command (stdin only, no checker/cache/output files):

```python
import itertools, resource
resource.setrlimit(resource.RLIMIT_AS, (128*1024*1024, 128*1024*1024))
resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
checked = 0
failures = []
for n in range(1, 4):
    for m in range(1, 4):
        mismatches = []
        for profile in itertools.product(range(1 << n), repeat=m):
            checked += 1
            oracle = any(all(mask & (1 << w) for mask in profile)
                         for w in range(n))
            pairwise = all(
                any(all(profile[i] & (1 << w) for i in subset)
                    for w in range(n))
                for size in range(1, min(2, m) + 1)
                for subset in itertools.combinations(range(m), size))
            if oracle != pairwise:
                mismatches.append(profile)
        print(n, m, (1 << n)**m, len(mismatches))
        if mismatches:
            failures.append((n, m, mismatches))
assert checked == 682
assert len(failures) == 1
n, m, profiles = failures[0]
assert (n, m, len(profiles)) == (3, 3, 6)
assert sorted(profiles) == sorted(itertools.permutations((3, 5, 6)))
```

The process exited 0. All domains except `(3,3)` had zero mismatches; `(3,3)`
had exactly six, the permutations of bitmask supports `(3,5,6)`. Masks encode
the table's three witnesses as bits 0–2. Searches above these ranges were not
run; the general `k` family and minimality argument are written derivations.
No source program, structural regularization algorithm, binder alternation,
world/admission history, effects, recursive resolution or compiler path was
executed. No Cargo build/test, formatter, child, Git mutation or performance
sampling was run.

Conservative calculation limits: one lightweight process, 10 CPU seconds,
128 MiB address space, 30 seconds wall allowance, stdout only. Measured
elapsed experiment-plus-dependency-check time: 0.022936 seconds; Python
user/system CPU: 0.018205/0.009103 seconds; maximum Python RSS: 16,480 KiB.
RSS/CPU of the short sequential `git show` dependency readers are not included
in Python's self accounting; aggregate peak and all command/session overhead
were not measured. No timeout, kill or partial shard occurred.

The run also byte-compared every dependency below against
`git show 87467e190cff6a8c208d07c1b1f0a1769e81389e:<path>` and computed SHA-256.
Before submission these dependencies are rechecked; changed dependency hashes
must be reported rather than silently accepted.

| Dependency | SHA-256 |
|---|---|
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | `dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf` |
| `notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md` | `37bc762c22d32258355e835a29f598a8b50aa7307a88c01454ef63849c11e133` |
| `notes/progress/2026-10-07-successor-effective-projection-round2.md` | `214e6a688b84b6ad11adf8446cc0c39cc61f292b8bfd221d2e66749046bc0e89` |
| `notes/progress/2026-10-07-successor-round2-review.md` | `97367f04b7fa6fd1f21adcc4609129a7d888f9dea6471acf0a06664daadf79bc` |
| `notes/theory/successor-proof-obligations.md` | `59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc` |

## Recommended next action and commit packet

Recommended next action: the primary should require one actual active
primitive's preservation/reflection law through the proposed pure
regularization or a complete original-fiber residual decision law, retaining
all active predicates together; do not promote pairwise compatibility into
simultaneous completeness.

- Exact leased/changed path:
  `notes/progress/2026-10-08-joint-dec-falsification.md`.
- Baseline SHA: `87467e190cff6a8c208d07c1b1f0a1769e81389e`.
- Dependency hash changes: none at construction; rechecked on submission.
- Review status: unreviewed research-only checkpoint; frozen on submission;
  zero independent review, semantic adoption or gate closure claimed.
- Checks already run: pinned HEAD/status inspection, dependency byte/hash
  comparisons, one 682-profile exhaustive finite experiment, narrow final
  lease/dependency inspection. No production tests/builds.
- Proposed one-line commit message:
  `research: falsify pairwise JOINT-DEC witness amalgamation`.
- Shared-record deltas intentionally left for the primary/curator: optionally
  link this bounded shortcut falsifier from JOINT-DEC/current progress after
  adjudication; retain OPEN-PROOF and all existing dependencies. No task,
  index, authority, theory map or question bundle was modified.
