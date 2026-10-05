# Function admission projections: finite correlation falsifier

Date: 2026-10-06
Status: frozen, unreviewed research checkpoint; bounded characterization and conditional derivation
Baseline: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`
Branch observed: `research/simple-sub-intrusion`
Scope: information lost by replacing whole Function challenges/observations with independently projected coordinates, shallow argument results, or typed-port displays
Authority: research only; no production semantics, compiler change, or gate closure

## Objective and exact dependencies

Test whether such summaries can certify both `D_C subseteq D_A` and, for each
checked-admitted challenge, `P_A(h) subseteq P_C(h)`, for the identity callable
whose Value entry receives the whole argument carrier. This lane attacks
projection loss, not endpoint generation or source adequacy.

All semantic inputs were read from committed blobs at the pinned baseline:

| Input | Blob | Governing section |
| --- | --- | --- |
| Approved inlet-domain answer | `e3c0dada3036e23c2929c5af9775e7490998a210` | Decisions 1–5: every independently typed compatible punctured context; callable and whole argument carrier; comparison-independent admission |
| Approved denotation basis | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` | Decisions 1–5: original `Rel_C` fiber and independent endpoint/role/path/origin/continuation/scope/authority/dependency restrictions |
| Approved membership policy | `fb4a169a2d748422490cc74c026338587290e90c` | Decisions 1–4: Option 2 permits conservative extras without mandatory source-constructor witnesses |
| Typed computation core | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` | §6 structural application/parameter rules; §9 entry, pending suffix, directions and joint containment law |
| Source contracts | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` | §§2.2, 3.3, 3.7, 10: active joint predicates, history-dependent providers, positive abstraction and open production obligations |
| Theorem C package | `ab212217cd404991cded2b8fd529a1e731a806b3` | §§2.4–2.6, 3–4: whole logical hiding, linked lift, query-independent response/future-use rules and conditional theorem |
| Coupled interface core | `841325b72ab797729b9f26d4569007ec6694c99b` | Candidate Function contract: two punctured holes, all contexts and open exact typing judgment |
| Prior inlet audit | `b87fb96ded029deaa6efdc419e323a4c31191bb9` | Conditional source-call derivation; production admission/satisfaction gap |

The design index was used only as a locator. Read operating rules:
`research-lab.md`, `design-authority.md`, `git-concurrency.md`,
`orchestration-budget.md`, and `testing.md`. No uncommitted semantic replacement
was used. The typed-core and source-contract constructions remain candidates
with the scopes recorded in their source documents; the approved answers do
not upgrade their missing production predicates into established rules.

## Source-facing reduction and its limit

In the supplied typed-core derivation, `id x = x` has Value entry and a pure
body result. At `A=Int`, `Return(0)` has no entry request. A designated
computation `Request(q,k)` that resumes to `Return(0)` gives the same eventual
Int, but entry exposes `q` and bind retains the rebind/body/return suffix.
Consequently eventual forced-result equality cannot justify equality of the
complete invocation observations. This follows conditionally from §9's
displayed entry and bind equations; it is not a new production evaluation rule.

At `A=L`, where `L` is a latent-provider value interface, entry can similarly
expose `q` and later return an `L` value. Identity returns that value without
recursively forcing it. Its legal future uses keep the original returned
descriptor, history and authority. The `A=Int` and `A=L` cases are distinct
instantiations, not a claim that their instantiated typed ports agree.
The common polymorphic identity/body display by itself says nothing about
the input carrier's complete request/return/future-use history.

Theorem C §3 explicitly requires a response at an exposed request and a
future use at an actually returned provider. Thus those links are material
in its source-generated reference domain. The approved production basis also
retains such evidence. Neither source supplies the exhaustive production
`Admit_F` and `Sat_F` clauses needed to instantiate the finite tables below
as a Yulang counterexample. No exact production pretty-printer is modeled.

## Minimized finite witness

Supply the finite envelope `U={0,1} x {0,1}` of complete packets. The two
coordinates are abstract references in a linked history, such as a request/
resumption reference and a returned provider/future-use reference. They are
not literal Int values, which the observation projection may erase.
All four packets have the same supplied endpoint types, role and fixed
ambient fiber. All other predicates are fixed. That envelope is an explicit
model assumption, not an established enumeration of `Rel_C`.

Let `m(S)=(pi_1(S),pi_2(S))` and supply:

```text
R = {(0,0)}
S = {(0,0),(1,1)}
T = {(0,0),(0,1),(1,0)}
m(S) = m(T) = ({0,1},{0,1})
R subseteq S; R subseteq T
(1,1) in S but (1,1) not in T.
```

This preserves a common nonempty base, so failure is not caused by erasing
all base behavior. On the supplied envelope these can be expressed as the
positive-grammar *algebra* of source-contract §3.7, with hard envelope `G=U`,
no rewrite edges, base `R`, and independently supplied extras
`Z_S={(1,1)}` and `Z_T={(0,1),(1,0)}`. This verifies extensivity in the finite
algebra only. It does not certify either extra as a production primitive.
The paired-grammar theorem does not apply: these `Z` relations differ.

Two separate uses isolate the two obligations:

1. **Admission experiment:** supply `D_C=S`, `D_A=T`. The coordinate test
   reports inclusion/equality, while complete domain inclusion fails at
   `(1,1)`. These are predicates on whole challenges supplied before any
   comparison; this does not generate challenges from output-contract success.
2. **Observation experiment:** supply one common admitted challenge `h`,
   `P_A(h)=S`, `P_C(h)=T`. Complete observation inclusion fails at `(1,1)`,
   although coordinate marginals agree. Here coordinates vary in the supplied
   conservative output relation at fixed `h`; they are not independently
   reselected challenge inputs.

These experiments use the same finite set algebra, not two independent
source validations. They show that a summary can miss each obligation
separately. They do not claim the same production endpoint pair fails both.

Without the common-base requirement the smallest equal-marginal collision
is `S={(0,0),(1,1)}`, `T={(0,1),(1,0)}`: four tuple entries. A singleton
relation is determined by its unary marginals, so no nonempty pair with
fewer than four entries has equal marginals and unequal relations. With a
common tuple, two size-two relations cannot form the diagonal/antidiagonal
collision; the displayed size-two/size-three witness attains five entries.
For marginal *inclusion* alone, three entries suffice:
`{(0,0)}` versus `{(0,1),(1,0)}`. These minima hold in the supplied 2x2 model.

## Conditional information-loss theorem

For relations on a fixed envelope, suppose a comparison procedure sees only
`m(left),m(right)` and certifies equality/inclusion when those summaries are
equal, as it does on the reflexive pair `(S,S)`. It receives identical input
on `(S,T)`. It therefore certifies a false inclusion for the witness above.
This is an information-loss derivation, conditional on that acceptance rule
and on the envelope admitting the relations. A sound incomplete procedure
may instead refuse certification, or use additional joint evidence.

A sufficient positive repair is a separately proved saturation property:
if every candidate member lies in the same envelope `U` and
`right = U intersect (pi_1(right) x pi_2(right))`, projected inclusion implies
complete inclusion. Every left tuple then has both permitted coordinates
and hence belongs to right. No cited production source establishes this
property for Function challenges or complete observations. A compact summary
may also retain a reference to a joint predicate/certificate; compactness
itself is not refuted. Independent coordinate projection without that
certificate is the shortcut falsified here.

## Executable method, oracle independence and coverage

Checker: `tools/research_function_admission_projection_20261006.py`.
The reference tests membership of complete supplied tuples. The candidate
compares coordinate projections. A third control encodes complete relations
as four-bit masks and checks exact inclusion. The reference never calls the
candidate summary. They nevertheless share the supplied universe and relation
tables. There is no independent source-semantics oracle, and no transition
rules are claimed or inferred. This checker proves finite information loss
for those predicates, not the predicates' source validity.

Enumeration: all 16 subsets of the explicit four-packet domain and all 256
ordered relation pairs, including empty relations. No seeds, randomized
search, unsearched shard or larger-domain claim. Results:

- 56 false positives from coordinate inclusion;
- 32 of those have identical marginals;
- 30 have identical marginals and a common nonempty base;
- exact packet-bitset control agrees on all 256 pairs;
- minimal total entries: 3 for projected inclusion, 4 for equal marginals,
  5 for equal marginals plus common nonempty base.

Named mutations are independent witness recombination (Cartesian closure),
discarding history while retaining exact returned-provider IDs, and replacing
the packet by its constant supplied typed-port signature. The witness defeats
all of them. Cartesian closure adds `(0,1)` and `(1,0)` to `S`.
No mutation models a compiler implementation.

Exact command, run twice (second run after strengthening the shallow-value
mutation from value kind to exact provider ID):

```text
/usr/bin/time -f 'wall=%e cpu_user=%U cpu_system=%S max_rss_kib=%M exit=%x' timeout 5s python3 -B tools/research_function_admission_projection_20261006.py
```

Both runs exit 0 and complete the range. Each reports 0.02 s wall, 0.01 s
user CPU, 0.00 s system CPU; peak RSS 11,040 KiB then 11,200 KiB. One Python
calculation process per run, no workers/builds; timeout/time are supervisors.
No logs or bytecode files written. The assigned 5 s / 256 MiB calculation
budget was met. Overall interactive/tool overhead was not separately timed;
the assigned 15-minute work window was not used for an unbounded search.

## Failure conditions, omissions and next action

If actual production predicates exclude one of these packets, require a
joint invariant stronger than the supplied `G`, or identify the references
under the actual observation projection, the witness is not a production
counterexample. If a candidate summary retains the original joint relation
or a proved saturation certificate, this projection attack does not apply.
The fixed original `(nu,K,D)` is never recomputed in the model; realization
of both tables at a real fixed fiber remains unverified.

Not searched: production endpoint membership/admission, `EnvStore/JointWF`,
raw-source realization of `U`, source-constructor coverage, typed continuation
scope, actual authority expiry, higher-order recurrence, handlers, mutable
state, adapters, all original-fiber solutions, principality or compiler
acceptance. No compiler tests/builds or production edits were authorized or
run. There is no claim of `P_actual=P_ref`, mandatory source witnesses, or
independent review of this artifact.

Recommended next action: require a proposed production summary to name its
retained joint predicate/certificate and independently establish its transport
at fixed `(nu,K,D)`; if it only exports marginals, prove a saturation property
or reject certification when correlation is unknown. Increasing this toy
domain cannot establish the missing production predicates.

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-function-admission-projection-falsifier.md`; `tools/research_function_admission_projection_20261006.py`.
- Baseline SHA: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`.
- Changed dependency hashes: none; committed pins above remain the read dependencies.
- Review status: frozen unreviewed research; no independent certification or production claim.
- Checks already run: exhaustive deterministic checker twice, final run after the only checker repair; scoped output-path inspection and pinned-source inspection. No compiler tests or broad checks.
- Proposed commit message: `research: record finite Function admission projection falsifier`.
- Shared deltas left to primary/curator: record a bounded projection-loss witness and the common-base qualification in `tasks/research-lab.md` or the primary queue; optionally link this note from the relevant theory/status record. Keep the production admission/denotation gate open. No shared task, index, authority or question files were written.

Writing stopped at this packet; review and integration belong to the primary.
