# Restricted incoming-use reconstruction

Status: independently reviewed conditional derivation and exhaustive bounded
evidence; non-authoritative research result. No production or DAG closure.
Source baseline: `45fb91e069120f05741a0a4d488e80b38ca59ceb`.
Checkpoint base: `62518f6f4e5961a857290f3ae36a00d6eb271e95`.
Producer: closed_q_use_reconstruction research worker. Independent review:
compiler-referee accepted within the declared scope with no findings.
Owned outputs: this note and
`tools/research_candidate_own_row_closed_q_use_reconstruction.py`.

## Objective, authority and method

Extend the reviewed assignment-to-closed-artifact result through the current
incoming consumer for the acyclic pure Function forwarding fragment. The
reference is original direct inequalities and an unexpanded Function challenge;
F5 output is never the semantic oracle. Method: source-local inspection,
conditional constructive reconstruction, and one finite exhaustive campaign.

Governing authority is `notes/design/2026-10-04-inference-research-playgrounds.md`
Direction/Boundaries. Target constraints are obligations 1–5 of
`notes/progress/2026-10-05-scc-generalized-boundary-contract.md`; that contract
is source-grounded with open obligations, not a selected successor carrier.
Dependencies are the reviewed own-row acyclic note/checker and the shadow
parameter candidate progress note. Foundation §§7, 9, 22, 23 and 33 provide
current representation, comparison and identity constraints. Ordinary candidate
mode remains false, unconditional diagonal repair remains rejected, guarded
recursion remains unresolved, and no source meaning is reselected.

## Exact conditional claim

Let L be a bounded lattice. Rows r0,...,r(n-1), 1<=n<=3, occupy one of
`(a,a,a)`, `(a,a,c)`, `(a,c,c)`, `(a,b,c)`. The ordered rows form a chain.
The original predicate for use t is

```
O_t(rho_t,u_t,v_t) := rho_t(a)<=rho_t(b)<=rho_t(c)
                    and u_t<=rho_t(a) and rho_t(c)<=v_t.
```

The redundant direct `a<=c` is also checked by the reference. The challenge
`u<=argument and result<=v` is the supplied scalar interpretation of pure
Function comparison; it is not a value denotation or a source typing theorem.

Assume the successful reviewed all-local generalization path: candidate own-row
mode; one distinct fresh Function root; pure Function(a,c) is its only lower;
acyclic forwarding is the only payload constraint; no exact payload bounds,
extra roots, enclosing references, guarded reentries, recovery, stale memo;
all payloads eligible outside non-generic closure; normalization, finalization
and terminal finish succeed. The reviewed bridge yields

```
PureFun(Intersection(Q(r0)-,...,Q(r(n-1))-),
        Union(Q(r0)+,...,Q(r(n-1))+)), R=[]
```

Q mapping is injective and shared across polarities. Exact duplicate removal or
singleton normalization does not change the relation. Ordinal order is
irrelevant; the checker deliberately uses reversed row-to-Q numbering.

For each incoming use, current code allocates one fresh row for every Q. The
negative Intersection flattens to its members; positive Union similarly
flattens. The positive Function emits every Cartesian pair `(q_i-,q_j+)`.
All resulting Functions are routed to the same live use row. With that row
challenged by Function(u_t,v_t), exact lower/upper replay and §22 Function
decomposition produce

```
A_t(eta_t,u_t,v_t) := AND_(i,j)(u_t<=eta_t(q_i) and eta_t(q_j)<=v_t)
                    iff AND_i(u_t<=eta_t(q_i)<=v_t).
```

This is the candidate's actual emitted constraint shape interpreted in L, not
a direct-bound table presumed to survive export. No Q direct edges are restored.
It uses one owned row for every repeated binder and distinct maps for the two
uses. Actual ordinal allocation is fresh by construction, not an equality
merge or a variable occurrence proxy.

Source locators: `f5c_binder_substitution.rs:404–448` maps both polarities by
the same Q map; `lib.rs:14523,14650` looks up the same fresh map;
`:14543,14670` flattens aggregates; `:14578–14601` builds Cartesian Functions;
`:14795–14829` allocates Q rows; `:14900–14927` routes all predicate parts;
`:15284` clears per-use scratch after routing;
`:14409–14456` admits all members before publishing the representative route.
Foundation §22 supplies exact Function decomposition and direct lower/upper
replay. This source inspection was not independently reviewed in this lane.

## Reconstruction and arbitrary caller predicates

With no fixed payload coordinates, existential O_t and existential A_t both
hold exactly when u_t<=v_t. The forward direction follows from original
inequalities: every rho_t(ri) lies in the challenge interval, so setting
eta_t(Q(ri))=rho_t(ri) satisfies all emitted pairs. Conversely an artifact
witness implies u_t<=v_t; assign every source row u_t. This restores all direct
inequalities while preserving the observable challenge coordinates.

For one or two independently freshened uses, perform that reconstruction
separately. Their projected joint relation is exactly
`AND_t(u_t<=v_t)`. Internal artifact row assignments need not be restored
pointwise; they are existentially forgotten. The observable ports in this
claim are precisely `(u_1,v_1[,u_2,v_2])`. Caller constraints cannot inspect
hidden local Q valuations or original internal row endpoints.

For any predicate P on those observable tuples, relation equality gives
`exists local rows. O and P` iff `exists fresh rows. A and P`; conjunction and
projection preserve equality. Thus arbitrary finite tuple-table predicates,
including correlated constraints between uses, are covered mathematically.
The checker exhausts every singleton predicate by testing every tuple. Every
finite predicate is a union of those singletons; enumerating all 2^N tables
adds no distinguishing power. Additionally the checker tests five concrete
predicates for each positive configuration: True, u_1=v_last,
v_1<=u_last, (u_1,v_1)!=(u_last,v_last), and every fixed value <=v_1.

## Fixed coordinates: conditional extension and first actual mismatch

For a partial fixed map kappa shared by all uses, the mathematical candidate
relation requires every kappa(ri) to lie in each use's interval. The original
also requires fixed values to respect their chain order. Hence zero or one
fixed payload coordinate suffices for projected equality. Reconstruct by
scanning rows in order: carry the most recent fixed value, starting at u_t;
write that value into each unfixed row. For one fixed value k, each interval
contains k, so the resulting source chain is monotone and respects k. The
same k is used across both uses; locals are reconstructed independently.

This fixed extension is a model-only conditional theorem. It assumes both
sides already possess a correctly shared fixed-coordinate interpretation.
The all-local reviewed generalization hypotheses do not supply it.

The first current representation mismatch is exact: foundation §7 requires
every closed variable to be Q or R and forbids surviving live/source identity.
At `f5c_binder_substitution.rs:404–416` (positive) and `:438–450` (negative),
an unmapped retained Variable has only R, Q or polarity-elimination choices,
then returns IdentityExhausted. An external/non-generic payload cannot simply
be inserted as a Fixed node. Mapping it to ordinary Q instead makes
`lib.rs:14795–14829` allocate a new row for each incoming use, losing the
required fixed identity. No Fixed carrier has been invented in this checker.

The two-fixed negative discriminator is minimized: one atom, slots `(a,a,c)`,
kappa(a)={x}, kappa(c)=empty, challenge (empty,{x}). Every emitted scalar pair
holds because both values lie in the interval, but original a<=c fails.
No source completion exists. One identity, zero atoms, or fewer than two fixed
rows cannot produce this fixed-order obstruction by the derivation above.

## Campaign, mutations, resources and limits

Exact command, exit 0:

```
timeout --signal=KILL 10s python3 -B tools/research_candidate_own_row_closed_q_use_reconstruction.py
```

One lightweight Python process, no Cargo/build/compiler tests or formatting.
Internal deadline nine seconds; external hard kill ten seconds. No randomness
or seeds. Exhaustive domains are powersets of one/two atoms (bitmasks 0..1 /
0..3), four alias patterns, one/two uses, all zero/one/two fixed-coordinate
maps and values, every complete per-use row valuation, and every observable
challenge tuple. Fixed values are global while local identities carry use tags.

Results: 312 configurations; 4,954 valuation visits; 40,064 routed pair checks;
32,352 observable tuples (10,192 positive, 22,160 two-fixed discriminator
tuples); eight disjoint freshening checks; 560 explicit caller-predicate checks.
No timeout, incomplete enumeration or failure. Checkpoint-path script wall
0.017322 s, CPU 0.031398 s, peak RSS 11,360 KiB (Linux). The compiler-referee's
scratch-path rerun also exited 0 and reproduced all counts and witnesses. No
aggregate measurement campaign or timing claim.

Named mutation witnesses, analytically minimal within their dimensions:

- Split one repeated binder across polarities: one row, one atom, one use,
  challenge ({x},empty). Reference rejects; negative row {x} / positive row
  empty admits the mutant. This mutation has an explicit extremal witness,
  not an exhaustive split-identity search.
- Reuse a Q row between uses: one row, one atom, two uses with challenges
  (empty,empty) and ({x},{x}). Independent source/fresh uses succeed; one shared
  row cannot inhabit both singleton intervals and fails. This is an explicit
  exhaustive two-value row check, not an exhaustive cross-use mutation campaign.

Reference and candidate share the finite lattice/order, alias identity map,
Function challenge and selected fragment. Their constraint logic differs:
reference evaluates original inequalities and the unexpanded Function;
candidate evaluates freshened Cartesian emitted pairs. Passing results prove
neither shared row semantics nor source-language adequacy. They are bounded
evidence for the conditional derivation. Failure conditions are relation or
reconstruction assertions, missing mutation/discriminator witnesses, incorrect
freshening, or budget overrun.

Unverified: actual compiler execution, arbitrary accepted source contexts,
source identification of the scalar observable ports, lattice interpretation
adequacy, source-boundary generation obligations 1–3, fixed-coordinate export,
additional Function nodes/challenges, arbitrary graphs/cycles/R/effects,
whole-scheme source typing, public observations/diagnostics/evidence and
production conformance. No gate closed; independent review does not certify
semantic adequacy or production readiness.

## Independent review

The compiler-referee reviewed the exact scratch note and checker, then reran the
checker read-only. It accepted the conditional proof, the finite coverage and
the fixed-coordinate scope with no blocking, major or minor findings. The
review confirms that two-use factorization follows from independent fresh maps,
and that the fixed-coordinate counterexample is model-only because current
closed schemes have no fixed carrier. It also confirms the stated source gaps:
source-derived ports, source-boundary construction, recursive/effect behavior,
and arbitrary source caller contexts remain unproved. This review does not
certify source semantics, candidate soundness, or production readiness.

Recommended next action: isolate the owning source-boundary construction that
retains a fixed-context identity and its original joint constraints; check that
certificate against boundary obligations 1–3 before extending incoming-use
reconstruction beyond the all-local scalar projection. Another lattice-only
probe would leave that representation/source premise untouched.

## Dependency freeze and commit packet

The producer's source HEAD and all inspected dependency SHA-256 values were
unchanged after the campaign. Frozen direct dependency hashes:

```
a8e91f292a0e04212de89bc044127154a91660473fd483d1a61a87190ee3d542  notes/design/2026-10-04-inference-research-playgrounds.md
9e117cac7bf5566d231b8cd7499222913ba639510d33d9a99d62b50118b40271  notes/progress/2026-10-05-scc-generalized-boundary-contract.md
e0aa8d78212aa67558fbfb43928dfee3040a51145e56e1c598d3344138c67206  notes/theory/2026-10-08-candidate-own-row-acyclic-model.md
9d6fa3e7cb485dc259bd4cc50b7593ee8334adf2a1ef9189e49414b5deaebc45  tools/research_candidate_own_row_acyclic.py
08fe67474ab2b36a44fd7028ccd6f9966c0b792a2330391f9e426e81c874a173  notes/progress/2026-10-08-shadow-apply-parameter-candidate.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
6f029758c19c99e397b9653af842b39ca680ece077b65322606266987515ab88  crates/yu-solver/src/f5c_generalization.rs
8f1db3a282956b7deaf312cec6668808c5c4137adb5f964ca7cc10ef471a9c81  crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs
6b2d9d53546fc2218132dad65fac8619ec125c65817af5fe42239ebc85ffee80  crates/yu-solver/src/f5c_binder_substitution.rs
236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2  crates/yu-solver/src/lib.rs
```

Commit packet:

- Exact leased paths: `notes/theory/2026-10-08-candidate-own-row-closed-q-use-reconstruction.md` and
  `tools/research_candidate_own_row_closed_q_use_reconstruction.py`.
- Source baseline SHA: `45fb91e069120f05741a0a4d488e80b38ca59ceb`; checkpoint base SHA: `62518f6f4e5961a857290f3ae36a00d6eb271e95`.
- Changed dependency hashes: none; checker SHA-256
  `7dfe5a08e8ab01e5fbb000344ff4deb2ea08c177d8604dc581d606365277b9fb`.
- Review status: accepted within declared scope by one independent compiler-referee.
- Checks already run: one command above; narrow source locator reads;
  dependency hash and HEAD recheck. The producer ran no builds or Git mutations.
- Proposed checkpoint message:
  `research: characterize acyclic closed-Q incoming-use reconstruction`.
- Shared deltas intentionally left for primary/curator: record conditional
  all-local emitted-constraint projection, fixed-coordinate closure mismatch,
  model-only two-fixed obstruction and remaining source-adequacy premise;
  keep `CandidateOwnRowGeneralizationModelUnresolved` and all broader gates open.
- Task/progress/theory-index synchronization is deferred because the primary
  worktree has a concurrently changing source-call lane and dirty
  `tasks/current.md`; the research checkpoint is isolated in a clean worktree.
