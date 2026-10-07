# Default-off parameter Apply and own-row generalization experiment

Date: 2026-10-08
Branch: `research/simple-sub-intrusion`
Integration baseline: `375d21eb0d7d64fe97830636e0704f761d90863e`
Status: independent implementation reviews passed; executable shadow only
Mode: M2; compiler-referee and performance-auditor
Authority: user authorization for parallel default-off experimental implementation;
F5 foundation parameter identity, whole-scheme freshening and correlation invariants.
Production cutover authority: none

## Executable slice

The `shadow-apply-candidate` feature extends the private candidate solver to
single-parameter Lambda bodies containing retained HIR Integer, own Parameter,
resolved module Name, Group and Apply constructors. Nested Lambda, local Bind,
unresolved references and recursive definition SCCs remain unsupported. The
candidate consumes retained HIR; it does not reconstruct a grouped callee that
the current lowerer already represented as Error.

Parameter references reuse the actual level-one startup row. Deferred endpoint
recipes distinguish component positions from parameter positions, and enter
the existing constraint owner after startup. They preserve child-before-parent
admission, occurrence provenance, directed value flow and ordinary module-name
incoming substitutions. Checked counts and fallible reservations include the
new recipes. No parameter occurrence proxy, equality merge or definition-use
substitution is introduced.

Preflight measures retained expression depth with root depth one and one
increment per Lambda body, Group child or Apply operand. Depth above 128 is
rejected before recursive emission. This bounds the emitter stack; it does
not claim a bound on solver work or materialized output.

## Generalization experiment and rejected global repair

The new source witness `my id x=x; my wrap y=id y; pub out=wrap 1`
exposed an existing generalizer defect: expansion of `y <= fresh-id <= result`
erases each bounded row's own symbol. Census then sees disjoint one-sided
terminal variables and exports `Top -> Bottom`, making `out` Never.

An initial unconditional diagonal prototype restored candidate Int but failed
the unchanged normative `my f x=f` test: it introduced an extra Q. It also
disabled memoization when every retained symbol was marked uncacheable.
Neither failure was accepted by changing the test expectation. An outer
recursive-bound-purpose distinction alone does not establish a complete
production repair; forwarding rows on guarded cycles remain unresolved.

The selected executable gate fixes its experimental mode at candidate
collection/session startup for the entire memo lifetime. Ordinary collection
keeps the mode false. Both candidate generalizer sinks preserve a nonroot
row's symbol alongside its positive lower union or negative upper intersection.
Stable ordinary row references use existing incidence-aware summary promotion;
active-path reentry still taints its frames. There is no per-root mode,
cross-mode summary reuse, new cache key, or merging of one-way subtype rows.

`CandidateOwnRowGeneralizationModelUnresolved` is carried by every candidate
call/export alongside the unresolved pure-effect, admission, invocation and
generalization/fresh-use correspondence premises. Candidate output remains a
private observation, never a publishable production `SolvedModule`.

Acyclic definition SCCs do not imply absence of recursive types: `x x` can
generate guarded type recursion. The candidate retains that unresolved
interpretation. Its tests cover closure/parity or atomic availability failure,
not source acceptance or recursive principality.

## Independent review

The compiler referee found no blocking, major or minor finding in the frozen
five-file executable slice. It checked startup-row reuse, recipe ordering and
provenance, count/reservation joins, module freshening, depth preflight, private
publication and both generalizer sinks. It expressly did not certify a
production repair, effects, admission or principality.

The performance auditor found no blocking cost finding in the candidate
experiment. Each bounded expanded row adds one leaf/aggregate edge and up to
one duplicate comparison per bound child. Existing metering/reservations and
summary promotion account for that work. A three-row cold/warm guard verifies
admissions, increased shared hits, unchanged uncacheable count and materialized
incidence. No timing or general recursive/diamond complexity claim is made.

The pre-write spec audit permitted the source-envelope fixture updates as
experimental contracts under the user's authorization. Previously unsupported
own-parameter Apply and module-name bodies now have candidate coverage. The
retained-HIR boundary and exact depth measure resolve its earlier findings.
The proposed changes to production raw expansion expectations were not applied.

Frozen SHA-256 reviewed by both reviewers:

```text
af28db57c5a28cce00255ff3ac14b878dae06e2eb2a117d71110f8025aea8169  crates/yu-solver/src/lib.rs
16bf5baf651b9e98b4cb5c3e3b12956ac40df0070ea06cec008be69a6c7cc4b7  crates/yu-solver/src/shadow_apply.rs
26d48cf69863b47051e05ee20083a6e28078c5464bad8aa48dd283c3f305a4d9  crates/yu-solver/tests/shadow_apply_candidate.rs
6f029758c19c99e397b9653af842b39ca680ece077b65322606266987515ab88  crates/yu-solver/src/f5c_generalization.rs
8f1db3a282956b7deaf312cec6668808c5c4137adb5f964ca7cc10ef471a9c81  crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs
```

## Verification

All Cargo commands use `RUSTC_WRAPPER=`, `-j 2`, `--offline`, and tests use
`-- --test-threads=1`. One Cargo process runs at a time.

- `cargo test -p yu-solver --features shadow-apply-candidate --test shadow_apply_candidate`: 12/12.
- Same feature with `--lib shadow_apply::tests`: 6/6.
- Same feature with `--lib f5d_`: 7/7, including unchanged productive recursion.
- Same feature with `--lib tests::<name> -- --exact --test-threads=1`: 1/1 each for
  `candidate_own_rows_preserve_shared_memo_and_materialized_incidence`,
  `f5c_replayed_lower_guard_keeps_unmatched_and_upper_sided_rows`,
  `f5c_normalized_census_ignores_traversal_only_direct_intermediary`,
  `f5c_recursive_upper_census_eliminates_new_negative_only_row_to_top`, and
  `f5c_recursive_lower_census_eliminates_new_positive_only_row_to_bottom`.
- `cargo test -p yu-solver --features shadow-f5 --test shadow_apply_candidate`: 1/1 with the candidate feature off.
- `git diff --check`: passed.

The source differential compares ordinary diagnostics, facts/provenance,
stable traversal/fact counters and exported schemes before/after candidate
execution, including a parameter/group body. It is same-binary noninterference
evidence, not cross-feature behavioral equivalence.

`cargo check -p yu-solver --all-targets --features shadow-apply-candidate
-j 2 --offline` passed at the phase boundary (5.37 seconds, no warnings).
Whole-workspace
tests, allocation-failure injection across new recipe paths, and large symbolic
graphs are omitted. No benchmark processes or samples were consumed.

## Remaining authority and gates

### Frozen mechanism correspondence

A bounded explorer read immutable Oracle objects at
`a58eefc31e22141574b6f20c6a5748151c6d79f1` from the original workspace's
object database; no Oracle execution or semantics adoption occurred.
Historical locators refer to that revision, not the current source tree.

- `crates/infer/src/compact/collect/mod.rs:746,765`: ordinary bound projection
  retains the same variable's own polarized occurrence.
- The same file at `1099` and `952–972`: bare positive and eligible unweighted
  negative variable bounds become Secondary references without recursively
  expanding the target's complete bounds. The fixture at
  `compact/tests/case_01.rs:609` checks that distinction.
- Collection at `761,776` and `collect/type_nodes.rs:653`: recursive reentry
  stores the complete side in an interval table and returns an owner reference.
- `compact/analysis/mod.rs:213` and `analysis/occurrence/mod.rs:490`: polarity
  elimination and co-occurrence run to a fixed point; recursive centers receive
  distinct co-occurrence treatment.
- `generalize/core/free_vars.rs:30` and `generalize/tests.rs:784`: historical
  recursive owners may also be quantified. This differs from current separate
  Q/R ownership and prevents direct transplantation.

Thus the candidate shares the historical own-symbol mechanism but not the
whole historical generalization algorithm. The next production repair must
justify the interaction of ordinary references, direct bounds and guarded
recursive owners under current F5 authority. Oracle representation is evidence
of an implementation mechanism, not the authority for that judgment.

Canonical status counts remain 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC and 1 IMPLEMENTATION-ONLY. No proof or semantic node closes.
The production generic-chain defect and recursive forwarding judgment remain
explicit blockers for adopting this generalizer algorithm. Source typing,
effects, original contracts, principality and production conformance require
their existing independent proofs. The next implementation gate replaces
unresolved candidate premises only with reviewed rules; production cutover
remains prohibited.
