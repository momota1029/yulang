# Sprint R64 — derive the fixed whole-ascription relation

Status: CANDIDATE until Luna verifies this manifest and baseline, obtains a
start-boundary confirmation, reconciles current writers and activates the exact
contract in `current.json`.

Branch / baseline: `research/simple-sub-intrusion` / `e5e0ac4e5b72c51406fac82ed82986d734bf3552`.
Primary: `/root`; session: `current-conversation-2026-10-19-r64`.
Parent: original computation-forwarding preservation §§1,6–7; original source
domain and quantifiers unchanged; Simple-sub A/B OPEN 0→0; R50 NOT ADOPTED.
Open item: `R61-SOURCE-ASCRIPTION-FORMATION-1`.

## Fixed source and target outcome

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Attempt the maximal noncircular derivation of the source contract for this
whole-definition Function ascription. First construct source constraints and
evidence from authentic settled source rules, including original `I,d,L,t,n`,
distinct occurrences `p_t,p_A,p_R`, and joint `xi=(nu,K,D)`. Then separately
attempt a source/native correspondence for the same original provider/carrier,
checking/exposed result evidence, and typed substitution/transport. Return
either the completed derivation under those rules or the first exact clause
whose authentic derivation is unavailable, with its attempted premises and
source owner. A bounded obstruction adds evidence only if it identifies an
isolated clause beyond R63's general unresolved relation.

Candidate correspondence is an output to construct, never a premise:

```text
Sol_src = { sigma | sigma satisfies the source constraints derived first }
Sol_nat = { rho   | rho satisfies the actual native constraints, if a native
                    derivation for this fixed source is admitted }
Corr_xi(sigma,rho) = evidence derived from the authentic source/native
                     correspondence for this same provider/carrier
```

Required proof obligations, only where the relevant judgments are actually
derived:

```text
for every sigma in Sol_src, construct rho in Sol_nat with Corr_xi(sigma,rho)
for every rho in Sol_nat, construct sigma in Sol_src with Corr_xi(sigma,rho)
for each legal typed substitution theta, show both judgments and Corr commute
  while preserving the same provider, K,D, positions, local permissions,
  ordinary constraints, correlated results and all actual Q dependencies
```

The fixed source currently encounters native negative-`p_A` guards. Do not call
a prospective schema an actual native derivation or `Q`. A source derivation
may be a valid result while native realization remains open. No R60 scalar
lifting unless its actual-Q independence premise is derived.

## Derivation method, discriminators and falsifiers

Use structural induction only over authentic source/annotation/type rules
found in the pinned authorities and original source constructors. Construct
`Sol_src` before looking at desired native inequalities. Derive each clause
from an applicable rule or source producer; a missing clause stops that branch
and is recorded as an exact unsupplied premise. Do not promote an induction
hypothesis, a candidate judgment, caller-supplied wiring, or a native guard
into a source rule.

At the `p_t` case, use retained formal annotation and resolved body Name only
for what the selected rules license. Do not identify its permission with
`p_A`; derive the `p_A` and `p_R` cases at their own source positions. Preserve
open incoming `E`, every ordinary generated constraint, scopes, joint `K,D`,
and result correlations. Build any `Corr` only from authentic mappings and
consumers; expose the exact first missing owner if no such mapping exists.

Falsify a proposed derivation on any unlicensed rule, circular `Sol_src` /
`Corr` / `Q`, provider/carrier or position change, permission transport added
without derivation, lost ordinary constraint/result correlation, a legal source
solution without native lift, an admitted native solution without source
reverse interpretation, or a typed substitution that changes original
evidence. A semantic-ambiguity claim requires two complete source derivations
compatible with every applicable decision and differing on an original
observable; missing documentation alone is not ambiguity.

## Continuing lanes and exact outputs

- Configured prover / Sol high, 600 seconds: derive the source judgment,
  solution meaning and legal substitution first; then attempt both
  correspondence directions and transport; freeze the maximal derivation or
  exact first unsupported clause. Write only
  `notes/theory/2026-10-19-r64-whole-ascription-derivation.md` and
  `tasks/agent-loop/inbox/20261019-r64-proof.md`.
- Luna / high, 500 seconds: map each candidate source clause to authentic
  syntax/identity constructors, selected rules, and native consumers; report
  whether the source rule licenses the clause and whether any actual native
  path exists. Do not implement or change semantics. Write only
  `notes/progress/2026-10-19-r64-ascription-clause-owners.md` and
  `tasks/agent-loop/inbox/20261019-r64-implementation.md`.
- Fresh compiler/source-owner and spec/domain reviews, 200 seconds each, only
  after both authors stop and all four author outputs freeze. Compiler review
  checks source/native applicability and native guard claims; spec review
  attacks derivation completeness, conservativity, circularity and substitution.
- Luna integration, 300 seconds. Total grant: 1800 seconds; Astra 0; actual
  runtimes UNKNOWN unless reported; no carryover. Luna's exact integration
  output is `notes/progress/2026-10-19-r64-closeout.md`; Luna also owns the
  central `tasks/agent-loop/current.json` snapshot and this contract.

The lanes are a source proof and its independently useful producer/consumer
map, not another crosswalk/API validation. If no implementation slice is
licensed, name at least two inspected owners and retain `NO_SAFE_CODE_SLICE`.

## Permissions and stop boundaries

Read the exact pinned sources below. No code, semantic or test edits; no tests,
builds, compiler execution, probes, runtime, instrumentation or measurements.
No guard removal, new inference rule, source narrowing, adopted semantics,
production claim, parent closure or R50 promotion. A genuinely new semantic
choice is reported to Luna without adoption. Dependency/authority changes,
first unsupported clause, resource cap, STOP or session end stop the affected
lane. No work starts before exact hashes/baseline and live writer identities
are reconciled and the contract is activated. Luna alone assigns reviewers,
adjudicates, updates current state, stages explicit paths, commits and pushes.

## Frozen dependency manifest

All pins below are direct byte dependencies at the stated clean baseline.
Verify every hash again before activation; R63's manifest does not substitute
for this manifest.

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536  questions/2026-10-05-function-call-view-formation/approved-answer.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
03a40bdba3bad125f93d5290b7f3519aceba17b93c20c5026ac9194b128c7f67  notes/theory/2026-10-19-r60-paired-annotation-interface.md
d4f3bce801167a8b8a2b6ff1edc8b688b163bb03bab9cc0186d864533b24c3e5  notes/progress/2026-10-19-r60-closeout.md
ff5791362fc0b63f67450f079c2c99246e90190484636a229d2afd5c5c615423  notes/theory/2026-10-19-r63-whole-ascription-formation.md
9660b1248f4fc7f6a79fdce9d0129e2af148b4122b3194d99cdbd7b4f6050893  notes/progress/2026-10-19-r63-whole-ascription-owner.md
46b545e54481a931efcda3b3be96e7e6aa63d2b2ce27b97dac78f90dd7091cee  notes/progress/2026-10-19-r63-closeout.md
e017634795a444c566f44eea26c94280bc5292612b26b0fe56f12214d850745e  tasks/agent-loop/sprints/whole-ascription-crosswalk-formation-20261019-r63.md
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
9a13b7b46d4d239d00d8f54ed93e6bc58064410bd556ab8f797242f2e87f6d5d  crates/yu-core/src/shadow_source_annotation_crosswalk.rs
dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95  crates/yu-core/src/shadow_typed_evidence.rs
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb  crates/yu-core/src/shadow_call_formation.rs
714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2  crates/yu-core/src/shadow_derivation.rs
460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66  crates/yu-hir/src/shadow.rs
```
