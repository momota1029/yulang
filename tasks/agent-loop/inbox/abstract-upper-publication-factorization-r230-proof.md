# R230 proof handoff — revision 1

Sprint: R230, contract revision 1, SHA-256
`38139890a715aa7c11a8a788d04ee442696c7755a38c7401988ad6201d3d5ef3`.
Baseline: `9137e14caa418cd3f686fc892b9cea9502a70b5f`.
Worker: `/root/r230_proof`, constructive leaf. No descendants. Requested role
`lean_prover`; actual model/effort not independently exposed to this leaf.
Outcome: **constructed conditional structural mathematics; focused kernel build
reported accepted by Luna; final complete type/axiom audit and independent review
pending at freeze**. This handoff is not self-certification.

## Frozen artifacts and exact writes

- Proof: `notes/theory/lean/YulangClosure/AbstractUpperPublicationFactorizationR230.lean`
  SHA-256 `ee16a4e68bb6357a51877a83e78239db08a0789eecd090f387760db2c2632a50`,
  49,723 bytes, 51 authored theorems. Final change after the accepted stage 3
  adds only the complete `#check @...` / `#print axioms ...` audit surface.
- Handoff: this exact file, revision 1. Its byte hash is sent with intake.
- No scratch files, cache writes, compiler edits, dependency/config edits,
  root imports, test changes, shared record changes, Git operations or children.

**Writes stopped** after this handoff. Only Luna owns verification/cache,
independent review assignment, adjudication, shared records and integration.

## Governing source and actual scope

Actually located and read the original local manuscript
`/home/momota1029/rust/simple-sub-reference-paper.pdf`, SHA-256
`5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`,
using `pdftotext -layout ... -` (stdout only). Relevant passages: §3.5.1's bound
level invariant and fresh instantiation, Figs. 6–9; §5.3's soundness/completeness
statements and distinction from the leveled let-polymorphic extension. This
proof does not formalize Fig.12 recursive coalescing or import paper principality.

Read the original parent scope in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1–3 and the
source-scope obstruction (§5 locator); SHA-256
`3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
Read the authoritative top-level inference principles and
`notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6; the latter hash is
`ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
The birth-level Value graph in that correction remains distinct from this
module's type-bound SCC. Research drafts are not semantic authority.

Actual parent definitions were read in `YulangClosure/Contracts.lean`,
SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`:

- `YulangClosure.SourceProblem.SourceScopedCoverage` quantifies every supported
  source, original scope, source witness and generated problem, and requires
  one solution with `sameScoped` for that SAME witness.
- `YulangClosure.SourceProblem.PrincipalCoverage` additionally requires a
  principal solution and every original source derivation to factor through a
  solution carrying its same original scope/witness under `instanceOf`.

## Dependency authentication

All fixed dependency hashes rechecked after construction, unchanged:

| Input | SHA-256 |
| --- | --- |
| `AbstractUpperInsertionInvariantR229.lean` | `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a` |
| `AbstractBoundCycleNormalizationR223.lean` | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |

Pinned configuration read: Lean `leanprover/lean4:v4.35.0`, no external packages,
`-j1 -M1024`. Pin/lakefile/manifest hashes respectively:
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`,
`212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
`058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

## Construction and exact theorem interfaces

Namespace for every authored theorem:
`YulangClosure.SimpleSub.UpperPublicationR230`.

1. `owned_clauses` extracts both owned bound sides and proves their mapped
   clauses equal R223's actual `physicalBounds`. `owned_upper` then derives
   that only negative/upper bounds occur on R229 histories, rather than
   deleting positive bounds by definition.
2. `bound_levels_closed`, `nonGeneric_false`, `stopped_closed` derive closure
   from `UpperInsertionR229.History`. `connected_levels`, `class_levels_same`,
   `capture_class_uniform` force equal levels and capture flags in actual SCCs.
   `class_minimum_level` identifies R223's actual fiber minimum with the
   original level at each in-scope class; `mapped_stopped_closed` proves the
   needed post-map closure. No closure/uniformity hypothesis is supplied.
3. `queryRoots query := ScopedPublication.vars query`; `query_covered` and
   `normalized_roots_computed` derive both original and normalized coverage.
4. `path_publication`, `mapped_reach_lift`, `mapped_owner_reach` derive copied
   SCC paths from the EXISTING owner-local `Published.copy` rules. They do not
   replace publication with full-store copying.
5. `publication_pushforward` maps ANY original owner-local publication
   solution to the mapped owner-local publication using the SAME valuation.
   `publication_pullback` constructs the reverse valuation using a computed
   bound `useCount uses`; all inactive-image and stopped-closure conditions
   are discharged from history. `pullback_query` gives exact equality for
   each allocated original query at every requested use.
6. `mapped_normalized_base` proves the exact named R223
   `(normalizedBounds state).Satisfied rho`. Mapped publication retains its
   own copied and duplicate clauses; no syntactic equality with
   `normalizedBounds` is asserted.
7. `publication_diagonal` constructs one valuation from ANY physical base
   solution. All active use blocks interpret their original row, while every
   allocated inactive anchor stays literally unchanged.

Principal terminal theorem (source statement, printed elaborated type is part
of the final requested audit):

```lean
YulangClosure.SimpleSub.UpperPublicationR230.terminal_solution_factorization
  {problem : CoreProblem} {state : CoreState}
  (valid : problem.inputValid = true)
  (history : UpperInsertionR229.History problem state)
  (terminal : state.pending = [])
  {boundary uses rho} {k : Kind} (query : Term k)
  (allocated : problem.termAllocated query = true)
  (solved : problem.originalConstraints.Satisfied rho) :
  ∃ sigma : Valuation,
    MappedSatisfied state boundary (queryRoots query) uses sigma ∧
    (normalizedBounds state).Satisfied sigma ∧
    (∀ kind i, i < scopeSize state → captured state boundary kind i = false →
      sigma kind i = rho kind i) ∧
    ∀ use, use ∈ uses → Equivalent (query.subst rho)
      (((query.rename (physicalClass state)).rename
        (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst sigma)
```

Here `Equivalent a b` is precisely existing `Sub a b ∧ Sub b a`, including
contravariant Function ports. `sigma` is the single explicit
`diagonal (scopeSize state) rho`, not separately chosen per term/use.
`terminal_publication_pullback` proves both the original owner-local
publication and the terminal original constraint list solved by ONE
`pullback state boundary uses rho` from any mapped publication solution.
`operational_publication_factorization` also handles nonterminal histories
and arbitrary original query terms, given an original publication solution;
it chooses `sigma = rho`. Allocation is required for diagonal/pullback query
transport, and is explicitly checked with `problem.termAllocated query = true`.
It is not presumed for arbitrary future query coordinates.

`self_upper_history` / `upper_only_history` construct the actual successful
one-step histories. `self_upper_application` and `upper_only_application`
instantiate the terminal theorem, retaining exact normalized bases `[]` and
`[⟨.value, .var 0, .atom 0⟩]` respectively. Their original constraint solution
and allocated-query inputs remain explicit.

Represented: both kinds; variables, atoms, bottom/top, union/intersection; all
four Function ports; record labels/optional flags; tuple order; variant labels
and payloads. Original repeated clauses and all physical owners are retained.
No source constructor is excluded from the parent by this packet; this is only
the finite structural model already fixed by R212/R223/R229.

Omitted/unproved: successful operations beyond R229 upper insertion,
representative-changing histories, nonGeneric propagation in such histories,
extrusion, source generation, recursive regular graph decoding/coalescing,
complete Call/effect evidence, source-scoped publication/uses and principal
ordering. `use_guard_same_snapshot` names the unchanged capture/live metadata
case; it does not cover later metadata-changing operations.

## Actual execution and failure preservation

The leaf ran no Lean/Lake command, no checker and no heavy process. Luna is
sole verifier/cache owner. Actual verifier outputs reported by Luna:

- Resolved Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
- `--version`: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
- `env lean --version`: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.
- Focused command from `notes/theory/lean`:
  `lake build YulangClosure.AbstractUpperPublicationFactorizationR230:olean`.
  Luna reported exit 0 on stages `6c422318...`, `41149b79...`, `908100d9...`,
  and `025ce4db...`; these are build acceptance, not independent review.
- Final source hash `ee16a4e6...` differs from accepted `025ce4db...` only by the
  51 requested printed-type/axiom audits. Final bundled checker and actual
  per-theorem axiom results are **PENDING, not fabricated here**.
- Source scan `rg -n 'sorry|admit|^axiom|skipKernelTC|native_decide' <proof>`
  returned exit 1 with no matches. This does not substitute for axiom auditing.

Material failed build stages, all reported by Luna and repaired against the
actual diagnostics (no proof obligation was moved into a hypothesis):

| Draft SHA-256 | Actual failure and repair |
| --- | --- |
| `c1aeb21b73d1fcad4236d81b7050c2ba26717535e89064b2002d18d2749c59b9` | Unreduced owned clause maps; existential/Or precedence; `History`/`Row` namespace collisions. Qualified names, parenthesized alternatives, explicit map congruence. |
| `f1b40aa1a8098607df8a5689a81e0c116f49a5508f5d218f106db1f6f801124e` | Map composition not unfolded; metadata projection mismatch; edge closure not instantiated. Added `Function.comp_def`, explicit metadata change, exact body-var closure. |
| `5767ff7292f48ffb6ef439e1220a320044114a8da4b30c0d801ef5efe5caa273` | Redundant `simp` made no progress at line 145; removed. |
| `032fbd1903c6e9c9ddacbd7b413a9ae5d99e91c3ed7d66fffe072ba79cd07dd5` | Dependent elimination of boolean edge conjunction failed; explicitly changed to `decide (...) = true`, used `of_decide_eq_true`. |
| `64a3ee60bc08079be02088588565f3bfcbba9c1c439ffa5bee429c536c3fcd4f` | Substitution eliminated `k,j`; replaced references with surviving `kind,target`. Lean diagnostic recovery displayed `sorry ()`; no `sorry` was written. |
| `0ac1f7fa43e9c4332eff418049176c10505c29b9da136f06f222acba72d4a277` | Bound-side projection remained a match; renamed projected clauses did not align. Destructed full Bound and changed explicit targets. |
| `8ad3eeaba11aa649a18454bc2742d2b0dc268d211d579c009014e47dd98b60af` | `Bound.rename_clause` is propositional rather than definitional for unknown sides. Explicit target rewrites before `change` fixed both branches. |

The primary's first summarized stage-1 count was provisional; final actual
surface is 51 theorems. Full audit commands follow the namespace in the proof.
Each is `#check @<fully-qualified-name>` followed by
`#print axioms <fully-qualified-name>`. The bundled checker should enumerate
ALL declarations below, then primary retains its actual printed types, complete
axiom lists, exit and cache-cap receipt. No default/full build is requested.

## Authored declaration audit list

- `YulangClosure.SimpleSub.UpperPublicationR230.owned_clauses`
- `YulangClosure.SimpleSub.UpperPublicationR230.owned_view`
- `YulangClosure.SimpleSub.UpperPublicationR230.owned_upper`
- `YulangClosure.SimpleSub.UpperPublicationR230.owned_bounded`
- `YulangClosure.SimpleSub.UpperPublicationR230.bound_levels_closed`
- `YulangClosure.SimpleSub.UpperPublicationR230.nonGeneric_false`
- `YulangClosure.SimpleSub.UpperPublicationR230.captured_eq`
- `YulangClosure.SimpleSub.UpperPublicationR230.stopped_closed`
- `YulangClosure.SimpleSub.UpperPublicationR230.edge_level`
- `YulangClosure.SimpleSub.UpperPublicationR230.reach_level`
- `YulangClosure.SimpleSub.UpperPublicationR230.connected_levels`
- `YulangClosure.SimpleSub.UpperPublicationR230.class_levels_same`
- `YulangClosure.SimpleSub.UpperPublicationR230.capture_class_uniform`
- `YulangClosure.SimpleSub.UpperPublicationR230.mapped_bound_levels_closed`
- `YulangClosure.SimpleSub.UpperPublicationR230.mapped_stopped_closed`
- `YulangClosure.SimpleSub.UpperPublicationR230.query_covered`
- `YulangClosure.SimpleSub.UpperPublicationR230.subst_equivalent_vars`
- `YulangClosure.SimpleSub.UpperPublicationR230.publication_base`
- `YulangClosure.SimpleSub.UpperPublicationR230.edge_bound`
- `YulangClosure.SimpleSub.UpperPublicationR230.capture_backward`
- `YulangClosure.SimpleSub.UpperPublicationR230.path_publication`
- `YulangClosure.SimpleSub.UpperPublicationR230.physicalClass_eq`
- `YulangClosure.SimpleSub.UpperPublicationR230.class_connected`
- `YulangClosure.SimpleSub.UpperPublicationR230.equal_classes_connected`
- `YulangClosure.SimpleSub.UpperPublicationR230.reachable_class_factorization`
- `YulangClosure.SimpleSub.UpperPublicationR230.query_factorization`
- `YulangClosure.SimpleSub.UpperPublicationR230.reach_same_class`
- `YulangClosure.SimpleSub.UpperPublicationR230.mapped_reach_lift`
- `YulangClosure.SimpleSub.UpperPublicationR230.mapped_owner_reach`
- `YulangClosure.SimpleSub.UpperPublicationR230.reached_term_factorization`
- `YulangClosure.SimpleSub.UpperPublicationR230.bound_clause_covered`
- `YulangClosure.SimpleSub.UpperPublicationR230.publication_pushforward`
- `YulangClosure.SimpleSub.UpperPublicationR230.mapped_normalized_base`
- `YulangClosure.SimpleSub.UpperPublicationR230.use_lt_count`
- `YulangClosure.SimpleSub.UpperPublicationR230.publication_pullback`
- `YulangClosure.SimpleSub.UpperPublicationR230.pullback_query`
- `YulangClosure.SimpleSub.UpperPublicationR230.operational_publication_factorization`
- `YulangClosure.SimpleSub.UpperPublicationR230.class_minimum_level`
- `YulangClosure.SimpleSub.UpperPublicationR230.use_guard_same_snapshot`
- `YulangClosure.SimpleSub.UpperPublicationR230.normalized_roots_computed`
- `YulangClosure.SimpleSub.UpperPublicationR230.diagonal_anchor`
- `YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh`
- `YulangClosure.SimpleSub.UpperPublicationR230.diagonal_base_term`
- `YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh_term`
- `YulangClosure.SimpleSub.UpperPublicationR230.publication_diagonal`
- `YulangClosure.SimpleSub.UpperPublicationR230.terminal_solution_factorization`
- `YulangClosure.SimpleSub.UpperPublicationR230.terminal_publication_pullback`
- `YulangClosure.SimpleSub.UpperPublicationR230.self_upper_history`
- `YulangClosure.SimpleSub.UpperPublicationR230.upper_only_history`
- `YulangClosure.SimpleSub.UpperPublicationR230.self_upper_application`
- `YulangClosure.SimpleSub.UpperPublicationR230.upper_only_application`

## Parent application and first remaining premise

Apply `terminal_solution_factorization` after an actual generated valid
CoreProblem has a successful upper-insertion-only terminal history, an allocated
query and an original base solution. This replaces R223's fixture-only reverse
owner-copy argument with a history-parametric construction and both transport
directions. It does not provide the source inputs.

The first remaining parent premise is the source-to-construction bridge:
from EVERY supported source derivation at its ORIGINAL scope/shared witness,
construct the actual generated constraints and corresponding lawful history,
and show the constructed joint publication/use valuation is `sameScoped` with
that SAME witness. Then `PrincipalCoverage` still requires the original
principal solution and `instanceOf` ordering. Owner: Luna's source/native proof
lane, informed by the separate read-only native owner audit. A valid numeric
CoreProblem, `History`, structural `Equivalent`, and a supplied base solution
do not establish this bridge or any concrete `SourceProblem` instance.

Parent delta **0**; source roots remain **0/4**, packages **0/5**. Independent
review and production authority remain separate, pending gates.

## Resources and stop disposition

Finite assignment bound: 3,000 seconds. No Lean/cache/verification process or
resource use beyond text reads/writes was started by this leaf. Exact worker
elapsed CPU/wall runtime is not exposed in this leaf; primary launch/runtime
accounting remains authoritative. Last sampled UTC before handoff preparation:
`2026-11-01 23:59:49 UTC`. No resource increase, dependency change or extra stage.

All source and handoff writes stop at this revision. Remaining exact action is
Luna's final type/axiom checker, cache inventory and independently assigned
review of these frozen bytes, then parent adjudication. No unresolved child or
scratch lease exists.
