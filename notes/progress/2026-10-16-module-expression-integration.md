# Module expressions: HIR, inference and playground integration

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Integration baseline: `1e62dfdc3`
Status: G2/G3 implementation and actual construction correspondence complete;
G4 implemented with independently reviewed structural/control correspondence.
Whole typed-source definition-materialization/root adequacy remains OPEN.

## Authority and implementation

The [approved ownership design](../design/2026-10-16-module-expression-source-owner.md)
consumes question revision 2 / draft a1 revision 1 at `f40e4235d`. Its authentic
direct-expression extension is implemented across the existing HIR, solver and
runtime owners; it introduces no synthetic definition or exported scheme.

- HIR privately mints each ExpressionRootId from the original direct item.
  SourceRootId honestly tags definition/expression ownership. The old binding
  formation pass finishes before new expression child allocation; ordinary
  output and existing binding identities are preserved. Per-root outcomes and
  private-stage rollback retain the original supported/recovery/error split.
- The solver authenticates SourceReceiver against the exact HIR source, retains
  original Name/use/component/level identities, and uses the canonical peeled
  Ascription endpoint. Definition SCCs publish before expression schedules.
  Expression uses take the existing capture/FreshUse route, outside definition
  SCCs; their authentic occurrence Values enter the existing reference graph.
  Annotation, view, weight and context provenance use the tagged source owner.
- The runtime constructs the mixed original-item demand list, validates opaque
  expression handles against original code joins, and evaluates each expression
  with a cache-free return frame. Results are discarded before observing the
  selected definition. ModuleRun/Invocation remain dynamic owners distinct from
  source provenance. Internal raw templates exclude the scheduler cursor.
  The primitive visibility classifier covers every new expression and child.
- Honest partial definition-owner adapters update the existing sibling APIs and
  tests. README now describes direct expressions and discarded results. Default
  inference selection, header/Act admission and F5 cutover are unchanged.

## Constructive proofs and independent reviews

Mode M2; at most two code reviewers per coherent cross-layer component.
HIR/solver: compiler-referee `ordinary_carrier_semantic` and spec-auditor
`ordinary_carrier_contract`, CLEAN. Runtime: compiler-referee
`runtime_semantic_review` and the same specification reviewer, CLEAN. Public
README delta also CLEAN. Producers do not certify their own work.

- [G2 preservation](../theory/2026-10-16-module-expression-carrier-correspondence.md):
  all five original claims independently CLEAN at producer `57ba5d19…`.
- [G3 actual bridge](../theory/2026-10-16-module-expression-receiver-construction.md):
  §10 independently CLEAN at `df8f57fc…`, consuming G2 and checking every
  relevant constructor, publication, FreshUse and provenance consumer.
- [G4 actual bridge](../theory/2026-10-16-runtime-module-expression-roots.md):
  §10 independently CLEAN at `965b9285…`; user-correction qualification CLEAN
  at `f36e6672…`. Mixed-plan, expression completion, owner and cursor claims
  retain their original scope relative to definition-materialization component
  premises. They do not prove unrestricted typed GetDefinition semantics.

The [consumed source correction](../../questions/2026-10-16-resumed-definition-materialization/receipt.md)
at `1e62dfdc3` selects no repeated-publication or suspended-demand law. A
definition's value reference cannot itself justify handling its initialization
effect at that reference site. Establish a valid typed source capture or actual
unreachability before requesting such a choice. The preexisting materialization
source bridge remains OPEN; this extension neither proves a defect nor closes
that gate through a pure forward-reference test.

## Verification and causal test changes

Primary-owned Cargo invocations were serialized with `CARGO_BUILD_JOBS=2` and
180/240-second caps. Successful final commands/results:

| Command (prefix/budget above) | Result |
| --- | --- |
| `cargo test -p yu-hir --test ordinary_expression_source_carrier` | 5 passed |
| `cargo test -p yu-hir --features shadow --test ordinary_expression_source_carrier` | 6 passed |
| `cargo test -p yu-hir -- --test-threads=1` | 168 passed |
| `cargo test -p yu-hir --features shadow -- --test-threads=1` | 207 passed |
| `cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source -- --test-threads=1` | 5 passed |
| `cargo test -p yu-solver --features shadow-apply-candidate --lib expression_receiver_tests -- --test-threads=1` | 2 passed |
| `cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_source_carrier --test candidate_computation_source_plan --test candidate_effect_annotation --test candidate_operation_source --test candidate_lifecycle_retirement --test candidate_receiver_boundary_release --test shadow_receiving_root_scheme_crosswalk -- --test-threads=1` | 41 passed; final named target correctly gated out |
| `cargo test -p yu-solver --features shadow-apply-candidate,shadow-scc-observer --test shadow_receiving_root_scheme_crosswalk -- --test-threads=1` | 4 passed with required features |
| `cargo test -p yu-solver --test ordinary_source_carrier -- --test-threads=1` | 1 default-path test passed |
| `cargo test -p yu-playground --test runtime_module_expressions -- --test-threads=1` | 10 passed |
| `cargo test -p yu-playground -- --test-threads=1` | all 103 passed, including 3 new internal root tests |
| `cargo check --workspace` | passed, no warnings |

The CLI stdin source `later; 99; my later = { my value = 11; value }; later; my main = 7`
with `cargo run -q -p yu-playground -- --run main -` exits 0 and prints `7`
(90-second cap). Logs are `/tmp/yulang-expression-*.log`; no logs are committed.
All final commands above have no warnings. `git diff --check` is clean.

Failures were resolved at their owners, with prewrite specification clearance:

1. New recovery fixtures use admitted `f(@missing)` rather than assuming bare
   `@` has a HIR expression node. The runtime retains bare `@` as a source
   entrypoint syntax-refusal control; tuple/recovered-carrier refusal remains.
2. Act and annotated-header positive fixtures explicitly use their existing
   opt-in lowering entrypoint. Pure ordinary-carrier cases remain ordinary;
   source strings and result/provenance assertions are retained.
3. The prior provisional `my main = 1; 7` refusal is superseded by the approved
   module-expression contract: it now checks exact output `1\n`. No expectation
   was changed merely to match output.
4. Definition-only test/experiment APIs now check the Definition receiver variant
   explicitly before reading its ordinal; generic expression routing is separate.

## Cost, omissions and next owners

Structural work/storage add one authentic owner/carrier/root per admitted item
and one original use per reference, plus existing constraint/copy costs. Root
transitions add no source scan; expression frames keep constant-size cursor
references. Classifier work remains expected-linear in the complete code graph,
with authentic identity hashing/equality costs. No benchmark, timing/RSS sample
or performance experiment was run (zero measurement samples/processes).

The full solver suite and full workspace tests were not run; focused solver
routes and one workspace check cover this phase. Record-only changes do not
repeat those checks. Primary updates current task, research queue and design
index/status at integration.

Native FIRST-RESULT-ADEQUACY retains its original all-xi,z theorem and primary
owner. Its next decisive premise is original whole-descriptor native predicate
adequacy, including declared Support members, Result/RE/entry and reached
post-checks. The separate runtime source-reachability proof is active. Neither
tests, G2/G3 construction nor this G4 extension closes full inference/runtime,
general visibility/hygiene, principality, production selection or F5 withdrawal.
