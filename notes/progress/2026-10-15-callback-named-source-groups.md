# Named callback source groups: retained construction facts

Date: 2026-10-15
Baseline: `cc37db38ac48ef88ffbc68f1fbd0cab1b5a351c2`; forwarding clarification `c8f065747`
Status: G1 source-fact retention and G2 factual Call joins independently reviewed;
selected-frame, protection/discharge and original hygiene gates remain OPEN.

## Authority and implementation

The [identity decision](../design/2026-10-15-callback-identity-forwarding.md)
records ordinary forwarding of each effect a function does not handle,
without an id-name rule or a new runtime representation. The selected compose
release preserves effect contributions. The [receiver construction](../theory/2026-10-15-callback-identity-receiver-construction.md)
§5 identified missing source facts: a named header's complete parameter group
and actual terminal body. This slice retains those facts at their existing
HIR constructors, with no selection rule or executable effect consumer.

`crates/yu-hir/src/module/local_source.rs` now retains one side-table record
per nonempty named header, at the top-level parameter loop and local
`Work::Initializer` parameter loop. Each record contains:

- DefinitionRoot-branded group identity and authentic definition/local owner.
- Header source and enclosing named group.
- Ordered actual formal IDs and generated Lambda indices.
- Terminal generated Lambda and actual declared-body index.

Each retained expression carries its lexical named group. Expression,
initializer and Catch-arm work items carry the context explicitly across
Apply arguments, Group/Ascription wrappers, If children, Catch children and
block final expressions. A zero-parameter initializer inherits the context
and introduces no group. Lexical restoration and source occurrence allocation
are unchanged.

`LocalSource::body()` and `LocalSourceBinding::initializer` still point to the
first generated Lambda. First Lambda, terminal Lambda and terminal body are
distinct retained facts. No group is reconstructed from a Lambda spine, equal
source keys or matching spellings. Explicit anonymous Lambda support is not
added. The shadow API exports construction records and checked group lookup.

Storage and construction are linear in expressions, groups and parameters.
Retained-byte accounting includes group-vector capacity, formal-vector
capacities and the enlarged expression record. There is no new solver
traversal, scope renaming, receiver key, discharge, Catch subtraction or runtime
state.

## Review and verification

M2: one implementer, one compiler referee for construction/context invariants,
and one spec auditor for exact scope and unchanged source behavior. Both
independent reviews found no findings. The source proof has a separate review.

Checks, each run once with `CARGO_BUILD_JOBS=2 timeout 180s`:

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-hir --features shadow --lib named_function_groups -- --test-threads=1` | 5 passed, 117 filtered |
| `check -q --workspace` | passed, no warnings |

Tests cover ordered top-level formals, nested capture of an early outer formal,
same-spelling bindings/parameters, zero-parameter initializers, Group/Ascription
and conditional context. They use actual parsed source and check authentic
identities, ownership and retained-byte accounting. New-test formatting and
narrow `git diff --check` pass.

Resource accounting: one focused Cargo test process and one workspace check;
at most two Cargo jobs, no concurrent heavy process. Before the build wave,
20 cores and approximately 24.5 GB available memory were observed, with no
Cargo/rustc process. No benchmarks, timing repetitions, Oracle runs, broad test
suites or native runtime executions were added. Logs and frozen source hashes
are under `/tmp/yulang-named-frame-20261015/`.

## Source correspondence boundary and next evidence

The [independently reviewed source bridge](../theory/2026-10-15-callback-named-frame-source-bridge.md)
characterizes named-header construction and proves frame identity conditional
on actual Oracle callee eligibility. It also refutes unconditional eligibility:
for `outer f x = ({ my unused = 0; f }) x`, native formation retains the formal
through `Block.final_expression`; frozen Oracle requires an actual `Expr::Var`
and does not recognize the Block callee. Header-group facts alone do not show
that the two constructors apply to the same calls. This is not an observed
runtime failure or permission to reject the native source or erase its qualifier.

G1 is independent of that premise. Existing validated `CandidateSourceCall`
accessors plus the HIR records already expose the original formal, introducing
group/Lambda, call lexical group, terminal facts and actual wrapper route.
The completed G2 artifact joins those facts using genuine source calls in
focused tests, without additional production metadata or accessors. Its local
observations retain wrapper occurrence/source/range and Block binding counts.
It does not label a result `selected_frame` or `oracle_eligible`.

G2 changed only `crates/yu-solver/tests/candidate_receiver_boundary_release.rs`.
Five added tests cover eight parsed controls: direct compose, captured early
outer formal, direct and nonempty Block callees, Group/Ascription wrappers,
zero-formal initializer, and two renamed ordinary identity functions. Both
direct and Block routes retain native authentication and inference availability.
The three earlier tests remain unchanged. Compiler-referee and spec-auditor
delta reviews both found no findings within this factual scope.

One additional command, under the same two-job/180-second envelope, passed:
`cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_receiver_boundary_release -- --test-threads=1`
(8 tests). The four G1 source hashes remained unchanged. G2 formatting and
narrow diff checks pass; no broader check was repeated for this test-only
addition. Combined gate accounting is two focused Cargo test commands (13
passing tests) and one workspace check, with no diagnostic retries. G2 logs
and frozen hash are `g2-tests.log` and `g2-frozen.sha256` in the same directory.
Final integration checks matched all five frozen code/test hashes and checked
14 new/changed local references without a missing target.

The primary retains the original source bridge. Intended forwarding and
introduction across all native callee routes, matching discharge, latent
values, activation, actual Catch consumption and execution remain OPEN.
No new user decision is needed merely to investigate this source mismatch.
