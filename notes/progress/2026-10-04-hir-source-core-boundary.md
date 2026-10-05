# Production HIR boundary for the source-generated callback core

Date: 2026-10-04
Status: source bridge audit with test-only probes; no production implementation authority
Scope: correspondence between Theorem C's typed source core and current
`yu-hir` lowering
Depends on: [source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)

## Finding

Theorem C defines a source-core generator for lambdas, calls, bind, reify,
explicit computation elimination, operations, and their typed source
derivations. The current `yu-hir` production path does not emit that graph.
This is a concrete boundary in addition to the separate gap between an
operational graph and a finite inference endpoint.

In `crates/yu-hir/src/module.rs`, `ResolvedExpr` currently has only
`Lambda`, `Integer`, `Name`, and `Error` variants (lines 425–449). In
`crates/yu-hir/src/lib.rs`, the separate pre-HIR `HirExpr` can preserve an
associated operator `Apply` (lines 48–69), but `lower_simple_chain` accepts
only a leaf `Value` with no children; a non-leaf associated expression returns
`Unsupported` (module.rs lines 1402–1423). Its supported leaf cases are
integer literals and identifier expressions. The resolved expression shown
here has no call/application, record, operation/request, handler, or explicit
computation-consumer constructor.

Therefore Theorem C's finite-generation induction is a theorem for its
mathematical typed-core derivation graph, not a theorem that the current
production HIR constructs such graphs from raw Yulang input. The new finding
does not refute Theorem C, change accepted Yulang programs, or authorize
compiler edits.

## Closed HIR-to-core subcase: monomorphic pure value bindings

There is a source-produced subgraph that maps directly. Take a finite HIR
module with no `Error` nodes, only integer/name leaves and admitted
parameterized bindings, no annotations, and a fixed monomorphic `Gamma` for
unique module `DefId`s. The lowering clauses create one parameter identity,
resolve each body name either to that parameter or to a fixed module root,
and wrap the atomic body in a lambda (`module.rs` lines 1159–1202,
1422–1464). Occurrences and source ranges are retained. No application is
included; the lowerer rejects a non-leaf associated `Apply`.

The generated derivation maps each HIR node directly: integer to `literal`,
parameter/module name to `name`, and the source-generated lambda to
`lambda(P, result(d_body))`. A source environment maps each `HirParameterId`
to its single core binder and each module `DefId` to its fixed root. For the
discriminating `id x = x` instance, the `NameResolution::Parameter` points
back to the same `HirParameterId` created for the lambda.

The typed-core derivation is syntax-directed:

```text
P = Value(A)                         // unannotated §21 parameter
Gamma[x := Value(A)] |- name x : Value(A)
Gamma[x := Value(A)] |- result(name x) : Comp(empty,A)
Gamma |- lambda(P, result(name x)) : Value(Fun(P,Comp(empty,A)))
```

Induction on the finite HIR binding graph gives the corresponding derivation
for this monomorphic pure value fragment. The body endpoint `A` is shared
through its parameter binding; HIR does not materialize or solve it. The
source tag chooses Pure function introduction, and §21 chooses its
Value-entry behavior. This proves that current lowering supplies Theorem C's
actual Pure identity **value derivation** and the same structural mapping for
all expressions in the named HIR fragment. It does not supply the known
callback callee/use graph, an effectful whole-argument carrier,
`d⁻`/`d⁺`/`b⁺` profile paths, receipt incidence, or the finite complete
endpoint. It is a source-derivation map under fixed `Gamma`, not a theorem
that the future inference generator emits the required constraints. Those
remain distinct source and solver bridges.

## Exact next bridge

To claim raw/production correspondence for the callback fragment, a later
implementation/design gate must identify the source forms admitted by that
fragment and map their resolved HIR nodes to Theorem C's derivation
constructors. The monomorphic pure-value case above closes the HIR map for
its named grammar. Callback applications, effectful argument
carriers, requests, and their `d⁻`/`d⁺`/`b⁺`, receipt, profile, and `K,D`
evidence need production HIR constructors and a lowering theorem before they
can be checked against the theorem generator. This is not yet evidence that
a new runtime or solver carrier is needed; it is a source-shape gap in the
HIR boundary.

No compiler code or tests changed/run. `git diff --check` is the only check
required for this record-only update.

## 2026-10-05 raw callback-lambda parser probe

A test-only CST characterization now runs the bounded source spelling
`host (\x -> x)` through the current expression parser with an empty operator
table. It produces an `MlArgument` containing a parenthesized expression, but
the purported lambda opener is not recognized: the error tokens are exactly
`\`, `-`, and `>`, while `x` is parsed as ordinary identifiers. The retained
empty-table probe is
[`research_unary_callback_lambda_header_currently_falls_back_to_errors`](../../crates/yu-syntax/src/tests/tails.rs).

A second probe supplies a constructed operator table with a `\` prefix
entry. The current parser then consumes the would-be lambda introducer as a
`PrefixOperatorUse` and still reports `-` and `>` as error tokens. This is a
table-level precedence fixture only; it does not assert that source programs
can declare that spelling. It characterizes the collision that the reviewed
parser design avoids by reserving a complete `\ Identifier ->` header before
dynamic-operator lookup, while leaving nonmatching `\` to existing fallback.
The test is
[`research_registered_backslash_prefix_interacts_with_lambda_header`](../../crates/yu-syntax/src/tests/tails.rs).

This narrows the raw-to-HIR gap to a concrete starting point: the current
parser does not produce the selected unary lambda header under this ordinary
operator environment, before the lowerer's already-known non-leaf Apply
rejection is reached. It characterizes present behavior only; it does not
change the accepted source contract or specify malformed-header recovery.
Both focused probes pass. Full-file/header operator interactions and the
subsequent Apply/HIR lowering remain untested, and no production parser or HIR
behavior changed.

## 2026-10-05 call-stage association probe

The existing pre-HIR associator was checked against parenthesized and
ML-argument chains from one through four stages (`f(a)(b)...` and
`f a b ...`). Across all eight generated sources, it preserves one argument
per stage as a left-nested binary structure, with exact source ranges and
identifier leaves. A test-only postorder walk records the source range for
each candidate `call` stage. The executable characterization is
[`research_call_surface_retains_left_associated_stages`](../../crates/yu-hir/src/lib.rs).
An independent delta review found one minor test-contract gap: the first
generated walk did not enforce a uniform stage kind or restrict recursion to
the callee branch. The test now checks both conditions, requires each
argument to be an identifier leaf, and compares all generated call and
argument ranges. The focused test and formatting checks pass after the repair.

This closes only the surface grouping question for those ordinary calls. The
association product stores structural `HirExpr::Value` nodes; it does not
assign call semantics or emit the typed-core `call`/`bind` graph. The
`ResolvedExpr` lowerer still rejects these non-leaf structures, so the actual
source-to-core gap is now localized after operator-chain/postfix association
and before resolved expression emission. Inline lambda parsing remains a
separate preceding gap. The focused test passes; no compiler behavior changed.

## 2026-10-05 test-only application-tree probe

A separate executable candidate now lowers actual associated `MlArgument`,
`CallTail`, parenthesized-expression, and identifier nodes into a test-only
binary `Apply` tree. It enumerates mixed source spellings through four stages,
checks retained application forms, source extent, and unique candidate
occurrences, and separately verifies that `f(g(a))` retains its nested call
as the argument subtree. The focused HIR tests pass.

The first candidate exposed two concrete parser/association facts and was
revised: ML argument parsing can absorb a following postfix call into the
argument (`f a(b)`), and a parenthesized HIR node can contain the accumulated
left expression plus tail children rather than exactly one child. The final
probe checks the exact 14 recovery-free bit patterns among the 30 generated
sources; the remaining 16 currently produce recoverable/error expressions.
This observed subset is not a claim about language legality. It checks the
outer source extent against the associated chain, not every internal node
range. Its generated occurrence counter and tree are
candidate data, not production `HirOccurrenceId` or `ResolvedExpr::Apply`.
This is parser-to-candidate-shape evidence only: it does not establish name
resolution, callback endpoint generation, constraint generation, or Theorem C
correspondence, and it changes no production behavior.

## 2026-10-05 complete lambda-opener predicate probe

A standalone test-only predicate now recognizes the bounded complete opener
`\ Identifier ->` before any operator-table decision would be made. Its
identifier scan mirrors the current lexer shape (XID start/continuation,
underscore start, and one optional `?`/`!` suffix); the generated trivia set is
horizontal space/tab only. Cases cover ASCII and Unicode names, the `_` family,
suffixes, nonzero source offset, a missing body after a complete opener, and
near misses with no binder or no exact arrow.

This predicate is only a characterization of the reviewed reservation shape.
It is not called by the production parser and does not test CST dispatch, body
parsing, malformed-body recovery, or binder ownership. The existing direct CST
tests still establish that current parsing rejects the ordinary single-
backslash spelling before HIR. A paired probe matches the recognized binder
and arrow ranges to actual CST tokens, confirms the body identifier remains
inside the same parenthesized `MlArgument`, and checks the parenthesized span.
This links the header candidate to the retained error-bearing CST shape, but
does not promote it to a lambda node or test body recovery/binder ownership;
parser implementation and callback lowering remain open.

### 2026-10-05 principal call declaration body probe

An independent regression audit found no issue within the changed test and
confirmed that it introduces no production/public HIR surface.

The test-only `research_binding_body_cst_flows_to_apply_candidate` now starts
from the full parsed declaration `my call f x = f x`, selects the direct body
`OperatorChain` from its `BindingBody`, associates it under the retained
operator environment, and passes that actual associated expression through
the existing generic `research_lower_apply` candidate. It checks the complete
candidate tree and source ranges (`f` at `14..15`, `x` at `16..17`, body at
`14..17`) with one application occurrence. This closes a narrow raw binding-
body-CST to research-Apply correspondence for an already-formed declaration.

The production route still stops earlier: `plain_binding_header` admits only
zero or one `PatternMlApplicationTail`, so this two-parameter declaration is
classified `UnsupportedTarget` before body lowering. Even a one-parameter
declaration whose body is an application reaches `lower_simple_chain`, which
rejects its non-leaf associated expression; `ResolvedExpr` still has no Apply
variant. The research test selects the body directly and does not make either
production stage accept the declaration. It proves neither name resolution,
currying/lambda elaboration, Function constraints, nor a typed-core source
correspondence. No compiler behavior changed.

The later bounded candidate `research_multi_parameter_declarations_form_nested_scoped_candidates`
extends this raw-CST path for the actual principal examples `call` and
`higher`. It extracts every distinct identifier parameter, nests research
lambda nodes in source order, resolves body names to those lexical binder
indices, and checks the resulting curried application shapes:
`λ0.λ1.(v0 v1)` and `λ0.λ1.λ2.((v0 v1) v2)`. This is a generic candidate
construction over the parsed parameter/application trees, not a type rule or
production HIR implementation. It does not establish effect ports,
co-occurrence, endpoint constraints, or principal schemes.

Independent compiler-referee review found no blocking, major, or minor issue
within this bounded candidate. Its scope remains deliberately narrow: the
candidate does not assert recovery-freedom for every header/body node, verify
parameter-to-binder source ranges as a separate invariant, or establish typed-
core correspondence. The focused `research_` filter passed all six
characterization tests, and the existing one-parameter admission integration
test passed separately.

An attempted inclusion of the exact acceptance source
`my compose f g x = f (g x)` reached an `Error(Missing)` inside its nested
parenthesized `g x` CST, so it is not counted as a valid candidate case. This
is a current parser-shape observation only; it does not select a grammar
change. The exact source spelling's raw parsing is now an additional earlier
conformance gap to resolve before a complete source-to-HIR theorem can cover
`compose`.

The exact checks for this slice were:

```text
env RUSTC_WRAPPER= cargo test -p yu-hir research_ -- --nocapture
  6 passed; 16 filtered out
env RUSTC_WRAPPER= cargo test -p yu-hir --test simple_module_resolution only_one_recovery_free_identifier_parameter_is_admitted -- --nocapture
  1 passed; 21 filtered out
rustfmt --edition 2024 --check crates/yu-hir/src/lib.rs
  passed
git diff --check
  passed
```

`cargo fmt --check` was also attempted earlier but fails on pre-existing
formatting differences across unrelated `yu-solver` files; it did not modify
them. No production HIR behavior changed.

### Test-only raw-source callback Apply candidate (2026-10-05)

The new private `research_callback_apply_from_error_cst` test helper composes
the bounded header predicate with the current parser's retained error-bearing
CST for `host (\x -> x)`. It requires a single callee identifier before the
parenthesized span, checks exactly one `MlArgument` and the intervening
`OperatorChain` parent/span relationship, checks the full parenthesized span,
and maps the header binder and arrow-following body identifier back to actual
CST tokens. The resulting `ResearchCallbackApply` candidate
contains `callee = host` and a lambda argument with binder/body `x`. Complete
headers with no body, and a missing binder, are rejected.

This is a raw-source-to-test-candidate correspondence for the single
parenthesized unary identity spelling. It consumes CST tokens that production
currently classifies as errors; it does not change parser dispatch, produce a
production lambda or Apply node, test body recovery, resolve names, or emit
typed-core/source-evidence records. The source/HIR and callback endpoint
bridges remain open. Independent regression review found two minor assertion
gaps (argument ownership/cardinality and full-span equality); both were added
and the focused test rerun. Delta review confirmed the assertions and scope
claims; no findings remain.

Verification: `cargo --config 'build.rustc-wrapper=""' test -p yu-syntax research_ -- --nocapture`,
`rustfmt --edition 2024 --check crates/yu-syntax/src/tests/tails.rs`, and
`git diff --check` passed. This test filter ran five characterization tests;
the rest of the package was not run for this slice.

## 2026-10-05 test-only source synthesis shape

The same private candidate now runs the typed-computation-core §6 result-role
shape over `f a`, `f(a)`, `f a b`, `f(a)(b)`, and `f(g(a))`, under a supplied
monomorphic research `Gamma`. It constructs `(I,d,n)` notation trees for
Name and Apply: Value names normalize through `result`, Computation names
through their original `eliminate_p` label, and each application reifies
`call(n_f,n_a)` before normalizing its Computation result. Exact per-call
structural-shadow endpoint triples are checked for staged and nested calls;
`f(g(a))` checks the inner computation remains the outer whole argument.
An empty-row-labelled Computation name remains a Computation through
normalization.

This candidate deliberately stores only effect labels, not source port
profiles, `K,D`, invocation/subtraction evidence, or complete application
constraints. Its endpoint triples are the pure structural-shadow projection,
not a successful concrete inequality or a complete Function query. The core
objects are test notation, not an executable typed-core API; name resolution
is supplied by the finite research `Gamma`. No production HIR, collector,
solver, or endpoint generation changed, and the test does not establish the
callback Theorem C bridge or principal-scheme preservation.

## 2026-10-05 parenthesized same-line application and exact `compose` source

The accepted principal source `my compose f g x = f (g x)` exposed that
parenthesized expression elements used `MlMode::LayoutOnly`, causing `(g x)`
to be parsed as two elements with a missing separator. The approved
[parenthesized ML addendum](../design/2026-10-05-parenthesized-ml-application-addendum.md)
now governs the expression-element owner: same-line ML application is allowed,
comma still separates elements, equal-or-shallower newlines still separate,
and deeper newlines still continue the item. Parenthesized Pattern and Type
owners are separate and were not changed. `(a b)` and nested `f (g x)` CSTs
are checked directly; `(a, b)` remains two elements, and the block-comment
case confirms its internal newline remains opaque with exact surrounding
trivia ownership.

The exact `compose` source now also enters the test-only scoped declaration
candidate alongside `call` and `higher`, producing
`λ0.λ1.λ2.(v0 (v1 v2))` with two application nodes. This closes the parser-to-
research-candidate shape for this spelling. It does not make the production
header accept three parameters, add an Apply node to resolved HIR, generate
Function endpoints, or prove the expected principal scheme.

The now-unused production `MlMode::LayoutOnly` arm was removed after the
focused build exposed its dead-code warning. The generic delimited-recovery
harness now uses `MlMode::All` for parenthesized expressions, and its old
`x y)` missing-separator expectation was updated under the approved contract.
The first full package run then exposed one more stale structural-diagnostic
expectation: `(1 x)` expected a separator `Missing`, although the same-line ML
rule now admits it as an application. A prewrite spec audit confirmed the
expectation was superseded and recommended removing only that row, retaining
the other trivia/slot witnesses and the adjacent `(1x)` separator case. The
focused repair and a delta review both passed with no remaining findings. No
production HIR or inference claim is made.

Exact verification:

```text
RUSTC_WRAPPER= cargo test -p yu-syntax tests::owners -- --test-threads=1
  34 passed; 0 failed
RUSTC_WRAPPER= cargo test -p yu-syntax tests::delimited_recovery -- --test-threads=1
  15 passed; 0 failed
RUSTC_WRAPPER= cargo test -p yu-syntax structural_diagnostic -- --test-threads=1
  9 passed; 0 failed
RUSTC_WRAPPER= cargo test -p yu-syntax -- --test-threads=1
  1387 passed; 0 failed; 1 ignored; doc-tests: 0
RUSTC_WRAPPER= cargo test -p yu-hir tests::research_multi_parameter_declarations_form_nested_scoped_candidates -- --exact --nocapture
  1 passed; 0 failed
rustfmt --edition 2024 --check <seven touched Rust files>
  passed
git diff --check
  passed
```

No broad syntax/HIR suite or production inference suite was run.
