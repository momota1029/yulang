# Production HIR boundary for the source-generated callback core

Date: 2026-10-04
Status: read-only source bridge audit; no implementation authority
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
