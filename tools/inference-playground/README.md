# Inference playground

`yu-playground` runs the existing experimental candidate inference path on a
small Yulang source file and prints its finite graph observations by default.
The optional `--run` mode executes a selected definition with a provisional
source evaluator. This is a research tool, not the production compiler path;
its output does not establish soundness, principality, or production admission.

## Observe the inference graph by default

From the repository root, pass one source path:

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/identity.yu
```

The graph uses finite node references. It includes retained subtype bounds and
row identities. Function nodes label their argument, argument effect, result
effect, and result. Effect operands whose contents are unavailable remain
opaque.

Node and row labels (`n0`, `r0`, ...) are local to each definition's graph.
Intrusion output uses `raw` row ordinals qualified by `Value` or `Effect`;
these are the solver's original rows, not the graph's display labels.

The `--intrusion` option adds retained source associations, including SCC
qualification, parent copies, reuse groups, settlement state, symbolic
directional introductions, and static computation-root source plans:

```sh
cargo run -q -p yu-playground -- --intrusion tools/inference-playground/examples/nested-recursion.yu
```

Event locations identify the retained call-tail occurrence from LocalSource;
they do not describe a whole-call range. The examples do not yet supply a
source witness for the reuse observations.

Static computation-root plans report original Lambda, formal, annotation, and
outer-row positions, the native parameter root, the retained entry row, exact
resolved concrete members, and an optional symbolic row variable. The outer
row is the annotation's root row; nested annotation rows are not root members.
An empty concrete member list (`[]`) does not impose a closed effect cap, and
additional effects are not excluded. The selected annotation policy treats a
contravariant concrete root annotation as local handling permission; an actual
`Catch` performs handling. See the
[annotation policy](../../notes/design/2026-10-10-annotation-effect-hygiene-integration.md).
These plans are static source observations. They do not report a runtime
receiver, grant, or handling event, and do not establish native `Name`, `AE`,
or `FreshUse` transport.

Each authenticated omitted-formal source call retains a distinct symbolic
introduction at exactly its original negative demand's `ResultEffect`, with
original formal/scope, checking use, complete demand, and raw invocation row.
Group, Ascription, and Block callee routes use the existing source authentication;
captured calls retain the formal's original scope. Known provider calls receive
no introduction from this rule. Other unauthenticated routes are unsupported
evidence, not a language-wide absence claim. These records are symbolic candidate
evidence, not event consumption or runtime hygiene; they change neither allowance
semantics nor provider rows and do not establish H1 or production cutover.

This output describes retained state; it is not a chronological runtime trace.
Without `--run`, the command reports inference observations. It does not print a
principal scheme or report current native execution.
The examples in `tools/inference-playground/examples/` cover identity,
nested recursion, effects, conditional bounds, normal-return Catch arms, and
a type conflict. The
examples put top-level declarations on separate lines.

## Read from standard input

With no path, the tool reads piped input. With terminal input and no path, it
prints help. Pass `-` to select standard input explicitly:

```sh
printf 'my identity x = x\n' | cargo run -q -p yu-playground --
cat tools/inference-playground/examples/identity.yu | cargo run -q -p yu-playground -- -
```

Use `--help` to print the command summary. A source conflict exits unsuccessfully
and withholds graph output. Source the current candidate path cannot observe is
reported as unsupported by the tool; this does not reject that source from the
Yulang language.

## Run a definition

Pass `--run` and a definition name to execute the source after candidate
inference accepts it. This stdin example prints the selected definition's
completed value:

```sh
printf 'my id x = x\nmy main = id 7\n' | cargo run -q -p yu-playground -- --run main -
```

```text
7
```

The evaluator executes computed top-level definition roots in source order
before producing the selected definition's value. `--steps N` sets a positive
transition limit;
the default is `100000`. If execution exhausts that limit, the tool withholds
the completed value. `--intrusion` is an inference-observation option and
cannot be combined with `--run`. The optional `--scoped-experiment` selects a
candidate inference experiment; it retains that path's source-availability
restrictions.

The evaluator supports ordinary literal values, lambdas, lexical closures,
recursive local definitions, and applications with `Value` or retained
`Computation` arguments. A conditional without `else` discards the taken
branch's value and returns unit. Type ascriptions and binding annotations in
the covered forms preserve the ordinary value.

Operation execution and `Catch` handling, bare module expressions, arithmetic,
imports, and standard-library operations are not available in this evaluator.
Its provisional execution does not establish production soundness or hygiene.

## Scope and limits

The tool accepts at most 65,536 input bytes. It caps each graph's observed
nodes, rows, and bounds at 4,096, and shares the aggregate budgets below with
retained intrusion observations.
The complete output or diagnostic report shares a 1 MiB byte budget and a
16,384-entry observation work budget across all definitions and intrusion state.
The work budget counts raw rows, node and child visits, bounds, definitions,
diagnostics, computation-root plans and their concrete members and symbolic
row variable, source calls inspected for introductions, intrusion events,
pairs, groups, reuses, and every printed source-event incidence. Exceeding a
cap rejects the complete report with a distinct tool-cap error; no partial or
truncated report is published.
These are tool output and input limits. They do not set a source-language limit
or a solver CPU-time bound.

The conditional example shows the bounds observed for both branches of one
explicit-`else` conditional:

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/conditional-union.yu
```

Its graph includes `IntPositive` and `StrPositive` bounds. Replacing `true`
with `false` leaves both bounds in the observation. The output does not print
a principal type. Conditional result references include conditions and every
branch through the selected Name/Apply/If fragments. Group, Ascription, Lambda
and Block remain fragment boundaries. This scoped construction does not certify
complete source Value-reference adjacency for the whole language.

The normal-return Catch example passes both conditional value bounds through
a binder:

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/catch-value.yu
```

The carrier observes unguarded total identifier or wildcard normal-return arms.
A binder refers to the original scrutinee value; the scrutinee effect and every
arm body's effect contribute to the Catch output. Both conditional branches
remain present for either constant condition. Catch adds no result reference
fragment to the existing Name/Apply/If construction.

The operation Catch example uses a resolved monomorphic operation declaration:

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/catch-operation.yu
```

The declaration supplies the operation's payload and response types. The arm
binds the payload and continuation, checks that the payload has type `int`, and
resumes with a `str`. In this carrier, the raw continuation returns the
original scrutinee value, and the arm runs outside the selected handler. The
effects of computing a response argument also remain outside that handler. The
current conservative effect upper bound reuses the original scrutinee effect
and retains the scrutinee and all arm effects without subtraction. This is a
provisional approximation; it does not claim that raw resumption must re-emit
the original request. The no-suffix raw continuation is semantically pure.

Operation arms currently support identifier or wildcard payload and
continuation patterns, or an empty call pattern. Normal-return arms support
unguarded total identifier or wildcard patterns. Generic operation-arm rigid
opening, complete residual/effect hygiene, guards, labels, non-total and tuple
patterns, and chained operation heads remain incomplete in this carrier. These
are carrier limits, not language rejections.

This carrier also does not observe arithmetic or string interpolation. The
playground does not prove general solver properties. Treat a bounded
observation as evidence about the displayed case only.

Use the research loop from the
[playground design](../../notes/design/2026-10-04-inference-research-playgrounds.md):
implement a conjectured invariant, check it, break and shrink counterexamples,
revise the conjecture, then prove the actual claim. A passing experiment does
not replace proof or review for production adoption.
