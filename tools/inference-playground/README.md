# Inference playground

`yu-playground` runs the existing experimental candidate inference path on a
small Yulang source file and prints its finite graph observations by default.
The optional `--run` mode executes a selected definition with a provisional
source evaluator. This is a research tool, not the production compiler path;
its output does not establish soundness, principality, or production admission.

## Browser playground

The experimental inference and execution entry points are also available in a
local WebAssembly playground. From `web/playground/`, install the JavaScript
dependencies once with `npm install`, then run `npm run dev` or create a static
build with `npm run build`. `npm run check` builds the page and runs a Node
smoke test against the generated Wasm; `npm run typecheck` checks the page
sources. The browser runs inference and evaluation locally through
`apps/yulang-wasm`; source is not sent to a server.

The browser exposes the same source subset and limits as this playground. It
does not provide Yulang2 compatibility, standard-library imports, arithmetic,
or the production compiler. Unsupported source is reported by the current
candidate/evaluator path rather than being assigned a new language diagnostic.
Its bundled execution examples cover identity, closure capture, recursion,
module expressions, conditionals, handled operations, continuation resumption,
and nested handlers, plus integer `case` patterns with a wildcard fallback. The
examples exercise implemented paths; they do not establish completeness for
any of those language features.

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

This output describes retained inference state; it is not a chronological
runtime trace. Without `--run`, the command reports inference observations.
It does not print a principal scheme or report runtime execution.
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

For accepted source, the evaluator interleaves supported direct top-level
expressions with computed definition roots in source order. It discards each
expression's result before producing the selected definition's value.
`--steps N` sets a positive transition limit;
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

The experimental `case` carrier supports integer literal patterns and `_`.
Arms are checked in source order at runtime; a case with no matching arm has no
runtime result. Pattern binders, guards, labels, and non-integer patterns are
outside this initial slice.

Supported resolved operation calls use the declaration's `Value` or
`Computation` entry and produce an operation request. If a request remains
unhandled, `--run` reports it and withholds the selected definition's output.
A `Value` payload is evaluated before the request is exposed; a `Computation`
payload remains unevaluated.

A `Catch` value arm runs after the scrutinee returns and outside that catch's
delimiter. A binder receives the returned value; a wildcard arm runs its body
without binding it. If no value arm is present, the normal return passes
through.

A matching operation arm can run when the runtime has enough receiving
evidence for that request. A ground `[io]` computation formal with result type
`()`, `int`, `bool`, or `str` supplies handling permission to its own receiving
`Catch`, even when inherited coverage is unknown. This stdin example resumes
the request and prints `11`:

```sh
printf 'act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay (io::tick 7)\n' | cargo run -q -p yu-playground -- --run main -
```

```text
11
```

`Catch` can also handle a direct primitive operation call without a computation
formal when the whole program uses the closed primitive form. This stdin
example prints `7`:

```sh
printf 'act io:\n    our tick: int -> int\nmy main = catch io::tick 7 { io::tick(p), _ -> p }\n' | cargo run -q -p yu-playground -- --run main -
```

```text
7
```

The closed form covers primitive operation payload and response types: `()`,
`int`, `bool`, and `str`. It does not cover lambdas, aliases to operations,
continuation binders, or `Computation` parameter ports. Every definition in the
program must fit this form, so even an unused callable definition withholds
the evidence needed for this direct handling path. The receiving `[io]`
computation formal described above remains a separate handling path for these
four ground result types.

Operation arms support declared primitive payload types `()`, `int`, `bool`,
and `str`. A total identifier or wildcard payload pattern can bind or discard
the payload. An empty-call pattern is also a wildcard for the payload and does
not require a unit payload. A response does not need to be `int` when the arm
discards the saved continuation. A continuation binder can instead receive the
saved continuation. Calling it with a value of the declared primitive response
type resumes the captured computation with that value. The saved context keeps
current binding cells, forwarding handlers, and normal-return arms. It excludes
the selected shallow `Catch`, so that handler cannot catch a request emitted
after resumption.

Continuation capture remains unavailable when its saved path includes a
top-level global read or root materialization. The CLI also exposes no external
response input for an unhandled request. Operation selection for
`Computation` or nonprimitive payloads, and decisions that require complete
inherited coverage, remain unavailable. When evidence is missing, `--run`
reports the request as unavailable and withholds the selected definition's
output.

Arithmetic, imports, and standard-library operations are also unavailable in
this evaluator. Its provisional execution does not
establish production soundness or hygiene.

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

The operation `Catch` example below is an inference-carrier observation. It
shows payload and raw-continuation typing, not execution with `--run`, because
it lacks a local receiving certificate at a declared computation formal.

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/catch-operation.yu
```

The declaration supplies the operation's payload and response types. The arm
binds the payload and continuation, checks that the payload has type `int`, and
resumes with a `str`. In this carrier, the raw continuation returns the
original scrutinee value. The effects of computing a response argument also
remain outside the selected handler. The current conservative effect upper
bound reuses the original scrutinee effect and retains the scrutinee and all
arm effects without subtraction. This is a provisional approximation; it does
not claim that raw resumption must re-emit the original request. The no-suffix
raw continuation is semantically pure.

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
