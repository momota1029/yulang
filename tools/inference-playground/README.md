# Inference playground

`yu-playground` runs the existing experimental candidate inference path on a
small Yulang source file and prints its finite graph observations. It is a
research tool, not the production compiler path. Its output does not establish
soundness, principality, or production admission.

## Run a source file

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
qualification, parent copies, reuse groups, and settlement state:

```sh
cargo run -q -p yu-playground -- --intrusion tools/inference-playground/examples/nested-recursion.yu
```

Event locations identify the retained call-tail occurrence from LocalSource;
they do not describe a whole-call range. The examples do not yet supply a
source witness for the reuse observations.

This output describes retained state; it is not a chronological runtime trace.
The examples in `tools/inference-playground/examples/` cover identity,
nested recursion, effects, conditional bounds, and a type conflict. The
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

## Scope and limits

The tool accepts at most 65,536 input bytes. It caps each graph's observed
nodes, rows, and bounds at 4,096, and shares the aggregate budgets below with
retained intrusion observations.
The complete output or diagnostic report shares a 1 MiB byte budget and a
16,384-entry observation work budget across all definitions and intrusion state.
The work budget counts raw rows, node and child visits, bounds, definitions,
diagnostics, intrusion events, pairs, groups, reuses, and every printed
source-event incidence. Exceeding a cap rejects the complete report with a
distinct tool-cap error; no partial or truncated report is published.
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

This carrier still does not observe arithmetic, omitted-`else` conditionals,
or string interpolation. These are limits of the carrier, not Yulang language
rejections. The playground also does not prove general solver properties.
Treat a bounded observation as evidence about the displayed case only.

Use the research loop from the
[playground design](../../notes/design/2026-10-04-inference-research-playgrounds.md):
implement a conjectured invariant, check it, break and shrink counterexamples,
revise the conjecture, then prove the actual claim. A passing experiment does
not replace proof or review for production adoption.
