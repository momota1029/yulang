# Ordinary playground execution

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Status: ordinary private execution gate complete; full user objective OPEN
Baseline: `cdfdb58bb244fecf0c895a6a1d65b2bdee06548c`

## Authority and implementation

The user's continuation authorizes finishing playground, inference and execution
with proofs. Existing source-call scheduling §§1–2A and charter §21 determine
whole-argument delay, Value entry and retained Computation entry. The architect
confirmed that a private provisional evaluator can implement these decisions
without adopting a production core/backend representation.

`tools/inference-playground/src/runtime/` owns a finite source-qualified code
arena, lexical cells, closures, delays and an iterative continuation machine.
Argument Delay captures code/environment only; it does not snapshot handlers or
memoize execution. Name consumption follows its source interface. Definition
materialization alone is cached, with explicit recursive-initialization detection.
Computed definition roots execute in source order, based on the frozen fetch
construction rather than solved effect support or SCC order.

`lib.rs::prepare` shares unchanged parse/lower/candidate/conflict handling between
graph observation and execution. `execute` uses exactly the program's derived
root vector. `--run DEFINITION` prints only a completed value; `--steps N` bounds
machine transitions (default 100,000). Syntax/type failures, unavailable runtime
evidence and exhausted steps withhold output. These are tool outcomes, not new
language restrictions. Default graph observation remains available.

## Proof and review

The [source-to-machine simulation](../theory/2026-10-15-playground-ordinary-runtime-simulation.md)
constructs the actual lexical/Delay/entry/Bind/control invariant. The first
source audit found two counterexamples: a taken no-else branch returned its
value, and heredoc literals bypassed escape decoding. The owning consumers now
discard to Unit and share the decoder; original counterexamples remain recorded.

Fetch classification and module order follow actual source constructors. The
annotation-adapter premise is discharged by the exhaustive Oracle registration
inventory and the current validated HIR envelope: error-generated helpers and
imported cast-rule tables cannot enter it. This covers expression, local and
definition annotations without discarding source formal roles. Future cast-rule
admission must revisit that constructor premise.

M2, two reviewers:

- `runtime_contract_review`: pre-write expectations, CLI/default-inference
  contract, literal/conditional/root behavior and no-adapter source premise.
  Initial ascription and bare-root blockers were resolved by construction or
  explicit unavailable outcomes. Multiplicity claims were not inferred from
  final pure values. A minor bare-root test weakness was repaired by retaining
  an existing selected definition in its witness.
- `runtime_semantic_review`: independent implementation and proof review of
  final artifact `68c0435377e5baa96aa05787d93ad0ee5d665dff6091c3ad9f9a09aaa394a744`,
  with no findings. Closure covers the local constructed-program ordinary
  completed-path simulation, not inference soundness or complete hygiene.

## Verification and resource budget

Primary-owned Cargo commands used two build jobs and a 300-second timeout:

| Command | Result |
|---|---|
| `cargo check -p yu-playground` | passed, no warnings |
| `cargo test -p yu-playground --test runtime -- --test-threads=2` | first repaired snapshot: 14 passed |
| `cargo test -p yu-playground -- --test-threads=2` | final snapshot: 43 passed (3 unit, 20 CLI, 5 inline-lambda, 15 runtime) |
| `cargo check --workspace` | passed once, no warnings |

The four new runtime files, new tests and changed CLI were formatted with
`rustfmt --edition 2024`; unrelated pre-existing library formatting was retained.
Diff whitespace checks pass. No timing experiment or benchmark sample was run
(measurement budget: zero). No workspace-wide test suite or backend suite ran.

The source code arena is built once. Runtime source recursion uses explicit
frames and arena references, avoiding Rust call-stack recursion and ownership
cycles. Lexical lookup follows parent environments; memory grows with executed
transitions. The step limit is not an allocation-safety or solver-time theorem.

## Remaining original obligations

Operation requests, Catch selection/raw continuations, complete receiving-view
evidence and hygiene remain explicit unavailable seams. Bare top-level expression
source roots need authentic retained code, rather than being silently omitted.
Arithmetic, interpolation, imports/member/library/loop coverage is unfinished.
Full B delivery, inference soundness/principality and production cutover remain
open. The separate receiving residual prototype advances the native consumer;
its finite source result does not close these universal parents.

Shared records synchronized: `tasks/current.md`, `tasks/research-lab.md` and
`notes/design/INDEX.md`. The resolved unary-lambda parser question was already
archived in `aefa527a7`; this gate changes no question-board answer.
