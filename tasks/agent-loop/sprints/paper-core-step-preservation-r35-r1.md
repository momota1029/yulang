# Sprint PAPER-CORE-STEP-PRESERVATION-20261026/r35 — core paper reductions

Status: CANDIDATE pending Luna's hash/lease/runtime acknowledgement.
Branch: `research/simple-sub-intrusion`
Baseline: `0f0d63373bc7762fdef2ae501bbe3a2a75a84ff6`
Contract revision: r1

## Original parent and bounded outcome

The original parent is the manuscript's precise one-step preservation and
display simulation theorem, `docs/yulang-operational-type-safety-ja.tex:1860–1875`.
This packet advances its ordinary core reduction cases without narrowing or
replacing that parent. The governing reduction clauses are `:301–316`; the
execution typing clauses are `:203–240`.

Create a standalone Lean module `YulangClosure.PaperCoreStep` defining a partial
raw computation step for exactly these manuscript cases:

- `letE (ret v) body` by the R28 capture-avoiding single term substitution;
- `force (delay body)`;
- either injection selected by `unionCase`;
- `unroll (roll v)`;
- `field` on a record with the requested label;
- optional/required `lookup` on a record, returning the right injection when
  the label is present and the left unit injection when absent.

The main theorem must retain the unchanged contexts and result type:

```text
PaperComputationTyped D Xi Γ c A → step c = some c' →
  PaperComputationTyped D Xi Γ c' A
```

Also prove that every typed redex in the enumerated cases returns `some`.
Constructor mismatches and unlisted reductions may return `none`; this partial
operator does not interpret `none` as termination, `Fail`, or `Bad`. The module
must not claim complete operational semantics, full progress, full preservation,
the global inference-soundness root, or closure of the paper parent.

## Method, discriminators and limits

Use inversion of the actual `PaperComputationTyped`/`PaperValueTyped` derivation,
R28 `TermSubstitutionTyped` and term-substitution results, and concrete record
lookup reasoning. Preserve one shared environment and the exact type `A`.
The `let` and union-case substitutions must shift variables above the bound
variable and must not capture them. Record lookup must use the runtime label
presence, not confuse the stored `Presence` tag with declaration requiredness.
Required `field` uses the typing evidence and typed record's required-field
invariant. Optional absence has the declared result union type.

Falsifiers: captured binder; wrong union branch; accepting a missing required
field; wrong result type on optional absence; using the raw field `Presence`
tag to choose a lookup branch; unroll result not definitionally equal to the
typing constructor's unfolded type; weakened contexts/result indices; a failed
`some` result for any typed enumerated redex; unsupported axioms or proof holes.

Source correspondence: manuscript `let`, Force, field/lookup, unioncase and
unroll clauses `:305–316`; their static rules `:203–240`; parent theorem
`:1860–1875`. The Lean type relation is partial: do not imply that this module
covers omitted source/native constructors, complete heap graph typing, handlers,
effects, primitive semantics, recursive allocation or `wrap`.

## Frozen dependencies

- Manuscript `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`:
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- Accepted R28 `PaperTermSubstitution.lean`:
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- Pinned Lean: `leanprover/lean4:v4.35.0`; `lakefile.toml` SHA-256
  `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.

R28 is used only for its checked fragment of term substitution. R26/mapOperation,
R30–R34 wrap authority, and the native immutable-graph lane are not dependencies.

## Exact lanes, leases and verification

One fresh registered `lean_prover` constructs and checks the bounded module in
the pinned project checkout. No other worker owns this Lean cache or changes
its frozen dependencies. Worker output leases are only:

- `notes/theory/lean/YulangClosure/PaperCoreStep.lean`
- `notes/theory/lean/.lake/R35Audit.lean`
- `notes/theory/lean/.lake/build` (worker is sole
  owner until a writes-stopped receipt, then primary takes over)
- `tasks/agent-loop/inbox/paper-core-step-r35-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-core-step-r35.md` (one handoff)

All frozen dependencies are read-only. No edits to existing Lean sources,
`YulangClosure.lean`, `lakefile.toml`, Rust, tests, expected outputs, fixtures,
diagnostics, or question files. No descendants or Git operations.

Worker: at most 10 serial Lake/checker invocations and 120 checker seconds.
Primary, after the worker stops: at most 4 serial invocations and 60 checker
seconds, using the handed-off isolated cache. One heavy build at a time. Total
envelope: 14 invocations, 180 checker seconds, 1800 active seconds. No default
full build, tests, Rust checks, network, dependency updates, shared cache use,
or retries after a failed command. Use Lean `-j1 -M1024`; verify the exact
module and every public theorem type/axiom result, and scan the changed module
for `sorry`, `admit`, project axioms and checker bypasses.

Required independent review: one fresh non-author `spec_auditor` after all
writers/checkers stop, up to 180 active seconds, source-only with no cache or
checker use. Review the frozen source/dependency hashes, exact statement and
proof cases, all reduction equations, complete theorem/axiom receipt, and every
falsifier above. Luna adjudicates and integrates only an accepted bounded
result. Apply it explicitly to the ordinary cases of the original parent;
leave omitted cases and every full-language/source-native/A/B parent OPEN.

Capacity at admission: eight UNKNOWN reservations remain quarantined, Luna is
primary, and one proof worker may be active; reviewer is sequential after
proof-worker/checker cessation. No lease is released by this contract. The
implementation lane is `NO_SAFE_CODE_SLICE`: no compiler or runtime change is
authorized by this proof packet.

Stop at the first source ambiguity, failed command, dependency/hash change,
budget edge, user STOP, session end, or unknown writer/runtime conflict. Preserve
all failed command evidence. The worker freezes one coherent module and handoff,
then reports actual runtime/model, checker versions/commands/exits/times,
complete theorem types and axioms, omissions, hashes, remaining parent premise,
and writes-stopped/descendant receipts. Luna owns current state, review
assignment, adjudication, integration, staging, commit and push.

## Before/after evidence

Before: no Lean one-step preservation theorem is connected to the R28 term
substitution result for these ordinary executor reductions. After success, one
checked theorem will establish exactly the listed typed redex preservation and
redex applicability, removing those cases from the original preservation proof
obligation. It will not establish the state-level simulation theorem or full
Yulang type safety.
