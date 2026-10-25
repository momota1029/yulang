# Sprint PAPER-CORE-STEP-PRESERVATION-20261026/r35 — revision 3

Status: READY after primary lease/hash acknowledgement; fresh worker receipt required before RUNNING.
Branch: `research/simple-sub-intrusion`
Baseline: `8c1fa2d3a` (R35/r2 failed candidate and evidence frozen)
Revision: r3 of the same R35 goal; one local proof repair, with no theorem or source-scope change.

## Original parent and unchanged outcome

The original parent is the manuscript's precise one-step preservation and
display simulation theorem, `docs/yulang-operational-type-safety-ja.tex:1860–1875`.
This packet advances its ordinary core reduction cases without narrowing or
replacing that parent. The governing reduction clauses are `:301–316`; the
execution typing clauses are `:203–240`.

Create standalone module `YulangClosure.PaperCoreStep` defining a partial raw
computation step for exactly these manuscript cases:

- `letE (ret v) body` by R28 capture-avoiding single term substitution;
- `force (delay body)`;
- either injection selected by `unionCase`;
- `unroll (roll v)`;
- `field` on a record with the requested label;
- optional/required `lookup` on a record, returning right injection when the
  label is present and left unit injection when absent.

The main theorem retains the unchanged contexts and result type:

```text
PaperComputationTyped D Xi Γ c A → step c = some c' →
  PaperComputationTyped D Xi Γ c' A
```

Also prove every typed redex in the enumerated cases returns `some`.
Constructor mismatches and unlisted reductions may return `none`; this partial
operator does not interpret `none` as termination, `Fail`, or `Bad`. Do not
claim complete operational semantics, full progress/preservation, the global
inference-soundness root, or closure of the manuscript parent.

## Method, discriminators and source limits

Use inversion of the actual `PaperComputationTyped`/`PaperValueTyped` derivation,
R28 `TermSubstitutionTyped` and term-substitution results, and concrete record
lookup reasoning. Preserve one shared environment and exact result type `A`.
`let` and union-case substitutions must shift variables above the bound variable
and avoid capture. Record lookup uses runtime label presence; it must not
confuse the stored `Presence` tag with declaration requiredness. Required
`field` uses typing evidence and typed-record required-field coverage. Optional
absence has the declared result union type.

Falsifiers: captured binder; wrong union branch; accepting a missing required
field; wrong type on optional absence; using raw field `Presence` to choose the
lookup branch; unroll result not equal to the typing constructor's unfolding;
weakened contexts/result indices; failed `some` for a typed listed redex;
unsupported axioms or proof holes.

Source correspondence: manuscript reductions `:305–316`, static rules
`:203–240`, parent theorem `:1860–1875`. The Lean relation is partial. This
module does not cover omitted source/native constructors, complete heap graph
typing, handlers, effects, primitive semantics, recursive allocation or
`wrap`.

## R2 failure and authorized repair

R35/r2 is frozen at commit `8c1fa2d3a`: its source, full first-failure log, and
handoff are immutable. Source SHA-256
`4b9afa131058a5bc585624d9851f251f27aa518530f90767a66bef77e9fd4b0d`;
handoff SHA-256
`93feb1df648d0645b4d641442f42af2260e475af007ed291305a8ec2258fd3d5`;
log SHA-256
`505abde97919b8288b88f7099e2a7c298d387cbf98d1e05c3fa0c2f47ae61fac`.
The first module build failed at `field_required_mem`, where `subst presence`
targeted an outer binder instead of the induction branch's `presence✝`; the
branch carries `he : presence✝ = Presence.required`. This was an elaboration
failure, not a counterexample.

The only authorized source repair is to replace `subst presence` in that `here`
branch with `cases he`, then simplify the resulting branch. This is a proposed
repair, not an already checked result. Do not alter
other definitions, theorem statements, hypotheses, contexts, result indices,
source cases, or dependencies. Continue the same preservation, applicability,
and complete theorem/axiom audit obligations. The first failed r3 Lake/Lean/checker
command stops r3; preserve the full output and do not repair or retry again.

R2 consumed 4/10 worker invocations and a conservative 34.103963267/120 checker
seconds. The remaining worker grant is at most 6 invocations and
85.896036733 checker seconds. No budget resets.

## Frozen inputs

- Manuscript: `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperExecutionSyntax.lean`, SHA-256
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`, SHA-256
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- Accepted R28 `PaperTermSubstitution.lean`, SHA-256
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- Lean pin: `leanprover/lean4:v4.35.0`; `lakefile.toml` SHA-256
  `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.

All r1 handoff/log paths remain immutable evidence: R35/r1 stopped on a
read-only absent-`.olean` lookup before construction, with 0 Lake/checker calls,
0 checker seconds, no source/cache writes, and no mathematical result. Its
failure did not change these dependencies or theorem scope. R26, wrap authority,
and native immutable-graph work remain outside this packet.

## Exact lanes, command order, leases and budgets

One fresh registered `lean_prover` owns the proof/cache lane in
`notes/theory/lean`; no other worker owns or changes this cache or frozen input.
The failed r1 and r2 output paths remain frozen. R3 uses separate receipts and one
handoff:

- `notes/theory/lean/YulangClosure/PaperCoreStep.lean`
- `notes/theory/lean/.lake/R35Audit.lean`
- `notes/theory/lean/.lake/build` (worker sole owner until writes stop; then
  primary takes over)
- `tasks/agent-loop/inbox/paper-core-step-r35-r3-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-core-step-r35-r3.md`
- `tasks/agent-loop/inbox/paper-core-step-r35-r3-primary-verification.txt`
- `tasks/agent-loop/inbox/paper-core-step-r35-r3-review.md` (fresh reviewer,
  only after proof/checker/cache writers stop)

All frozen dependencies are read-only. No changes to existing Lean modules,
`YulangClosure.lean`, `lakefile.toml`, Rust, tests, expected outputs, fixtures,
diagnostics or question files. No descendants or Git operations.

Before any checker work, the fresh worker receipt and primary lease
acknowledgement must bind the exact source/dependency hashes. Confirm the pinned
dependency hashes and r2 version/build receipts. The dependency build already
passed under the unchanged pin and its cache is transferred from the stopped r2
owner. From `notes/theory/lean`, resolve the native Lake path read-only with
`elan which lake`, then apply the single authorized source repair. The first
native checker command is `lake build +YulangClosure.PaperCoreStep`; if it passes,
run `lake env lean -j1 -M1024 .lake/R35Audit.lean` for complete theorem type and
axiom output. Both commands count against the remaining r3 budget. If a dependency
output is absent or any frozen hash differs, stop and return the issue to Luna;
do not install, update or rebuild unrelated targets. Use no Lake `-j1` flag;
existing lakefile arguments bound Lean processes. The first failed Lake/Lean/checker
command stops the packet; retain the complete diagnostic and do not retry or
repair again. Do not run full default build/tests/Rust/network/package operations.

Worker allowance remaining from r2: at most 6 serial native Lake/Lean/checker
invocations and 85.896036733 checker seconds. Primary allowance after worker
STOPPED: at most 4 serial invocations and 60 checker seconds. One heavy build at
a time. The original R35 envelope is **not reset**: total remains 14 invocations,
180 checker seconds and 1800 active seconds, less actual prior usage. R1 used 0
checker calls/seconds; r2 used 4 invocations and 34.103963267 checker seconds.
At least 760 aggregate active seconds are conservatively charged at r3
admission; at most 1040 seconds remain. Preserve and charge all further primary/worker
elapsed time; do not extend or reset the envelope. If remaining aggregate time
cannot be established, stop.

Only after all proof/checker/cache activity stops may one fresh non-author
`spec_auditor` perform source-only review for at most 180 active seconds, with
no cache/checker use. Luna owns adjudication and integration. Apply an accepted
bounded result to the enumerated ordinary cases of the original preservation
parent; all omitted cases and full-language/source-native/A/B/production gates
remain OPEN.

Capacity: eight UNKNOWN reservations stay quarantined. One proof worker runs
under the unchanged R35 capacity envelope; a reviewer is sequential after all
proof/cache writers stop. No lease is released by this amendment.
Implementation lane remains `NO_SAFE_CODE_SLICE`.

Stop on source ambiguity, failed Lake/Lean/checker command, dependency/hash
change, budget edge, runtime/lease conflict, user STOP or session end. Preserve
all failure evidence. Handoff reports exact source/dependency/artifact hashes,
actual tool versions and command times/exits, theorem types and complete axioms,
omitted cases, parent application/first premise, runtime model/effort (UNKNOWN
when unavailable), and writes-stopped/no-descendant receipts.

## Before/after evidence

Before: no one-step type-preservation result applies R28 substitution to these
ordinary executor reductions. After success, one checked theorem will establish
listed redex preservation and applicability, removing only those cases from
the original preservation proof obligation. It will not prove state-level
simulation or full Yulang type safety.
