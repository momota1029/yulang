# Simple-sub type-error continuation and rejection boundary

Date: 2026-10-11
Status: frozen, unreviewed, non-authoritative static source characterization.
Baseline: `d82c7b4220d1e158ac1e9d3c16dc1de948c61341`.
Oracle source baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, at
`/tmp/yulang2-oracle-read` (detached HEAD inspected as a plain file).
Lease: this note only. No compiler/test edit, execution experiment, build,
Oracle rerun, delegation, or Git mutation.

## Objective, authority, and claim class

Trace one syntactic function binding through actual source constructors,
constraints, conflict settlement, and result consumers. The primary's updated
user decision controls: continue inference and diagnostics on abnormal or
ill-typed input where possible; report appropriate errors; exact diagnostic
matching and complete internal rollback are not general requirements. Do not
accept incorrect typings or publish inconsistent results. Unrecoverable
resource failures may safely abort. Deterministic inference must not retry an
ill-typed program to manufacture a typing.

Governing sections: `rules/design-authority.md`, “Authority order” and “Active
withdrawal of Simple-sub bypasses”; the withdrawal design's “Selected policy”
and “Mechanism-by-mechanism completion evidence”; F5 foundation
`2026-09-21-f5-general-function-scheme-foundation-draft.md` §§38–40 for its actual
diagnostic owner; `2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` §10 for
availability versus semantic errors. The later user-selected
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
supersede the private suspension contract's §§6–7 requirements for blanket
failure restoration and supported retry. Its successful suspension, retained
continuation, invalidation, and no-inconsistent-publication obligations remain.
This audit characterizes the current source path; it does not propose a
replacement recovery architecture. No callback result, expansive annotated
value, or pending question bundle is used as authority.

This is a bounded source derivation, conditional on normal successful
construction/accounting and completion of the inspected source schedule. It
is not an executed source counterexample, independently reviewed theorem,
whole-language rejection theorem, or production conformance result.

## One source case and Oracle qualification

```text
my bridge x = 1 1
```

The binding is syntactically a function with one parameter. Its invalidity is
inside the body: an integer is applied as a function. This avoids value
restriction and annotation polarity entirely. The smallest contradictory
subexpression is `1 1`; the `bridge x` wrapper retains the requested function
binding. Minimality is syntactic for this witness, not a global search result.

“Oracle-valid” here means grammar and lowering supported, **not** well typed
or observed acceptance. Static Oracle evidence is independent source code:

- Parser `stmt/binding.rs` parses a binding header Pattern then its expression
  body. `parser/tests/stmt_grammar.rs:2378` retains `my f x = 1` as a Pattern
  with an `ApplyML` parameter. `infer/src/lowering/expr_syntax.rs:402–439`
  extracts that actual parameter; `lowering/body/mod.rs:2207–2234` dispatches
  to function-body lowering when arguments exist.
- `lowering/expr/chain.rs:551` and `:584` dispatch integer syntax to
  `block_local.rs:1309` `lower_number`, which creates a pure computation with
  an exact primitive lower and upper. There is no requirement that an integer
  be named before applying it.
- `lowering/expr/tail.rs:15` dispatches `ApplyML` to `apply_arguments` at `:89`;
  `make_app_with_origins` at `:535` allocates a negative Function and emits
  `Var(callee.value) <: Function(argument, argument_effect, return_effect,
  result_value)`.
- `constraints/machine/propagate.rs:119–150` installs that Function upper on
  the callee variable. Its concrete-head check at `:194–210` emits
  `UnsatisfiedSubtypeShape` for Constructor(int) versus Function.
  `analysis/session/lifecycle.rs:510` routes the event;
  `subtype_diagnostic.rs:17` retains a deduplicated source-projected mismatch;
  `lowering/body/mod.rs:1680–1684` transfers analysis diagnostics into
  `BodyLoweringError::Analysis`.

Thus the actual Oracle source owners generate and diagnose the fixed-head
contradiction. No Oracle command was rerun; exact rendered diagnostic, exit
status, generalized output, and CLI publication disposition are unverified.
Existing Oracle tests were inspected as source contracts, not executed.

## Yulang3 source-to-conflict chain

The inspected candidate route uses opt-in
`yu_hir::shadow::lower_module_with_local_source`, not ordinary lowering.
`module/local_source.rs:295–325` forms the Lambda from the actual parameter;
`:477–559` forms the source Apply and both operand identities;
`:663` forms integer nodes. The candidate constructor deliberately tolerates
the ordinary HIR placeholder `UnsupportedExpression` only when that error is
covered by its retained supported source (`shadow_apply.rs:82–107`).

Let C be the callee integer's Value row, A the argument integer's Value row,
R the application's result row, and F its fresh negative Function demand.

1. `candidate_source.rs:333–350` emits `Int+ <: C <: Int-` and
   `Int+ <: A <: Int-`, with bottom/empty literal computation effects.
2. Its Apply branch at `:374` retains the recipe, source operand indices,
   checking occurrence/cause, and an `Action::Candidate`.
3. `shadow_apply.rs:1300` `admit_candidate_fact` validates that association;
   `:1345–1378` builds F with the actual argument and result/effect endpoints;
   `:1382–1405` admits and drains `C <: F` at that Apply occurrence/cause.
4. `candidate_extrusion.rs:808` `candidate_apply_value` stores the selected
   upper and calls `candidate_replay_bound`. The already retained `Int+` lower
   produces the terminal comparison `Int+ <: F`.
5. `lib.rs:12376` `dispatch_live_item` records a direct
   `IncompatibleValue { lower: Int, upper: Function }` witness and returns
   `Ok(())`. This stops decomposition of that impossible pair, not the
   inference attempt. `complete_diagnostic_delta` at `:13099` settles the
   newly admitted diagnostic graph; `replay_witness` at `:13721` reports its
   root witness at the original occurrence/cause.
6. `report_solver_kind` at `:14085` reserves, deduplicates, and appends
   `SolverError`, then returns `Ok(())`. `constrain_live_item` completes the
   drain, clears temporary diagnostic scratch, and returns normal transitions
   (`:12088–12110`). The persistent errors remain.

The decisive constraint is impossible under the inspected concrete shapes:
`incompatible_value_shapes` at `lib.rs:14047` explicitly rejects Int versus
Function. No alternative traversal, new fresh use, or resumed generation can
make this same fixed-head obligation satisfiable. This audit does not assert
the entire scheduler's determinism or prove that every generated conflict is
retained across every lifecycle invalidation.

## Result consumers: accumulation exists; source rejection is absent

| Owner | Actual disposition |
|---|---|
| Shared typed diagnostic core | Records a witness and continues; semantic conflict is not an availability error. |
| Candidate SCC plan (`candidate_scheme.rs:842–914`) | Executes member actions, captures graphs, then makes the staged graphs visible together. This inspected path has no `self.errors` guard. |
| `run_candidate` / `finish_candidate` (`lib.rs:10361–10376`) | Executes once, finishes observations, and returns `Ok(CandidateSolvedResult)` when availability succeeds; no empty-error condition. |
| `finish_observations` (`lib.rs:17523` onward) | Transfers accumulated errors and candidate graphs into the frozen result. |
| `CandidateInference::candidate_conflicts` (`shadow_apply.rs:116`) | Returns those errors; its explicit contract says candidate conflicts never establish source rejection. |
| `CandidateInference::export` (`shadow_apply.rs:123–141`) | Checks artifact/root/graph identity, not conflict absence, and exposes a borrowed private graph. |

Consequently the private conflict is **observable and nonterminal**, and is
**not connected to a source-rejection consumer** in this chain. Continued
diagnostics agree with the user's new decision. Returning a private research
result with errors is not evidence that the compiler accepts a valid typing.
These graph APIs explicitly leave source admission and public scheme
correspondence unresolved and cannot publish a `SolvedModule`. Nevertheless,
their internal staged graph visibility and export require an actual validity
boundary before a successor public typed-result consumer can rely on them.
The present accumulation behavior alone does not establish safe rejection or
safe usable output for ill-typed source.

## Existing F5 boundary for the same source

Ordinary `lower_module` has no LocalSource carrier. The source body's Apply is
outside `lower_simple_chain`'s ordinary admitted envelope:
`module.rs:1682–1697` emits `HirErrorKind::UnsupportedExpression` and a
`ResolvedExpr::Error`, wrapped in the admitted outer Lambda at `:1473`.
Feature-gated shadow application retention still emits that placeholder
(`:1961`) and ordinary collection classifies a Lambda with Error or Apply body
as `CollectedBodyStatus::Error` (`yu-solver/lib.rs:1047–1075`).

Thus ordinary F5 does not generate this candidate Function demand and does
not reach the Int/Function mismatch for this source. Its actual semantic
diagnostic machinery is the same typed pair/witness settlement owner above,
but that machinery cannot establish source parity when the upstream
application constructor is absent. `SolvedModule::solve` at `:17601` runs the
ordinary session; `finish` at `:17267` owns genuine closed finalization and
retains its `errors()`, while `hir()` separately retains HIR diagnostics.
Completion and an empty solver-error slice alone therefore do not certify this
source was admitted: Unsupported HIR must still be consumed by a caller.
No complete application type-error or CLI rejection parity is claimed.

`SolveAvailabilityError` is separately
`ArtifactMismatch | CauseMismatch | ReceiptMismatch | IdentityExhausted`
(`lib.rs:3947`). It is not the semantic mismatch above. Likewise the suspension
contract §2 forbids treating private `Suspended` as availability failure,
source rejection, a language diagnostic, or completed `Ok`. These are three
different owner boundaries, not interchangeable error spellings.

## Coverage, dependencies, and next action

Static inspection only: `rg`, bounded `sed`/`cat` reads and `sha256sum`;
initial read-only `git status --short` / `git rev-parse HEAD` identified a clean
baseline. No Git mutation occurred. Zero tests, builds, Oracle reruns, searches
over seeds/ranges, mutations, heavy processes, or measurements. Shell captures
were bounded; some early broad multi-file captures truncated and decisive
source sections were subsequently inspected narrowly. Resource peaks and
exact total wall time were not measured; no runtime success is claimed.

The Oracle constructors are independent of the candidate checker and shared
diagnostic kernel. Both source derivations use the same ordinary integer and
application meaning and assume successful normal construction. They do not
prove complete Call, global source rejection, effect hygiene, principality,
soundness, all rollback/replay paths, continuation fairness, recovery on an
arbitrary malformed program, external caller handling, or public cutover.

Next action: the primary assigns the successor source/result consumer owner a
bounded validity/publication packet: retain and report conflicts while
continuing safe work, and prevent the affected inconsistent graph from being
consumed as an accepted public typing. Keep ordinary HIR adoption and F5
replacement explicit; no immediate fail-on-first-conflict or general exact
rollback premise follows from this audit.

Frozen dependency SHA-256 values:

```text
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a  notes/design/2026-10-10-simple-sub-legacy-withdrawal.md
3e17d035b5009b61fe34f193ab5aac3304cc81b42c590ba7ebd4b15b0e151817  Oracle crates/parser/src/stmt/binding.rs
ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8  Oracle crates/infer/src/lowering/expr/tail.rs
8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086  Oracle crates/infer/src/constraints/machine/propagate.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-simple-sub-type-error-rejection-audit.md`.
- Baseline SHA: `d82c7b4220d1e158ac1e9d3c16dc1de948c61341`; Oracle dependency
  SHA: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency changes authored: none. Primary must revalidate the frozen source
  hashes before integration if concurrent compiler work changes them.
- Review status: unreviewed research characterization; no self-certification,
  source acceptance claim, theorem closure, or production authorization.
- Checks already run: static owner/consumer trace and dependency hash capture;
  no test, build, executable probe, or Oracle command.
- Proposed checkpoint message: `research: trace type-conflict continuation and source rejection boundary`.
- Shared-record deltas intentionally left to primary/curator: record that
  private conflicts accumulate and remain observable in completed research
  results; public valid-result consumption and ordinary Apply adoption remain
  separate open owners. Preserve the revised user error decision and the
  independent private suspension contract without implying global rollback or
  fail-on-first-conflict requirements.
