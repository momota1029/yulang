# Frozen Oracle source producer: bounded mechanism archaeology

Date: 2026-10-06
Status: Frozen, independently compiler-referee-reviewed (no findings); research-only historical characterization
Yulang3 baseline: `c4a4515739cf120b708d269726da2f46cdd7f97d`
Historical source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only
Implementation authority: none

## Objective, authority, and claim class

Trace the historical internal mechanism corresponding to the exact candidate
`my apply f = { my step x = f x; step }`. The result is **historical
characterization only**, conditional on the source traversing the inspected
lowering routines. It is neither a source-rule theorem for Yulang3 nor a
compatibility, soundness, principality, or source-adequacy proof.

Current meaning is fixed by user-approved call-view formation Option 2,
q1/a2, and nested-block q1/a1. Governing sources are
[inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5, and the
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. Their integrated receipts remain the acceptance records. Oracle source
and its acceptance/output supply **no Yulang3 authority**. Historical stack
operations below do not select current role, protection, or lifetime rules.

The missing current obligation is Q-independent registration of the ordinary
binder endpoint into one shared role-indexed contract/profile, with original
`beta/Slots(beta)`, typed incidences, receiver/evidence links, and one joint
`(nu,K,D)`. Under a supplied original receipt, typed receipt/rebind/capture/read
correspondences are a separate missing producer. The three assigned blocker
notes are conditional research evidence, not rules. This archaeology reduces
uncertainty about historical implementation machinery; it closes neither gap.

## Baselines and explicit hypotheses

- H1: `/tmp/yulang2-oracle-rebuild` denotes the detached historical worktree.
  Read-only `rev-parse HEAD` returned the exact historical SHA, initial status
  was empty, and all eighteen directly read source files listed below matched
  their Git blobs at that SHA byte-for-byte.
- H2: the candidate reaches ordinary parameterized-binding, local-binding,
  name-reference, and application lowering. The existing rebuild/probe note
  was only a locator; this lane did not execute the candidate, instrument its
  call stack, or infer internal invariants from its printed scheme.
- H3: analysis of code assignments and calls characterizes the state they
  create. It does not prove that the solver or compiler correctly implements
  the selected language semantics, nor that every conditional branch listed
  below executes for this exact candidate.

The initial Yulang3 status was clean. Named current dependencies matched the
Yulang3 baseline except the capture-attachment note. The primary authorized its
current digest; a narrow comparison found only review-status wording changes,
not technical-premise changes. That note remains non-authoritative evidence.

## Concrete source trace — historical characterization only

All source paths in this section are relative to the frozen historical tree;
line numbers identify that exact revision.

1. **Parser and structural representation.**
   `crates/parser/src/stmt/binding.rs:16,56,88` creates `Binding` and
   `BindingHeader` and parses the header as a pattern with `=` as a stop.
   `crates/parser/src/expr/core.rs:110` routes an opening brace through
   `parse_brace_stmt_block`; `crates/parser/src/stmt/block.rs:156` creates
   `BraceGroup`. Its machine at lines 18–105 parses ordinary statements and
   preserves semicolon/comma separators. `crates/parser/src/expr/tail.rs:273`
   creates `ApplyML` for an ML argument. The retained poly representation
   explicitly has `Var(RefId)`, `App(ExprId,ExprId)`, `Lambda(PatId,ExprId)`,
   and `Block(Vec<Stmt>,Option<ExprId>)`
   (`crates/poly/src/expr.rs:478`). The complete header-pattern expansion and
   CST dispatcher were not independently reconstructed in this budget.

2. **Definition and lexical identity.**
   `ExprLowerer` has one `locals: Vec<LocalBinding>` and shared
   `AnalysisSession`, plus function frames and a local generalization boundary
   (`crates/infer/src/lowering/expr/mod.rs:13`). A `LocalBinding` contains
   `name`, `DefId`, `TypeVar`, optional effect/scheme, and call/predicate state
   (`crates/infer/src/lowering/local.rs:6`). Pattern lowering inserts that
   state with `scheme: None`
   (`crates/infer/src/lowering/pattern.rs:263`). Defined lambda lowering
   creates fresh parameter variables, installs parameter patterns, and marks
   input/effect/call-frame information
   (`crates/infer/src/lowering/expr/lambda.rs:658,707`). It saves the preexisting
   local-stack length and later truncates to it, rather than replacing the
   outer lexical environment (`:658,865`). Consequently a nested body can
   look up the already installed outer formal while also seeing its own `x`.

3. **Inner use of outer `f`.**
   `local_binding` searches locals in reverse order
   (`crates/infer/src/lowering/name_ref.rs:215`). `lower_name_at` selects a local
   first (`:73`). `lower_local_name` obtains its value via
   `instantiate_local_value`, creates a fresh `RefId`, resolves it directly to
   that local's `DefId`, records parent/value/source span in `RefUse`, and emits
   `Expr::Var` (`:146`). A local without a scheme returns its existing
   `TypeVar` directly
   (`crates/infer/src/lowering/expr/tail.rs:855`). Thus, given H2, the unannotated
   outer formal's inner occurrence is tied to the same lexical definition and
   live value variable. This is a concrete identity/constraint link, not a
   typed receipt certificate.

4. **Application constraints at `f x`.**
   The application construction creates fresh result-value, result-effect,
   and call-effect variables; forms a `Neg::Fun` with positive argument
   value/effect ports and negative return ports; and submits
   `Pos::Var(callee.value) <: callee_upper`
   (`crates/infer/src/lowering/expr/tail.rs:543–563`). It links callee effect
   and the return-effect lower to the result effect, emits `Expr::App`, and
   returns an expansive `Computation` (`:615–627`). `make_source_app` allocates
   an `ApplicationArgument` source boundary and registers application/callee
   source spans (`:630–670`). This directly generates constraints from operands
   sharing one inference session; it does not first certify Yulang3 admission.

   A related historical mechanism is explicit: an unannotated local `Def::Arg`
   with a suitable defined-function frame can receive one fresh `SubtractId`
   indexed by its `DefId`, an `Empty` declared subtraction fact, a frame pop,
   and matching push-weighted positive/negative return-effect views
   (`:740–798`). The full frame-selection path and annotation construction
   were not traced, so this is characterization of a guarded routine, not a
   claim about the exact candidate's final stack weight. Its `Empty` and
   push/pop representation has no established correspondence to the approved
   provisional Handler seed or its discharge.

5. **Local `step` and its returned value.**
   `lower_block_items` lowers the local binding before the remaining items;
   its final-expression branch simply returns the lowered expression
   (`crates/infer/src/lowering/expr/block_local.rs:122–140`).
   `lower_local_binding_stmt` allocates a recursive placeholder, installs a
   local `DefId`, lowers the body, changes the local value to the completed
   body's value, records the body, generalizes the binding, and emits
   `Stmt::Let` (`:545–594`). `lower_local_binding_body` sends argument patterns
   to defined lambda lowering (`:866–896`). `wrap_lambda_param` constructs a
   positive Function lower bound and `Expr::Lambda`, returning
   `Computation::value`
   (`crates/infer/src/lowering/expr/lambda.rs:946–975`). Returning the final
   `step` reference therefore does not insert an application at this site.
   `lower_expr_block` restores its lexical stack after constructing the block
   (`crates/infer/src/lowering/expr/block_local.rs:69–86`).

6. **Generalization and use-time instantiation.**
   `generalize_local_binding` drains pending selection and subtype work before
   snapshotting; unresolved relevant selections can keep `scheme: None`
   (`crates/infer/src/lowering/expr/tail.rs:951–969`).
   `local_non_generic_vars` inserts other locals' value/effect variables,
   traverses their lower/upper bounds, and closes the resulting set
   (`:1014–1040`). Thus the captured outer formal is explicitly an environment
   input to generalization, rather than an unrelated per-port fresh witness.
   The routine generalizes with that set and type-level boundaries, captures
   generalized provenance witnesses, finalizes the compact root, and records
   both the definition scheme and local scheme (`:970–1011`). This identifies
   the environment-retention mechanism; it is not a proof of all pruning,
   quantification, or correlation invariants.

   A scheme contains type quantifiers, residual role predicates, recursive
   bounds, stack quantifiers, and a predicate
   (`crates/poly/src/types.rs:17`). `instantiate_local_value` collects recorded
   generalized witness paths/completeness, instantiates the scheme, and builds
   routes back to source witnesses (`crates/infer/src/lowering/expr/tail.rs:855–927`).
   The complete tail of that routine was not separately read.
   `SchemeInstantiator::instantiate_scheme_parts` freshens quantified type,
   recursive, and stack IDs before cloning the predicate and role predicates;
   `fresh_var` reuses a mapping for repeated occurrences of a source variable
   (`crates/infer/src/instantiate.rs:620–648,732–738`). This is evidence for
   coordinated instantiation, not a theorem preserving current `(nu,K,D)`.

7. **Concrete runtime capture mechanism, separately scoped.**
   In the frozen evidence VM, `RuntimeEvidenceClosure` stores parameter, body,
   `Env`, and `RuntimeEvidenceProviderEnv`
   (`crates/evidence-vm/src/runtime.rs:1152`). Evaluating a runtime lambda
   obtains provider evidence, clones the current environment, and stores both
   in the closure (`:15570–15587`); `clone_env` calls `env.clone()`
   (`:10842`). The plain tail-call path clones that stored environment, binds
   the argument, and resumes the closure body (`:16555–16564`). This is
   environment capture, rather than an inspected free-variable-minimization
   pass. The full poly-to-runtime lowering and CLI backend selection were not
   traced. These lines establish that this historical backend has a concrete
   capture mechanism, not that the recorded CLI dump executes that backend or
   that its provider environment contains Yulang3's required receipt packet.

## Correspondence table — historical characterization only

| Historical mechanism | Actual retained state/evidence | Current obligation it resembles | Critical difference or unproved bridge |
| --- | --- | --- | --- |
| Local stack, resolved `RefId -> DefId`, live formal variable | Lexical identity, name precedence, one shared endpoint; parent and source span | Resolve `u_f` to the captured outer binder | No typed receipt/rebind/capture/read map is constructed by those assignments. |
| Function frames and guarded unannotated-return routine | Per-definition/frame subtraction identity and weighted return ports | Annotation absence and protected internal call view | Historical stack recipe has no established equivalence to current role-indexed seed/discharge rules. |
| Source application boundary/provenance | Constraint origin; application/callee spans; expected-type occurrence roots | Stable source incidence and path provenance | Diagnostic/provenance identities are not proved to be original `beta/Slots(beta)` or complete semantic admission inventory. |
| Function constraint from shared operand slots | Four-port Function upper, common session bounds, connected result/effect slots | Joint source-generated callable constraints | Generated subtype constraints do not independently supply completed contract/profile, receivers, original `D`, or admission. |
| Environment-aware local generalization | Non-generic local variables and bounds, compact scheme, witness completeness | Preserve outer capture relationships through generalization | Full normalization/principality and current joint-fiber preservation remain unproved. |
| Scheme instantiator and source-witness routes | Shared freshening map, original witness path links, explicit completeness flags | Preserve correlated identity through uses | No complete original path/profile/receiver inventory was established; partial provenance is explicitly representable. |
| Evidence VM closure creation and entry | Stored lexical environment and separate provider environment | Retain outer provider across later closure calls | Exact end-to-end provider transport is omitted; no current certified receipt or activity/lifetime theorem follows. |

## Analogue checks and bounded absence

**Historical characterization only:** the inspected `LocalBinding`,
`Computation`, `Typing`, and `Scheme` definitions do not contain an explicit
original-slot/profile inventory or the current joint `(nu,K,D)` packet.
`Typing` explicitly stores definition types rather than an expression/pattern
type table (`crates/infer/src/typing.rs:1–5,112`). Conversely, application
boundaries, type-position paths, generalized provenance witnesses, and
instantiation routes are real historical evidence structures; saying Oracle
has no identities or paths would be false.

A literal search for `Slots(`, `beta`, `nu`, `Q.independent`, and capture/free-
variable patterns was restricted to non-test source under `control-ir/src`,
`mono/src`, `evidence-vm/src`, `infer/src/lowering`, and `poly/src`. No current
slot or joint-packet terminology appeared in the displayed matches. This is
not a repository-wide absence result, nor a proof that differently named
structures elsewhere cannot be analogous. Only bounded selected definitions
and data flow support the table's gaps.

Q-independent admission was **not established**. The name and application
producer is concrete and source-driven, but subtype submission is part of its
formation flow. It has not been shown to construct exhaustive semantic
membership before, and independently of, the pending comparison. One shared
mutable constraint machine and a coordinated variable map also do not by
themselves prove the current original joint valuation/kernel/incidence
correlation.

The precise stopping point is the bridge from historical resolved binder,
environment variables, and provenance routes to current original contract
registration and typed receipt/capture correspondences. No equivalent toy
transition probe was added. A new current source rule would still need its
own explicit hypotheses and proof.

## Independence, coverage, commands, and resources

There was no executable oracle in this lane. Direct frozen implementation
assignments/calls are independent of the current conditional transition
models, but source and a binary built from it share the same implementation
assumptions. Their agreement would establish neither language soundness nor
correctness of the source rules. The earlier acceptance/printer output was
not used as proof, and no self-review is claimed as independent review.

Coverage: the exact candidate's structural/local-reference route, selected
Function-constraint and scheme routines, and one separately scoped evidence-VM
closure route. No mutations, seeds, input ranges, executable probes, builds,
tests, or performance samples apply. No generated files or Git mutations.

Checks used read-only `git rev-parse HEAD`, `git status --short`, bounded
`rg --files`/`rg -n` searches, and Python source-window reads with line
locators. Eighteen source files were compared byte-for-byte against
`git show a58eefc31e22141574b6f20c6a5748151c6d79f1:<path>`; eight current
dependencies were compared against `git show c4a4515739cf120b708d269726da2f46cdd7f97d:<path>`.
The attachment note's authorized status delta was checked separately.

The primary's budget was one sequential read/search process, initially eight
frozen-source search/read commands and a 20-minute wall cap. Two further
sequential reads, each capped at 6,000 output tokens, were explicitly
authorized after broad captures truncated decisive clauses. Exactly ten
frozen-source search/read commands were consumed. Initial lightweight reads
preceded receipt of the numerical budget and included two concurrent frozen-
source locator commands; after receipt, source commands were sequential.
Three frozen-source captures and the initial combined context capture were
truncated; no complete inspection of their omitted portions is claimed.
The last two narrow reads completed without truncation. CPU, peak RSS, and
wall duration were not instrumented; this was not a resource measurement.

Failure conditions: changed source blobs invalidate the associated locators;
different CST/dispatch routes weaken H2; additional evidence-bearing structures
may invalidate a claimed local gap, which must then be narrowed; any claim of
current profile/admission equivalence needs new evidence. Unverified scope
includes complete dispatch/header lowering, all annotation/frame-selection
branches, full source-to-runtime lowering, non-plain provider-env invocation,
solver/generalization correctness, recursion, broader local polymorphism,
effects, handlers, current source acceptance, source adequacy, principality,
soundness, and production conformance.

Recommended next action: use the current resolved binder/use/capture graph to
state a candidate Q-independent original contract/profile registration rule,
with explicit source-to-typed receipt/rebind/capture/read maps; review that
rule against current authority. Historical names and stack recipes supply no
implementation permission or semantic shortcut.

## Frozen dependency hashes

SHA-256 of direct current dependencies:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-registration-constructive-derivation.md` | `b4d15fd017085f0b58836be544c576d1ce94b1f869482496d1c0507eecd24bd9` |
| `notes/progress/2026-10-06-nested-block-capture-transport-derivation.md` | `5e15ec1c99369c2d6d14f234cd02d4fc2f37ab918fa36f0ecb06ee5a74eb2f62` |
| `notes/progress/2026-10-06-capture-evidence-attachment-falsification.md` | `215d3cf8fb05f1655dea58e7e05d94bc1d64725535efe8d887b52d655e275eda` |
| `notes/progress/2026-10-06-frozen-oracle-rebuild-and-source-probes.md` | `091fb3d6d860adfd7c190ca23d4ff39324a5625e5e91fb9dbfcb75cd65f6780c` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

Historical source SHA-256; every file matched the frozen commit blob:

| Path | SHA-256 |
| --- | --- |
| `crates/parser/src/stmt/binding.rs` | `3e17d035b5009b61fe34f193ab5aac3304cc81b42c590ba7ebd4b15b0e151817` |
| `crates/parser/src/stmt/block.rs` | `c8d43f681a75605c3131abcf92501c7e809babd74a07622e23211055ed385384` |
| `crates/parser/src/expr/core.rs` | `fb2d9b660675b03dabadd6f726826e0487a39e613d8b74272f830e2fdab3243c` |
| `crates/parser/src/expr/tail.rs` | `ff3aaa7bb28ec77f0b7942f2ae6c1d435babe5cc9ec10127ca58a4df1623d52f` |
| `crates/poly/src/expr.rs` | `fbee59668b778c09cf32ad5b59c919feb36726b1af75cb630bca1ca9b7aebd88` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `crates/infer/src/typing.rs` | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |
| `crates/infer/src/lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| `crates/infer/src/lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `crates/infer/src/lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/evidence-vm/src/runtime.rs` | `eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-source-producer-archaeology.md`.
- Baseline SHA: Yulang3 `c4a4515739cf120b708d269726da2f46cdd7f97d`;
  historical Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hash: attachment note changed from
  `112d929b2f5a586d3af4085993eb84dacd1b8231a248c01814d2e7d7c164f1ef`
  to `215d3cf8fb05f1655dea58e7e05d94bc1d64725535efe8d887b52d655e275eda`;
  primary-authorized review-status synchronization only. Other named current
  dependencies matched baseline; historical direct source files matched their
  commit blobs.
- Review status: frozen, independently compiler-referee-reviewed with no
  findings; bounded historical characterization only; no current theorem
  closure or implementation authority.
- Checks already run: revision/status reads; ten bounded frozen-source reads/
  searches; source/blob equality and SHA-256 checks; current dependency/blob
  comparisons and narrow authorized status-delta inspection; lease/path and
  artifact whitespace inspection. No executable, Cargo, test, or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: trace frozen Oracle binding and capture producer mechanisms`.
- Shared-record deltas intentionally left for primary/curator: record historical
  binder/endpoint sharing, environment-aware generalization, provenance routes,
  and separately scoped runtime capture as mechanism evidence; retain original
  contract/profile registration, typed receipt/rebind/capture/read production,
  admission, joint correlation, soundness, principality, adequacy, and production
  conformance as open. Do not promote Oracle semantics to authority.
