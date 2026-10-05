# Block result and nested-binding capture: source/legacy correspondence

Date: 2026-10-06
Status: frozen research characterization and conditional derivation; independently reviewed with one minor attribution repair; no implementation authority
Baseline: `62429dd53dd667e1808ac98b52b020d8a50ffea6`
Legacy reference: `a58eefc31e22141574b6f20c6a5748151c6d79f1` (`a58eefc3`)
Exclusive lease: this file only
Method: bounded static authority and frozen-source correspondence search

## Objective and result

Determine whether an already approved rule establishes H_binding/H_scope/H_block
for the existing candidate:

```text
my apply f = { my step x = f x; step }
```

**Bounded characterization:** the retained legacy meaning is materially better
specified than the prior encoding audit established. Frozen public references
explicitly describe final-expression block values and curried declarations;
a recorded Oracle witness returns a local function with an outer capture.
Frozen lowering independently corroborates sequential local binding and
final-expression result transport. These are useful existing-behavior evidence,
not a newly executed exact-candidate test or adopted current raw-source rule.

**Authority boundary:** no examined in-scope Authoritative current document
supplies the complete raw braced-block/local-function/capture translation that
would make this candidate a proved curried equivalent. This is a missing
source-to-core correspondence premise; it does not establish that the intended
legacy language meaning is unknown or that a new language choice is required.
A blanket claim that block-result/capture has no existing evidence would be
incorrect. Whether existing-behavior evidence suffices under the primary's
confirmed compatibility envelope remains an authority adjudication for the
primary, with the concrete evidence below.

H_call/H_registration remains a separate open gate. None of this evidence
supplies its protected provisional view, ordinary-value discharge judgment,
typed incidence, or one correlated original `nu,K,D`.

## Governing authority and exact locators

1. `notes/design/2026-10-05-inferred-function-call-views.md` §§3 and 5
   (116–134, 153–186) fixes the approved unannotated `apply f x = f x`
   direction and leaves exact source judgments and preservation proofs open.
   Section 2 (98–114) requires scope/capture/typed-path source evidence before
   comparison. Section 1.1 (67–82) separates internal provisional views from
   written types and actual callable roles. No equivalence rule for nested
   local declarations or braces is stated.
2. `syntax-reference/en/src/expressions/braced-statement-block.md` §1
   (5–10) excludes HIR interpretation and types; §2 defines only the sequence.
   The underlying syntax architecture's “`{x: 1}` and semantic interpretation
   boundary” (6415–6432), particularly 6430–6432, assigns interpreting a brace
   sequence as a block value or another construct to future HIR/inference
   design. “Scope and non-unification boundary” (6145–6188) also distinguishes
   expression braces from historical declaration/control owners.
3. `syntax-reference/en/src/statements/binding-use.md` “Non-goals”
   (190–195) explicitly excludes body result, recursive scope and lowering.
   Placement at root and nested statement owners (15–18) is grammatical.
4. Authoritative F5 foundation §§3–4 and 21 (65–100, 483–523) gives one-formal
   Lambda HIR, value construction and parameter-local lookup. Its contract is
   scoped to that production subset; it supplies no arbitrary local block
   lowering/capture/extrusion theorem. The redesign charter §§1–2 (24–48)
   treats F5 scheme machinery as legacy and selects frozen Oracle final
   well-typed-program capability as compatibility evidence, not mechanically
   copied implementation semantics.
5. Authoritative result-synthesis choice §4 (143–159) gives
   `Result(Value(A)) = Comp(empty,A)` and
   `Result(Computation(E,A)) = Comp(E,A)`. It preserves an already known body
   interface. It does not select a brace's final statement as that body.
6. Typed computation core §§2–3 and 6 (70–106, 117–135, 396–410) supplies a
   *Draft, derivation-indexed candidate*: lexical-reference closures and
   `my x = r; b` mapped to `bind(x,n_r,n_b)`. Its §6 coherence theorem
   (442–459) is relative to known lexical/declaration interfaces. The source
   mapping at issue cannot be proved by assuming that candidate table.
7. `notes/design/2026-10-04-common-allowance-context-preimage.md`
   “Source examples covered” (115–129) explicitly labels its curried and
   braced examples as source-core proof notation; they establish no current
   raw HIR implementation or new brace/capture authority.

The prior reviewed encoding audit's syntax composition and production boundary
are inputs, not repeated investigations. Its root/local binding and block
premises are refined here; its H_call/H_registration claims are left intact.

## Frozen legacy evidence, with provenance limits

At `a58eefc3`:

- `web/docs/reference/control-flow.md:176–189` shows a braced block with a local
  binding and final expression and states ordered evaluation with the final
  expression returned.
- `web/docs/reference/syntax-style.md:186–208` gives brace and indentation
  examples, final-expression block values, and curried header arguments.
- `web/docs/reference/functions.md:14–32` describes binding arguments and
  left-to-right currying. These public references express legacy meaning;
  they contain no current approval header selecting a new block bridge.
- `crates/infer/src/lowering/expr/block_local.rs:69–86` enters a local block
  scope and truncates lowering locals after the result is built.
  `122–140` lowers an ordinary local binding before its tail, and returns a
  final expression directly. `545–590` allocates a local definition and
  generalizes its body. `866–896` sends parameterized local declarations to
  the defined-lambda lowering route.
  `1284–1306` transports `tail.value` to the block value and retains
  `Expr::Block(..., Some(tail.expr))`. This supports the *static lowering*
  correspondence; it does not prove runtime lifetime or capture semantics.
- `crates/infer/src/lowering/expr/lambda.rs:271–282,310–368` recursively lowers
  parameter stages, restores scopes, and emits a Lambda value. This is a
  legacy implementation fact, with its own inference/role assumptions.

At the research baseline,
`notes/progress/2026-09-29-intrusion-oracle-ledger.md:36` records the accepted
source `my outer x = my inner y = ({left: x, right: x}, y); inner`, its two
curried schemes, and exact shared outer TypeVar retained outside the local
quantifiers. This is a nearby nested-return/capture witness, not the exact
braced `apply` candidate. The temporary probe was removed and was not rerun;
this audit relies on the retained report. Line 37 separately records a failed
local forward-reference witness, so this evidence must not be expanded to
arbitrary recursive local groups. Lines 57–58 limit the capture result to the
exact programs inspected.

Frozen `spec/README.md:3–6,39–41` distinguishes specification from executable
Oracle and excludes lowering/runtime semantics from the historical syntax
spec. It supplies no blanket route for promoting legacy implementation into
current source authority.

## Conditional derivation and exact untouched premise

Let `B` be the candidate brace body, `df` and `dx` its formal occurrences,
and `c` the retained `f x` call. Assume:

- **L:** the raw candidate maps to a lexical derivation in which `f` resolves
  to `df`, `x` to `dx`, and final `step` to the local definition. The local
  one-formal declaration introduces a closure with body `c`; the braces
  execute its binding and select final `step` as their returned expression.
- **C:** closure construction is inert, preserves the same enclosing lexical
  references and typed evidence after leaving the block, and local lookup
  returns that closure without an extra consumer or observable allocation
  distinction. This assumption includes capture preservation; a token range
  or a static TypeVar identity alone does not establish it.
- **R:** the already selected parameter/result roles are retained, with local
  binding represented by the Draft core's `bind` rule, and the core's
  `Return`/environment-extension composition laws apply to this derivation.

Write `F = lambda(dx, n_c)`, with references to `df`. Under L/C/R:

```text
n_B = bind(step, result(F), result(name step))
X[n_B] = Return(Closure(dx, X[n_c], lexical_refs_df))
           >>= (v => Return(lookup(step, env[step := v])))
        = Return(Closure(dx, X[n_c], lexical_refs_df))
```

The outer definition therefore returns the same retained inner closure as
`lambda(df, result(lambda(dx,n_c)))`, subject to the stated observation law.
The `f x` call remains inside the inner body and is not executed by constructing
or returning `step`. This is a conditional derivation in the stated core,
not an effectful raw-source contextual-equivalence theorem, typing/principality
result, or current production registration certificate.

Legacy references and lowering support L as an intended correspondence;
the recorded capture witness supports the static capture-identity part of C
for one nearby witness, not its operational reference/evidence lifetime or
consumer/allocation clauses. Neither proves L/C for the exact candidate in the
current source system. R uses selected role
premises but a Draft binding construction. The smallest missing bridge is
therefore the explicit source realization of this two-statement brace with one
local function and final Name, preserving the enclosing binder/evidence on
return. It does not require solving empty blocks, records, control bodies,
forward references, mutation, State, handlers or arbitrary local recursion.
Those are omitted rather than silently generalized.

Even after this bridge is established, identifying the returned closure's
formal/use contract with approved `apply f x = f x` needs H_call/H_registration,
including scoped generalization and unchanged annotation absence. This audit
neither changes actual roles nor infers Pure from Value entry or empty effects.

## Independence, coverage, checks and resources

No new Oracle, parser, compiler, checker, build, test, probe or semantic
experiment ran. Documentation and owning lowering are different retained
artifacts from the same legacy implementation lineage; they are corroboration,
not two independent operational oracles. The ledger is reported historical
execution evidence, not independently reproduced here. The conditional core
calculation assumes L/C/R and therefore does not prove the source rules it
requires. No seeds, numerical ranges, enumeration, mutants or performance
samples apply.

Search envelope: pinned task/index locators, supplied encoding audit, current
call-view/syntax/F5/result/core/charter documents, current source-core example
record, retained Oracle ledger, and six frozen legacy reference/source files.
A broad pinned Markdown keyword search located the decisive source sections.
Early output from invocations 2, 3, 4 and 8 was truncated; subsequent narrow
reads recovered the cited decisive passages. This is not an exhaustive search
of all historical specs, all runtime paths, external sources or question-board
bundles. No pending question answer was consumed as authority. No network ran.

Budget consumed: exactly 12 sequential lightweight top-level `exec_command`
invocations, including final lease write/dependency recheck. All returned
command wall-time reports were at most 0.1 s; complete session wall time, peak
RSS and aggregate CPU were not instrumented and are unknown. Python and
read-only Git subprocesses ran sequentially; no heavyweight process, child
agent or Git mutation ran. Unrelated shared edits were preserved. Dependency
bytes below were rechecked against the pinned revision before freezing; no
baseline dependency changed. The lease write/readback and hash inventory are
artifact checks, not compiler verification or independent review.

Failure conditions: changed direct dependencies, discovery of an already
approved exact raw-block/capture rule, or evidence that this source maps to a
different callable/result/capture structure. Any such evidence requires a
narrow delta audit. A parser-only success or another checker assuming L/C would
leave the main premise untouched.

Recommended next action: the primary should adjudicate this narrow existing
behavior against its accepted compatibility envelope and obtain/record the
exact current raw-block-to-lexical-core realization premise. Then pass that
fixed mapping to the separate H_call/H_registration lane; no equivalent toy
probe or general language redesign is recommended.

## Frozen dependency inventory

All current direct semantic inputs below match their baseline bytes. Frozen
legacy files are read only at the named Oracle revision. Shared task/index
files were navigation inputs read from the pinned revision, not live authority.

| Revision | Path | SHA-256 |
|---|---|---|
| `62429dd5` | `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `62429dd5` | `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `62429dd5` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `62429dd5` | `syntax-reference/en/src/expressions/braced-statement-block.md` | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| `62429dd5` | `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `62429dd5` | `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `62429dd5` | `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `62429dd5` | `notes/design/2026-10-04-common-allowance-context-preimage.md` | `e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e` |
| `62429dd5` | `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `62429dd5` | `notes/progress/2026-09-29-intrusion-oracle-ledger.md` | `b603335b97537931396c56cd2537fa7a83df3ce8f73cc9738de5920c641c8b60` |
| `62429dd5` | `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `a58eefc3` | `web/docs/reference/functions.md` | `b2a616ea603dccaa431bfcea0c4c2e6eff54b5e058ff9fb6370cb2eb081fa611` |
| `a58eefc3` | `web/docs/reference/control-flow.md` | `cce270b697f4a8ce3a711a6daec107405dbf93d192187e555138204813d84da1` |
| `a58eefc3` | `web/docs/reference/syntax-style.md` | `d14da22ae583771387f41320126c5d2be0fe20a33df8d78a8113243cd2c3d229` |
| `a58eefc3` | `spec/README.md` | `410793d67dc045969115caa4c8a4ca457f131c0eba4f19936d7ad66b9e150362` |
| `a58eefc3` | `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `a58eefc3` | `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` only.
- Baseline SHA: `62429dd53dd667e1808ac98b52b020d8a50ffea6`.
- Legacy dependency revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; exact inventories above. This audit recalculates SHA-256 rather than copying the prior note's foundation digest.
- Claim/review status: bounded static characterization and conditional core derivation; frozen, unreviewed research checkpoint. Producer reread is not independent review; no gate closure.
- Checks already run: pinned-source locator reads, baseline/live dependency equality, SHA-256 inventory, exclusive-lease existence guard and exact note readback. No compiler/test/build/probe/Git mutations.
- Proposed one-line commit message: `research: trace block-result and nested-capture legacy correspondence`.
- Shared-record deltas intentionally left for primary/curator: strengthen existing-behavior evidence with frozen final-expression/currying references and the retained local captured-diamond witness; replace any blanket absence claim with the narrow current raw-block/capture realization premise; keep H_call/H_registration separate and open. No shared task/index/theory/authority or question-board files changed.
