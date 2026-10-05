# Nested block source-to-core construction: first missing rule

Date: 2026-10-06
Status: frozen partial constructive derivation; unreviewed research only; no implementation authority
Baseline: `503ae9d21fc7b0e4a1062cd101804fb13183273c`
Legacy evidence revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only
Method: construct the raw-owner-to-lexical-core derivation from governing rules; stop at its first unsupported edge

## Objective and boundary

Attempt H_binding/H_scope/H_block and static capture correspondence for:

```text
my apply f = { my step x = f x; step }
```

The primary fixes this as an existing-grammar candidate for an illustrative
approved shape, without grammar or actual-role changes. The reviewed encoding
and legacy audits are inputs. This note tightens their L/C/R premises by locating
the earliest missing inference rule; it does not repeat their conditional
`bind`/`Return` reduction.

**Result: bounded partial derivation.** Approved rules determine the outer
one-formal binding, parameter role, and forwarding of an already established
body interface. They do not supply a judgment interpreting this raw brace
owner as a lexical local-function binding followed by its result lookup.
Construction stops at that owner edge. H_call/H_registration and operational
capture lifetime are later obligations and are not premises discharged here.

## Exact governing sections and their scope

| Source | Status and applicable rule | Boundary |
|---|---|---|
| Syntax architecture, “canonical Statement binding / use declaration extension,” lines 11090–11140 | Scoped Authoritative addendum; shared nested Statement binding and inline OperatorChain body | Grammar/CST composition; the architecture's historical Proposal header does not promote all its prose |
| F5 foundation §§3–4, 20–21, 41; lines 58–101, 425–480, 483–523, 1420–1440 | Authoritative one recovery-free identifier formal; parameter identity, Lambda occurrence, local-first parameter lookup; approved shared Pattern application admission | §1 lines 32–34 excludes expression-application typing, multiple semantic parameters, roles and Core IR; §21 preserves root/parameter/Lambda on an unsupported body |
| Braced statement syntax §§1–4, lines 5–50; Binding/use “Non-goals,” lines 190–195 | Accepted sequence/CST with direct Statement children and a semicolon separator | Explicitly excludes HIR interpretation, body result, recursive scope and lowering |
| Syntax architecture, “semantic interpretation boundary,” lines 6415–6432 | Defines the CST interpretation boundary | Lines 6430–6432 assign block-value interpretation to future HIR/inference design |
| Redesign charter §21, lines 572–601 | Recorded user decision: unannotated ordinary parameter has `Value(A)` and same-activation entry rebind | The charter header is Reviewed; this exact selected amendment supplies source authority, not production approval |
| Result-synthesis choice §4, lines 143–160 | Authoritative A: name copies known interface; Lambda forwards `Result(I_body)` | Does not identify the final brace statement as the body interface |
| Typed computation core §§2–3, 6; lines 70–107, 117–135, 303–342, 387–459 | Draft candidate with reviewed conditional construction: lexical-reference descriptors, known-interface name/Lambda/bind rows | Header says full raw-source elaboration open; table takes known lexical/declaration interfaces and contains no raw brace-owner rule |
| Inferred call views §§1.1, 2–3, 5; lines 67–82, 98–134, 153–186 | Authoritative approved direction; source-derived identities/evidence precede comparison | Exact protected seed/discharge and source registration judgments remain open; actual callable roles stay fixed |

The redesign charter §§1–2 also withdraws F5 scheme equivalence as the semantic
target. Using its source identity contract here does not reinstate its Q/R or
closed-scheme architecture as a successor requirement.

## Partial derivation tree and first hole

Use occurrence labels `df`, `dx`, `ds` for the outer formal, inner formal and
local declaration, and `uf`, `ux`, `us`, `c` for the three uses and application.
These are labels for distinguishable source occurrences, not freshly certified
typed paths or identities. The prior audit supplies the production-composition
syntax characterization; no exact-byte parser execution was added.

```text
BindingStatement(my, Pattern(apply, formal f), inline OperatorChain(B))
  B = BracedStatementBlockExpression
        Statement(BindingStatement(my, Pattern(step, formal x), body(f x)))
        BlockStatementSeparator(;)
        Statement(OperatorChain(Name(step)))
                 [grammar/CST composition: established input]

  outer header is one recovery-free identifier formal
  -------------------------------------------------- F5 §§3–4,21
  definition root + df = ParameterId(root,0) + outer Lambda occurrence

  outer formal has no outer computation annotation
  -------------------------------------------------- selected charter §21
  P_f = Value(A_f); body binding for f is Value(A_f) after entry rebind

  B is a raw brace owner containing a local declaration and final Name
  ================================================================== M_B: MISSING
  B realizes a lexical local-function/result-binding body, with ds/dx,
  enclosing df visible in the inner body, and final us selecting ds

  Synth(B) = I_B                                 [unavailable premise]
  -------------------------------------------------- result-synthesis A
  outer Lambda result = Result(I_B)              [cannot instantiate yet]
```

F5's actual implementation boundary is consistent with this stop:
`crates/yu-hir/src/module.rs:1155–1205` allocates the outer formal and wraps the
lowered body; `1419–1423` requires a childless atom and returns Unsupported for
a composite body. `1305–1320` separately rejects indented statement blocks.
F5 §21's unsupported-body outcome retains a Lambda/root/parameter but makes
the Function ineligible. This is a current implementation fact, not a source
meaning that braces must be rejected.

**M_B is the first unsupplied premise:** an in-scope raw-owner realization rule
for precisely `{ my step x = body; step }` under one enclosing ordinary formal.
It must introduce the local declaration/formal, determine the lexical body
environment, select final `step` as result, and transport the same enclosing
binder into the returned Function's static evidence. For this fragment the
required resolution edges are `uf → df`, `ux → dx`, and `us → ds`. None is
inferred merely from a token spelling. The rule can leave the inner application's
typed call elaboration as a separate child obligation: selecting a bind/Lambda/name
structure must not assume the later protected callback contract.

This is an obligation description, not an adopted successor rule. In particular,
writing the Draft table's `bind(ds, result(lambda(dx,...)), result(name ds))`
as the answer would assume M_B. No governing clause has been found that licenses
that replacement for this raw owner. The construction stops before doing it.

## What L/C/R now contains

| Prior premise | Removed or bounded part | Exact remainder |
|---|---|---|
| L: raw lexical mapping | Grammar composition and outer one-formal root/Lambda identity follow the supplied syntax audit and F5. Parameter role follows selected §21 once that occurrence is a formal. | M_B: local owner realization, nested scope edges and final-result selection. Applying the ordinary role decision to the inner `x` is conditional on introducing that local formal. |
| C: capture | The retained Oracle ledger supplies static shared-TypeVar capture for its exact nearby program. Draft §3 explicitly makes descriptors lexical-reference captures with inert creation. | Exact candidate static evidence transport is still part of M_B; Draft descriptor lifetime, runtime escape and observational allocation/consumer claims are not approved raw-source facts. |
| R: roles and result/core composition | Value parameter default and forwarding A are selected source rules; they need not remain arbitrary role/result assumptions. | Raw local binding realization and the Draft `bind` construction remain conditional. No execution law is applied to raw braces here. |

Thus H_binding is established only for the outer F5 wrapper; local H_binding,
H_scope and H_block are blocked at M_B. No complete source-to-core theorem is
established. The already reviewed Draft theorem remains conditional on its
lexical/declaration derivation inputs and has not been promoted.

## Frozen evidence and independence

At `a58eefc3`, public `control-flow.md:176–189` and
`syntax-style.md:186–208` expressly describe final-expression block values;
`functions.md:14–32` describes local binding placement and left-to-right
currying. Frozen `block_local.rs:69–86,122–140,545–590,866–896,1284–1306`
corroborates lexical local registration before the tail, local Function
lowering, final-expression result transport and scope restoration.
`lambda.rs:271–282,310–368` recursively lowers parameter stages and emits a
Lambda value. These supplied paths were read directly at the frozen revision.
They corroborate intended correspondence; they do not install M_B into the
current raw-to-core rules or prove escaped runtime reference lifetime.

The retained Oracle ledger at baseline, line 36, reports successful lowering of
`my outer x = my inner y = ({left: x, right: x}, y); inner`, exact shared outer
TypeVar identity, and its exclusion from local quantifiers. It establishes a
reported historical static-capture witness for that program. Its removed probe
was not rerun. It does not establish exact brace-candidate acceptance, receiver
evidence or operational capture. Line 37's failed local forward-reference probe
prevents generalizing this evidence to arbitrary local recursive groups.

Legacy docs, lowering and ledger have a shared Oracle lineage. They are
corroborating artifacts, not independent runtime oracles. The Draft core shares
its supplied lexical/interface assumptions with the contemplated correspondence;
a checker implementing those transitions would not prove M_B. No new oracle,
checker, mutation, enumeration, random seed, numerical range or performance
sample applies to this derivation attempt.

## Checks, omissions, resources and stopping condition

Budget: at most 12 sequential lightweight top-level commands; no compiler edits,
tests, builds, probes, child agents, Git mutations or extra output paths.
Consumed: nine sequential `exec_command` invocations and one leased-file
`apply_patch` write. Commands were scoped `rg`, pinned `git show` reads, rule
reads, baseline/status inspection, SHA-256/equality checks and artifact readback.
All command wall-time reports were below 0.1 seconds. Full session wall time,
aggregate CPU and peak RSS were not instrumented and remain unknown. Read-only
Git subprocesses were sequential; no heavy process ran.

The first locator scan read live shared navigation; semantic conclusions use
the pinned sources. One larger read was output-truncated; the decisive core
header/input/translation/§6 and architecture boundary were recovered by narrow
reads. This is not exhaustive historical-authority or runtime research. Pending
question-board answers and unrelated shared edits were not consumed or modified.
Empty/trailing-only blocks, records, control owners, multiple formals, State,
mutation, handlers, forward groups, and arbitrary recursion are omitted. No
semantic or compiler verification is claimed by the note's hash/readback checks.

Failure conditions: a direct dependency changes; an existing approved M_B is
located; or exact source evidence contradicts the proposed lexical/result
structure. Those require a focused delta audit. Increasing toy-model cases or
parser-only checks would not discharge this premise. Stop at M_B under the
assignment's first-unsupplied-premise condition.

Recommended next action: the primary should locate or record the exact supported
raw-owner realization M_B using the retained compatibility evidence, then dispatch
its fixed lexical output to the separate H_call/H_registration gate. This does
not require reopening the selected grammar or actual callable meaning.

## Frozen direct dependency hashes

All current inputs below were read at baseline and matched live bytes when
checked; legacy inputs were read only at the named frozen revision. No changed
direct dependency hash was observed. Shared task/index files were navigation
inputs only and are intentionally excluded from the semantic pin set.

| Revision | Path | SHA-256 |
|---|---|---|
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` | `bef24bf81b5d561538974db75c950a2df9cc2ed0b49248f2440fb0781941e436` |
| `503ae9d2` | `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `503ae9d2` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `503ae9d2` | `syntax-reference/en/src/expressions/braced-statement-block.md` | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| `503ae9d2` | `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `503ae9d2` | `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `503ae9d2` | `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `503ae9d2` | `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `503ae9d2` | `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `503ae9d2` | `notes/progress/2026-09-29-intrusion-oracle-ledger.md` | `b603335b97537931396c56cd2537fa7a83df3ce8f73cc9738de5920c641c8b60` |
| `503ae9d2` | `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `a58eefc3` | `web/docs/reference/control-flow.md` | `cce270b697f4a8ce3a711a6daec107405dbf93d192187e555138204813d84da1` |
| `a58eefc3` | `web/docs/reference/syntax-style.md` | `d14da22ae583771387f41320126c5d2be0fe20a33df8d78a8113243cd2c3d229` |
| `a58eefc3` | `web/docs/reference/functions.md` | `b2a616ea603dccaa431bfcea0c4c2e6eff54b5e058ff9fb6370cb2eb081fa611` |
| `a58eefc3` | `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `a58eefc3` | `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-source-registration-block-core-constructive.md` only.
- Baseline SHA: `503ae9d21fc7b0e4a1062cd101804fb13183273c`; legacy revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none observed; direct inventories above, with final recheck.
- Claim/review status: frozen, unreviewed partial constructive derivation and bounded authority characterization; producer checking is not independent review; gate remains open.
- Checks already run: pinned-source/locator reads, lease absence guard, SHA-256 inventories, live/baseline dependency equality, final note readback and dependency recheck. No compiler/test/build/probe/Git mutations.
- Proposed one-line research-checkpoint commit message: `research: locate first nested block source-to-core realization premise`.
- Shared-record deltas left for primary/curator: record that selected parameter roles/result forwarding reduce R, while M_B precedes local binding/scope/export correspondence; retain bounded legacy static-capture evidence and separate H_call/H_registration plus runtime lifetime. No task/index/theory/authority/question-board files changed; no gate closure proposed.
