# Current Call contribution seam: structural consumers and typed invocation cut

Date: 2026-10-06
Baseline supplied by primary: `1d29aafb1a89568ac61bc6bf007398db2b31cc23`
Branch assigned by primary: `research/simple-sub-intrusion`
Status: frozen, regression-reviewed bounded implementation correspondence; minor falsifier scope repair closed by primary
Method: constructor/output audit and explicit hypothesis derivation
Exclusive write lease: this new note only
Semantic and implementation authority: none

## Objective and genuinely new result

Audit the complete contribution coordinate in the original signature attachment
`Attach_C(X,e,t)`, for exactly:

```text
my apply f = { my step x = f x; step }
```

The [previous supplier continuation](2026-10-06-current-signature-supplier-continuation.md)
already supplies parameter/Apply identities and the production lower-Function
recipe. This note follows a different interface: the two actual structural
computation-core consumers in `yu-core::shadow_derivation`, including their
Call payloads and existing test contracts.

The new bounded result is that all structural operands of the selected
Call survive into the exact eleven-node core projection, while the raw core
consumer preserves each retained Apply and its own ordered pending rows.
Neither constructor interprets those operands as a complete typed invocation
contribution. This locates the first missing conversion after structural
Name/Result/Call formation, rather than asking for another identity crosswalk.

It does **not** prove that every possible repository carrier has been
enumerated. The ten-file source budget was fully used; other Rust modules and
external consumers were not searched. It proves no source impossibility,
accepted-source counterexample, complete-profile result or production change.

## Governing sources and hypotheses

Read the original sources, not only the index:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1–5 fixes
  shared original formation, stable slots, source/public/internal distinctions
  and comparison-independent admission; its constructing judgments remain open.
- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3 fixes sequential binding, return of the local closure, the original
  outer `f` and its retained lexical capture.
- [Source-call construction](2026-10-06-source-call-generation-construction.md)
  §§4.2–4.3, §7 supplies the mandatory complete-invocation address and
  `ElimOrigin`, distinguishes initial seed inventory from complete original
  slots, and keeps contribution interpretation as a remaining P clause.
  Its §§3,5 define the retained Name roots and interpreted Call image.
- [Current supplier continuation](2026-10-06-current-signature-supplier-continuation.md)
  §§3–7 and [original supplier map](2026-10-06-original-signature-source-supplier-map.md)
  supply the already audited structural identities and precise negative scope.
- [Original licensing construction](2026-10-06-original-signature-licensing-construction.md),
  “Explicit hypotheses and sorts,” fixes the contribution coordinate as a
  witness/contract, distinct from outward support and dynamic receivers.
- [Exact structural core record](2026-10-06-shadow-structural-core-arena.md)
  and [raw structural record](2026-10-06-shadow-raw-structural-inventory.md)
  describe the accepted experimental limits; their historical verification
  results are not new checks by this worker.

Use these explicit hypotheses:

```text
H_id: one validated ShadowArtifact/Skeleton, exact branded references,
      and successful guards of the displayed constructors.
H_core: approved nested structural meaning and existing ordinary
        Name/Result/Lambda/Bind/Call interpretation, when interpreted.
H_gen: previously reviewed Gen-Call-0 at original scope and shared xi,
       only when invoking its semantic address result.
H_attach: independent original complete contribution/signature attachment,
          stated only as the still-open premise.
```

No complete original row, world admission, successful Q, solved provider role,
profile inventory or live receiver is assumed in H_id. The language meaning
of H_core/H_gen is a shared governing premise; reading Rust does not prove it.

Avoid the overloaded name `c`: below `a_src` is the source Apply identity,
and `kappa` denotes the contribution coordinate called `c` in
`t=(beta,s,p,c)`. They are different sorts.

## Exact new route and complete invocation boundary

| Route at the supplied source snapshot | Preserved object and first missing interpretation |
| --- | --- |
| `yu-hir/src/shadow.rs:1500`, `:1551` | Apply retains original callee and argument ExprIds. CapturedCallInput validates the direct outer-formal callee, direct local-formal argument, local Lambda, returned step Use and exact capture incidence. This supplies structural operands, not J_f/J_x semantic roots. |
| `yu-core/src/shadow_derivation.rs:19`, `:61` | Exact source bytes and all seven CapturedCallInput fields are rejoined before projecting the same skeleton body. Use becomes Name plus Result; Bind's local Lambda value receives Result. The argument subtree is preserved, not replaced by a printed pure interface. |
| `shadow_derivation.rs:99`, `:159` | PendingCall carries a_src, callee/argument arena offsets, borrowed pending rows, exact capture and static unresolved-source-view categories. Its exhaustive fields have no endpoint, complete Function demand, original xi, carrier interpretation, entry/body/consumer image, slot or invocation receipt. |
| `shadow_derivation.rs:176`, `:217`, `:297` | RawStructuralArena borrows every retained Form. Each Apply gets RawCall; pending rows are attached by their exact ExprId, then direct Use and capture identities are validated. RawCall's exhaustive fields are only pending rows/direct incidence/capture. It does not add Result, Value/Computation or an invocation interpretation. |
| `yu-hir/src/shadow.rs:716–756`, `:855–860`, `:1693` | Original signature/contribution formation is a static unresolved category; event contribution/output observation is a pending enum row. The Apply constructor records the row without attaching a typed contribution witness. |
| `yu-core/src/lib.rs:3`, `yu-core/src/shadow.rs:1` | The core modules are gated by the shadow feature; the facade reexports structural HIR objects. It contributes no additional interpreter. |
| `yu-hir/src/module.rs:426`, `:1400`, `:1440` | Production ResolvedExpr has Lambda/Integer/Name/Error. The leaf-chain lowering route has no Apply/Bind/capture expression constructor. This excludes a production typed-Call bypass through this inspected lowering route, not every conceivable future route. |

For the exact source, PendingCall borrows the whole pending table. This is
appropriate to its validated singleton Call; it is not a generic per-call
partition rule. RawCall instead groups the complete retained table by exact
Apply, preserving row order/multiplicity. Neither storage choice supplies
semantic licensing.

The complete invocation sought here includes receipt, actual provider entry,
body, designated result consumer, pending suspension suffix, responses and raw
resumptions on the original joint row. A source argument ExprId and Result
wrapper provide the structural operand of Delay(J_x); they do not establish
its complete CarrierContract or type it in an independently admitted world.
Similarly the capture incidence identifies outer f without manufacturing its
typed environment packet or current receiver.

For this exact Name callee, ordinary core interpretation can construct the
returning J_f; the outer block's final step return is a different Result.
The audit does not identify the whole Call's callee-evaluation prefix,
provider body effect, complete invocation effect and latent returned effect
as one contribution. Existing p0/ElimOrigin identifies the immediate complete
invocation position; no new typed path is extracted from raw storage offsets.

## Derivation and claim classes

**Bounded code characterization.** Under H_id, recursively inspect every
branch of the exact projector. Name retains source/binder/use and adds Result;
Lambda retains parameter/captures/correspondence; Bind retains value/body;
Apply recursively preserves both operands and constructs only PendingCall.
Thus the selected source has the structural input needed for the existing
H_core/H_gen constructors. Inspecting the raw constructor establishes
retention of all original Forms and per-Apply pending rows, with only the
listed identity joins. No transition in either constructor has a semantic
contribution or Attach_C conclusion.

The smallest static witness is the assigned source itself. Its exact arena
has two Lambdas, one Bind, four Results, three Names and one PendingCall.
Removing argument, replacing captured f by x, or invoking returned step
changes the test's structural template. There is no minimized *semantic*
counterexample and no newly executed accepted-source witness.

**Conditional semantic composition.** Applying H_core and H_gen to those
retained operands recovers the already reviewed symbolic construction:

```text
retained a_src, same captured d_f, local d_x
  -> J_f=ReturnImage(Name(d_f)), J_x=ReturnImage(Name(d_x))  [H_core]
  -> shared unsolved U, p0, p_out(a_src), ElimOrigin       [H_gen]
  -> emit complete interpreted Call checking obligations [prior rule]
  -> original kappa and signature incidence attachment   [OPEN H_attach]
  -> independent Lic_C, and exhaustive origin inversion  [OPEN]
```

The source-call construction's ExecuteCallableImage is an independently
interpreted semantic operand under its displayed decorated premises. No
equivalent Rust payload exists in the two audited core constructors.
Emitting that symbolic checking obligation does not automatically identify
its image as the original beta-owned kappa or license every source slot.

**Candidate assumption, not adopted:** identify `kappa` with a_src, a callee
UseId, the pending-row vector, or the whole printed output effect. Each would
replace an interpreted contribution contract with structural identity or
obligation metadata. Adding more such metadata leaves H_attach untouched.

**Established results reused:** exact lexical identity joins, the scoped
nested source meaning and Gen-Call-0 retain their recorded reviewed scopes.
This note is producer correspondence evidence. A regression auditor found no
blocking or major issue and one minor falsifier-precision issue; the
distinction between falsifying contribution absence and closing full licensing
was repaired by the primary. Neither its construction nor the test's template
erasure proves the source transition rules.

The narrower absence claim is falsified by an actual consumer of these retained
core objects that independently constructs a complete typed invocation
contribution on original xi. That result alone would still leave original
signature attachment and forward/reverse licensing open. To close the full
gate, it must additionally derive the attachment and both licensing directions.
Merely changing a pending row, storing another identifier, observing a solved
row or passing the structural tests does not falsify this bounded claim. A new
source rule can resolve the cut without requiring an earlier complete profile;
that possibility is preserved.

## Checks, independence, coverage and resources

Commands run: bounded cat/sed/rg reads, filename discovery with rg --files,
sha256sum on the direct dependencies, output-path absence check, and final
note/dependency consistency checks. Ten distinct current Rust source/test
files were inspected, listed below; the source cap is exhausted. No tests,
builds, Oracle execution, solver/checker, formatter, semantic enumeration,
children or Git mutation ran.

Two initial read-only Git commands (rev-parse HEAD and status --short)
matched the full supplied baseline and initially clean tree. They exceeded
the packet's literal no-Git instruction; the primary was notified and no
further Git command ran. Final branch/ref and baseline blob validation belong
to the primary. Some combined captures truncated; decisive interfaces were
reread in bounded windows.

Existing tests were **read only**. The exact core test checks eleven-node
shape, borrowed identities, unchanged pending rows and three structural
mutations; its foreign/unsupported-source test includes a same-artifact
trailing-whitespace rejection. Raw core tests check exact Form borrowing,
ordered per-Call rows, capture association, two annotations, and eight source
fixtures including same-binder/distinct-use nested calls. CapturedCallInput
tests specify five invalid edge/capture mutations; the locator test preserves
its seven categories. These are contracts, not passes measured by this lane.

Oracle independence: no Oracle source or run was used. One read raw-core
test contains historical spans for a different nested source; those spans
provide no premise here. The exact projection and raw arena share the HIR
skeleton, so their agreement is not an independent semantic oracle. The
exact test's erased template assumes the selected structure. A checker
assuming H_core/H_gen transitions would likewise establish consistency, not
prove those source meanings or H_attach.

Seeds/ranges: none; no search was executed. Coverage is the exact candidate,
both audited core constructors and their tests, source pending-row producers,
and the displayed production lowering route. Typed execution, all
carriers/worlds/resumptions, imports/adapters, recursive components, arbitrary
annotation/brace forms, all Rust consumers, complete-profile nonemptiness,
initial admission, principality and production-only membership remain
unverified. No omission is interpreted as source rejection.

Failure conditions: foreign identities, malformed/missing joins, unsupported
or nonexact source bytes, unavailable Skeleton, and changed dependencies can
prevent the structural result. Any newly found semantic consumer or governing
rule requires rechecking the bounded negative statement.

Resource usage: short read/hash processes only; zero heavy processes, tests
or measurement samples. No numeric CPU/RAM/wall-time budget was supplied;
aggregate CPU, peak RSS and elapsed time were not instrumented. Only the
leased note was written. Direct dependency hashes were rechecked at freeze;
writes stop before review submission.

Recommended next action: derive and independently review the original
contribution interpretation/Attach_C clause using the already preserved
Call operands, original Gen-Call-0 position and complete invocation semantic
image; prove both licensing directions before another identity-plumbing probe.

## Frozen direct dependencies

These are the inspected current snapshots, not a claim that historical
dependency tables are current. In particular, HIR shadow.rs differs
from the older supplier-continuation freeze; the current baseline contains
later shadow work. The primary verified that all listed direct dependencies
match baseline `1d29aafb1a89568ac61bc6bf007398db2b31cc23` byte-for-byte.

| Inspected dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `tasks/current.md` | `01ec045a3bd1f15449529d826565a9e12e9cdb72d8c8513ef7002b50285be59a` |
| `tasks/research-lab.md` | `d8794543008221be430c3b676929b8601fb4534799fc67856e99ad140da0975d` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-current-signature-supplier-continuation.md` | `1e42cf9be0576c12a057e9675d4c8c7bb9f5eac2538d5c62b1b9413593bcddc1` |
| `notes/progress/2026-10-06-original-signature-source-supplier-map.md` | `9f160920a0aa43518e93ec8a139e80657a58032a69e13a7bcfd26ba6a3dd1c59` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-shadow-structural-core-arena.md` | `2bca7eac9d6dbf370d34dcc3e3e6c9fab6db1798a4fb39d553d7892f790c036c` |
| `notes/progress/2026-10-06-shadow-raw-structural-inventory.md` | `61831a9ec400cc47c5b2df7a2d0ddffae30fd2c1887cdd74b3583d747b462e5d` |
| `crates/yu-core/src/shadow.rs` | `f9d44ae357b0af86db2c17b93bc56d33dd150cb460fab612876f16909f3d9f43` |
| `crates/yu-core/src/shadow_derivation.rs` | `651d4c4e77fd76b518d87c841f9cc4ea360760a94ad3198b9265e71443a124ba` |
| `crates/yu-hir/src/shadow.rs` | `4b0914f3a29a5ca47fd912de23ebad690d57908ad628e5dc392b0d8b6df811ac` |
| `crates/yu-hir/src/module.rs` | `2cabe33fa9eda7130e556129be64d80409215018c7c46bf84cb5906819f8b156` |
| `crates/yu-core/src/lib.rs` | `017ee5fae1bc46aea70ac962e2f5de762ed6c2c3afb1f459147b8a2ec1ed9746` |
| `crates/yu-hir/src/tests/shadow_captured_call_input.rs` | `43aeb186da8057452d4783089965d7b466014e0e8a3844d29d0814025b8e30b3` |
| `crates/yu-hir/src/tests/shadow_source_view_premise_locator.rs` | `e2561b6869e88ffa3174d5c411ff8b5f3cf962854423d9702361d66235588500` |
| `crates/yu-core/tests/shadow_derivation.rs` | `dddfa95afca374adc15ca8e15cfb99b64a3c91ea3482ef91d26dc6d7e287d454` |
| `crates/yu-core/tests/shadow_raw_structural_inventory.rs` | `53679ed201adc72b6c79a1328fc879624016682dfc1e61bb2836bc1bc1c074f4` |
| `crates/yu-hir/src/tests/shadow_raw_source_inventory.rs` | `fba09f095deac7383078eda795302b6ea290c886fbd812adc5745ee164c3aa3d` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-current-attach-contribution-seam-audit.md`.
- Baseline SHA: `1d29aafb1a89568ac61bc6bf007398db2b31cc23`.
- Dependency hashes changed during the lane: none; the primary's baseline
  comparison confirmed all 24 direct dependency paths are unchanged through
  reviewed HEAD `64c210c52`.
- Review status: frozen unreviewed bounded research correspondence; no theorem,
  conformance or implementation closure.
- Checks already run: governing/source/interface reads; both complete
  constructor payloads and test contracts; ten-file cap; dependency hashes;
  note-local whitespace/link/hash checks. No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: locate complete invocation contribution seam in shadow core`.
- Shared-record deltas intentionally left for primary/curator: record the
  exact PendingCall/raw RawCall route as preserved structural Call inputs,
  with complete typed contribution interpretation and original Attach_C/
  Lic_C inversion still open. Keep profile/admission existence and production
  gates separate. No shared task/index/authority, manifests/lockfiles,
  compiler or question-board edit.
