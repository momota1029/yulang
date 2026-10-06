# Original association: current shadow correspondence audit

Date: 2026-10-08
Baseline: `5809cd94c346c6095189e0e0664a13457dea4a68`
Status: unreviewed research characterization; frozen on producer submission
Scope: current default-off source/core/solver structural plumbing only
Authority: FVIEW §§2,5 and integrated function-call-view-formation/q1/a2;
typed-computation-core §§6,9; source-contracts §§2.1,3.2,3.5

## Objective, method and exact premise

Map each required original-fiber component to the existing implementation,
without treating structural identities or assumed witnesses as semantic
introductions. This is a bounded correspondence derivation from inspected
constructors and their consumers, not an executable experiment, source
counterexample, repository-wide absence theorem or independent review.

The target remains the existing query on `I_orig(X)`: an original incidence
`t=(beta,s,p,c)` whose witness owns it at the original receiver/use/scope,
types its complete contribution over the receiver-invocation family, and
preserves providers, source arms and one shared `xi=(nu,K,D)`. Keep every
legitimate witness. Do not define `s=p0`, `c=j_call`, singleton Slots, or a
fresh association predicate by decree. The query is recorded in
`notes/progress/2026-10-07-successor-source-association-falsification.md:120`.

Hypotheses for the structural conclusions below:

1. Read the exact baseline implementations named in the dependency manifest.
2. Source/HIR joins use the same retained parse artifact and its sidecar;
   foreign or missing identities are rejected or remain unavailable.
3. Application and SCC queries observe existing inventories; they create no
   dependency occurrences and discharge none of their pending premises.

These hypotheses establish structural preservation only. They do not assume
`CALL_TYPE`, independently interpreted owner/view contracts, Generalize
eligibility or any inhabited original fiber. Source-contracts §2.1 explicitly
takes independently typed primitive and owner/view contracts as input; §3.5
also assumes local typing and complete emission conformance. Reading those
conditional results cannot construct the omitted input.

## Governing decisions and baseline

FVIEW §2 requires one source-component contract, stable `beta/Slots(beta)`,
source-generated typed paths/Flow/owner/receiver, and jointly scoped original
constraints. §5 leaves the exact generation judgments and implementation
gated. The integrated q1/a2 decision permits annotations as inputs but does
not require them; the selected unannotated provisional Handler treatment and
ordinary-value refinement concern the shared inferred relationship. Actual
callable role/entry remains separate. The selected directional protection
rule seeds the original upper output occurrence; it gives no reverse provider
protection rule or independent source formation certificate.

Typed-core §6 generates `(I,d,n)` relative to lexical/declaration interfaces
and complete-call constraints. §9 separates `J_arg`, closure `J_body` and
complete `J_call`, preserving entry demand, typed rebind, body, designated
consumer and pending return/resumption suffixes. Source-contracts §3.2 needs
that complete constructor contribution, including conservative production
alternatives under their original licensing. A syntax Apply is neither its
independently typed complete family nor its static incidence witness.

`tasks/current.md:382` and its subsequent implementation entries describe
the approved default-off lane. The committed pending use-instantiation
carrier is included here; its existing independent implementation review is
not a review of this audit.

All following SHA-256 hashes matched the working files and their baseline
blobs at the dependency check. No dependency hash changed during this audit.

| Dependency | SHA-256 |
| --- | --- |
| `tasks/current.md` | `c78c649542fda61aa74ca6460ace9cc1dc4f25a47b6a1d90294539a3aff33d12` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `crates/yu-hir/src/shadow.rs` | `cfecce4aff6bc28ee234e83fd1a6748ae4193c2a0c24644a8823a8c89470ae4b` |
| `crates/yu-hir/src/module.rs` | `d1bcf808d885bc975bf876c9fb1274d3cd0bfb48f6abf03d3970898b3499da45` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-core/src/shadow_directional_protection.rs` | `9bb4fa098d275874dc0349b115dcc9031648b788fedefd1466af60889e460493` |
| `crates/yu-core/src/shadow_typed_evidence.rs` | `dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95` |
| `crates/yu-solver/src/lib.rs` | `235ed5e36f9ad8da1491ed77509fca085de00244f0e0df494d15efb2137e6dfb` |
| `crates/yu-solver/src/shadow_f5.rs` | `8eac749c1a3b65981bf3a0868a9778f9929ec28ef356267ec0edbbe5ec290e13` |
| `crates/yu-solver/src/shadow_scc.rs` | `b9f14fa8f6e7301014b39496f6992f99fa15ec5587ee497ef9e37bcee1d37d57` |
| `crates/yu-solver/tests/shadow_f5_differential.rs` | `2790c8688b246f45b2bff0262dea94c1af6d5246e0239d3cad60c14de1051663` |

## Component correspondence

| Required component | Exact retained payload and locator | Missing interpretation / class |
| --- | --- | --- |
| `beta` | Artifact-branded source `PositionId`, syntax parent/children and range; annotation occurrence identity (`yu-hir/src/shadow.rs:500`); exact HIR occurrence/parameter/root sidecar joins (`:256`, `:279`, `:301`). | Structural source identity exists. No source-generated contract identity `beta`. `AssumedOriginalContext.beta` (`yu-core/src/shadow_directional_protection.rs:12`) is caller-supplied, not produced. |
| `Slots(beta)` and original `s` | Ordered header parameters and annotation incidences (`yu-hir/src/shadow.rs:560`, `:575`); direct-call and all-retained-Use groups (`yu-core/src/shadow_derivation.rs:580`, `:589`); current scheme Q/R inventories (`yu-solver/src/shadow_f5.rs:167`, `:174`). | No semantic slot inventory or original incidence `s`. These three inventories have different domains and cannot be equated. `OriginalSignatureApplicabilityAndContributionFormation` (`yu-hir/src/shadow.rs:759`) remains unresolved. Empty inventories establish no exhaustive absence. |
| Typed `p0` | Exact source Apply/callee/argument positions and expression identities (`yu-hir/src/shadow.rs:634`); eight candidate structural labels keyed to the Apply (`yu-core/src/shadow_derivation.rs:633`). | No source-generated typed effect position. Whole-ApplyEffect, CalleeEffect and CandidateFunctionReturnEffect labels assert no endpoint equations or original upper correspondence. `AssumedTypedPort.position` (`yu-core/src/shadow_typed_evidence.rs:153`) is an assumed token. |
| Owner/receiver | Lexical UseId/BinderId resolution, declaration Lambda owner or root-header membership (`yu-core/src/shadow_derivation.rs:735`, `:751`, `:759`); capture incidence (`yu-hir/src/shadow.rs:814`); SCC parent/target/component (`yu-solver/src/shadow_scc.rs:209`). | These are lexical/declaration ownership and current topology. No actual receiver activation, typed receipt/rebind, active owner/handler or typed ownership incidence is produced. AssumedBoundary/Receive/Configuration (`yu-core/src/shadow_typed_evidence.rs:160`, `:190`, `:209`) explicitly take those inputs. |
| Complete contribution `c` and invocation family | Retained Apply syntax and complete operand subtrees; raw call-local pending metadata (`yu-core/src/shadow_derivation.rs:735`); PendingApply projection (`:329`); pending solver Apply/callee/argument rows (`yu-solver/src/lib.rs:782`). | No independently interpreted complete contribution or `OriginalAssocType_X` witness. `ApplicationTypingRuleUnresolved` persists. Syntax has no typed entry/receipt/body/consumer/native-return/resumption relation. Supplied typed-evidence graph reachability does not construct that relation. |
| One original `xi=(nu,K,D)`, source arms and scope | Branded parse/HIR/collection/solved ownership; borrowed original source nodes and lexical binders; finalized current scheme endpoints (`yu-solver/src/shadow_f5.rs:160`); collection-brand validation (`yu-solver/src/shadow_scc.rs:48`). | Identity consistency exists. No source-generated joint semantic assignment or joint descriptor/admission interpretation. `JointlyScopedOriginalConstraints` stays pending; AssumedOriginalContext.xi is external. Scheme endpoint/Q/R equality cannot supply the shared original witness or transport. |

The seven application `Premise` rows (`yu-hir/src/shadow.rs:892`) and seven
`UnresolvedSourceViewPremise` categories (`:759`) are distinct inventories.
Neither list is an introduction rule. Conditional helpers check assumption
wiring and derive conclusions under it; they do not establish those source
assumptions.

## Structural derivation and smallest useful witness

The compact supported fixture already retained in
`crates/yu-solver/tests/shadow_f5_differential.rs:435` is:

```text
my invoke x = x(x)
```

This is a structural domain discriminator, not a semantic counterexample or
a claim of globally shortest source spelling. One Apply and two immediate
Name operands suffice; two occurrences of one binder avoid introducing a
second declaration. Existing test assertions were inspected, not executed.

1. `retain_pending_applications` (`yu-solver/src/lib.rs:1295`) recursively
   visits Lambda/Group/Apply and retains one row for this Apply. Both Name
   operands carry distinct HIR occurrences and `NameResolution::Parameter`.
   `pending_application_source_uses` (`shadow_f5.rs:79`) yields two borrowed
   uses in callee/argument order without inventing a dependency UseId.
2. Collection emits `PendingDefinitionUse` only for a root resolved Name or
   an immediate Lambda-body resolved Name (`lib.rs:1053`, `:1107`). This
   fixture's Lambda body is Apply, so neither branch runs. In addition,
   Parameter is a different resolution category from Resolved(DefId).
   DefinitionUseId construction (`lib.rs:1150`) consumes only those previously
   collected pending dependencies; traversing a shadow Apply does not feed it.
3. `pending_use_instantiation` (`shadow_scc.rs:21`) requires an existing
   `SccUseRef`, validates its retained parent/target and obtains the target's
   current closed scheme. It cannot be invoked for either application operand
   by calling a parameter a definition dependency. A shared Binder, component,
   current scheme or source range cannot repair this occurrence-domain gap.
4. Independently, each valid pending Apply can join through its exact source
   sidecar to a shadow Apply, its two source operands, and raw metadata. The
   existing nested differential (`shadow_f5_differential.rs:393`) joins a
   direct-use registration and declaration owner. The endpoint-skeleton query
   (`yu-core/src/shadow_derivation.rs:599`) validates an exact same-arena Apply
   and offers eight derived addresses. It supplies no typed association.

Thus current source/core/solver retention composes where the structural
projection exists. Current SCC use-time observation is a separate partial
chain over current collected definition dependencies. The entire original
fiber has no semantics-free unification seam in this inspected representation:
`beta/Slots`, typed `p0`, actual receiver and complete contribution are missing
interpretations, not merely fields omitted from an identity join.

## Smallest optional plumbing seam and its boundary

The smallest additional structural slice is an exact borrowed correspondence
from a pending solver Apply row to `RawStructuralArena`'s existing
`PendingApplyEndpointSkeleton`, using the same parse sidecar and exact source
Apply identity. Existing differential code already performs most of this join;
it does not query the eight candidate addresses. A future separately authorized
slice could retain/inspect that final link and compare each operand with the
source operands, without allocating endpoints or adding a solver fact. Keep
this at a compatible observation/test boundary; this audit does not authorize
a new production dependency between crates.

This unifies only the existing source/core/pending-application chain. Preserve
all application premises and missing-skeleton outcomes. Do not attach
`PendingUseInstantiationRef` unless the exact SCC dependency occurrence already
exists. A resolved definition could independently expose its current scheme;
that would still not prove an application use-time instantiation or create the
missing SCC occurrence. Parameters, grouped/computed operands and unresolved
Names must retain their distinct outcomes.

Recommended next action: have the primary adjudicate an independently typed
original owner/view introduction over the complete Call family at the same
`X/xi` (after or explicitly conditional on `CALL_TYPE`). The optional eight-label
join improves inspectable bookkeeping but cannot replace that source clause;
another model assuming it would leave the same premise untouched.

## Subsequent shadow crosswalk checkpoint

The optional observation seam identified above was added to
`crates/yu-solver/tests/shadow_f5_differential.rs` at commit
`d8304f33b1adf62cf8645529e2a9c81281688e15`. The reviewed differential now
joins solver Apply rows through HIR positions to the existing core
`PendingApplyEndpointSkeleton`, checks all eight labels and all seven source
premises, and distinguishes outer argument labels from inner whole-Apply
labels. The application typing state remains unresolved. Its focused target
passed four tests under compiler-referee review.

This closes the optional identity-inspection seam, not a semantic premise.
The eight labels still assert no typed `p0`, endpoint equality, `beta`/slots,
callable role, complete contribution, or original `xi`. No typed or production
inference fact was added. The source/kernel introduction and `ORIGINAL_ASSOC`
gate therefore remain open.

At integration HEAD `02743d3dd`, the only changed dependencies are
`tasks/current.md` (current SHA-256
`163f03a180f9cd32c7a8998e6c23f7c7e7cc53e6f362c4c7a33971b84c08298f`) and
`crates/yu-solver/tests/shadow_f5_differential.rs` (current SHA-256
`3d079a7a0f54fdd0d24935d73dcc26c9617df3f0de3299189696c9e914c913e0`). The
task changes are navigation/progress records; the test change is the reviewed
structural crosswalk described here. The other thirteen direct dependencies
remain byte-identical to baseline `5809cd94c346c6095189e0e0664a13457dea4a68`.

## Checks, independence, failure conditions and omissions

Read-only commands: `git rev-parse HEAD`, `git status --short`, scoped `rg`,
`sed`/`cat`, `git ls-files -s`, and a single Python process comparing each
manifest file byte-for-byte with `git show 5809cd94...:<path>` and computing
SHA-256. All 15 manifest comparisons returned PINNED; HEAD was still the
baseline at that check. These are dependency/inspection checks, not execution
of compiler behavior or semantic validation.

No checker, compiler tests, builds, formatting, benchmark, Frozen Oracle read,
Git mutation or child agent ran. No seeds/ranges/enumeration/mutations apply
to this source-inspection method. The displayed witness and collector branch
analysis provide the bounded discrimination. Hypothetical future controls
would reject foreign parse/collection brands, non-Apply sources, swapped
operand identities and missing metadata, and keep nested argument labels
distinct from the inner Apply's whole-result labels; none was executed here.

Oracle independence is literal: no Frozen Oracle artifact was consulted.
Structural projections and inspected existing tests share parsing, sidecar
identity and implementation data, so they are not an independent semantics
oracle. Agreement of those paths cannot prove source transition rules.

Resource usage: one small shell/Python inspection process at a time, zero
Cargo/build/test processes and zero heavy computation. Wall time, peak RSS and
aggregate CPU were not measured. Output is this one leased note; no scratch
output. Searches were limited to the named authorities, current shadow code,
collector seam and cited progress/test locators. Other source forms, exhaustive
licensing inversions, production-only alternatives, complete descriptor and
admission clauses, arbitrary recursion/worlds, semantic eligibility and source
acceptance were not audited. Baseline changes in the named dependency cone
invalidate affected deductions; unrelated branch movement does not.

## Commit packet

- Exact lease/change: `notes/progress/2026-10-08-original-association-shadow-correspondence-audit.md` only.
- Baseline: `5809cd94c346c6095189e0e0664a13457dea4a68`.
- Revalidated at the post-crosswalk integration point: only
  `tasks/current.md` and `crates/yu-solver/tests/shadow_f5_differential.rs`
  changed from the pinned dependency snapshot. Both deltas are recorded above;
  the source correspondence deductions and gate status remain valid.
- Review: unreviewed producer artifact; no independent certification claimed.
- Checks already run: narrow read-only source inspection and all 15 dependency
  byte/hash comparisons at the research baseline; the later endpoint-crosswalk
  test passed 4 focused cases under independent compiler-referee review. This
  audit itself has no semantic test or independent semantic review.
- Proposed commit message: `research: audit original-association shadow correspondence`.
- Shared-record deltas left for primary/curator: optionally link this bounded
  audit and record the application/SCC inventory distinction in
  `tasks/current.md` or the relevant research queue. Keep ORIGINAL_ASSOC,
  CALL_TYPE and all dependent semantic/lifecycle gates open; no authority,
  theorem-status or obligation-edge promotion is proposed.
