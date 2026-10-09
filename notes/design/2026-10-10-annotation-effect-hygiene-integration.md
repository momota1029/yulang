# Annotation effect hygiene: selected policy and existing proof integration

Date: 2026-10-10
Status: Authoritative for the explicit user policy in §1; integration mapping passed scoped conformance review
Scope: polarity-sensitive concrete effect annotations and reuse of existing hygiene results
Selected-by: user, directly in the continuing inference conversation
Reviewed-by: bounded architecture mapping and independent spec/authority conformance review
Approval locator: exact message timestamps/URLs unavailable
Baseline: `b17eae5638dfe9378928fa8ca2c0ae99db02d6a1`
Implementation: policy/proof integration checkpoint; concrete annotation solver integration remains open
Supersedes: no existing conditional theorem; narrows any framing that hygiene must be reproved from scratch

## 1. Current user policy and instruction

The user stated:

> エフェクトの衛生性についてはOracleを参考にしてほしいのですが，注釈として反変位置に`[E]`と入った場合，その関数内ではその場所のエフェクト変数から`E`を引いて良い，共変位置に`[E]`と入った場合，そのエフェクト変数では具体的に`E`が出ても良い（型変数は無視する），という考え方です．ここらへんは大丈夫でしょうかね？

After discussion of the current implementation gap, the user instructed:

> かなり前に衛生製の証明はしていた気がするんですけど，また別なんですかね．まあ統合を試みてくださいな．そうじゃなくても方針としては書いておいてください

Record and use this selected policy. No further semantic vote about the displayed
positive/negative cases is required. This instruction authorizes integration
work; it does not claim that the current compiler already implements it.

| Annotation position | Selected meaning |
| --- | --- |
| Contravariant `[E]` | Permit function-local subtraction of the specified concrete `E` from the effect variable at that position. |
| Covariant `[E]` | Allow concrete `E` at that effect position. Type variables are not concrete annotation atoms. |

Polarity is composed through nested Function structure, rather than determined
only by the nearest textual argument/result label. Keep concrete effect identity
and its type arguments resolved; spelling alone is not semantic identity.

The following variable distinction is the Oracle-supported integration reading,
not an invented stronger user quote: ignoring a variable while collecting
concrete annotation atoms does not delete its connection, declare it empty, or
exempt concrete lower bounds later reaching it from the retained checks.

## 2. Oracle correspondence

Reference: frozen Yulang2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
These are source-inspection results; no Oracle execution ran for this checkpoint.

- `crates/infer/src/lowering/mod.rs`, `SignatureLowerer::lower_pos/lower_neg`,
  lines 571–663: Function parameter/argument-effect polarity reverses, while
  return/result-effect polarity is retained.
- `lowering/signature_effect.rs:78–107`: positive concrete rows become `Pos::Row`
  and symbolic tails retain their variable connection. The negative return-effect
  construction at 162–178 and 319–439 uses an inner variable, a fresh
  `SubtractId`, declared concrete `Set(E)` and a filtered `Neg::Stack` view.
- `signature_effect.rs:453–460` and `annotation/constraints.rs:741–748` skip
  annotation variables when constructing concrete atom/grant sets.
- `annotation/constraints.rs:424–470` constructs stack/pop evidence;
  363–389 and 848–851 carry matching `NonSubtract` weights into returned values.
  The lambda annotation/predicate path retains actual local/function ownership
  in `lowering/expr/lambda.rs:919–942,1232–1237,1244–1307`.
- `constraints/machine/bounds.rs:3213–3255,3285–3360` retains filters on variables
  and checks existing/future concrete lowers. An unresolved variable is not
  itself a forbidden concrete effect; a later concrete effect is still checked.

The reference motivates source-owned scoped filters and allowances. It does not
select a literal migration of Oracle weights/IDs into the successor. A concrete
allowance is not a subtraction grant at every occurrence of the same row.

## 3. Existing results retained and reused

Document-level Draft status does not reopen a reviewed conditional subtheorem.
The existing results retain their exact premises and claims.

| Existing result | Reuse for this integration | Retained premise/limit |
| --- | --- | --- |
| [Typed boundary transport/lifetime package](2026-10-02-typed-boundary-realization-draft.md), §6, “Transport and lifetime theorem package” | Composition, identity, source-union distribution, no authority creation, depth preservation and current-scope filtering transport annotation-owned profiles through argument/environment/store/result views. | Requires supplied valid typed correspondences and owner/profile derivations. It does not construct raw annotation profiles. |
| [Typed source owner realization](2026-10-02-typed-source-owner-realization.md), owner/view preservation | Retain original receiver/receipt identity, request origin, dependencies and expiry across transport/re-entry. | Reviewed within its finite monomorphic decorated input; raw-source inference is outside that claim. |
| [Source interface adequacy](2026-10-02-source-interface-adequacy-theorem.md), exact-interface simulation and milestones 1–2 | Reuse candidate semantic-carrier step simulation, latent future-use preservation and bind composition once annotation construction supplies those transitions. | Exact relational-image result does not certify the current finite solver or raw annotation lowering. |
| [Concrete capture profile derivation](../progress/2026-10-05-concrete-capture-profile-derivation.md), conditional concrete-item corollary | An established concrete annotation profile yields receiver-local eligibility under the existing typed path and active-owner rules. | Eligibility is conditional and does not prove actual handler selection or whole-support removal. |
| [Protection-only filtering derivation](../progress/2026-10-05-handler-protection-filter-derivation.md) | Preserve its frame condition and witness-local filtering result if protection release is involved. | This is the separate `'e?` operation, not a reinterpretation of `[E]`; one global row bit cannot distinguish sibling routes. |
| [Attached subtraction separation](../progress/2026-10-05-effect-attachment-subtraction-playground.md) | Retain the known distinction between subtracting an attached contribution and deleting an entire family/type support point. | Bounded executable characterization with supplied flags; another same-point contribution can remain in the complete output. |

The earlier [parent transport theorem](../progress/2026-09-30-intrusion-parent-transport-composition.md)
remains a reviewed conditional **pure injective renaming** result. It is not
silently promoted to a proof of the current parent/copy equality operation,
which can identify rows. Likewise, existing directional protected-variable
results retain their documented source envelope; new concrete/filter constructors
are a delta, not a reason to repeat that established empty-effect derivation.

## 4. Connection to the current successor

The integration preserves two facts separately: canonical type/effect row
identity, and the original annotation position/boundary that supplies authority.
The existing boundary proofs prohibit inventing a grant solely from equal
families or equal underlying values. Parent/copy equality must not turn an
annotation-local grant into an unconditional global removal property.

A source annotation at its resolved position supplies the concrete contract or
allowance; its symbolic variables remain connected. Existing typed transport
then carries the original position/owner witnesses with their dependencies.
Concrete lower contributions encounter the appropriate retained check/filter.
Actual handler output projection still preserves independent surviving
contributions, including another contribution with the same family/type point.
This instantiates the existing proof responsibilities; it adds no new universal
proof or full-Call-registry prerequisite to basic inference.

The read-only implementation attempt found these concrete owner gaps:

| Owner | Current boundary | Required construction |
| --- | --- | --- |
| `yu-hir::module::plain_binding_header`; `module/local_source.rs::LocalSourceParameter` and `LocalSourceForm` | Parameter carrier admits plain identifiers and retains no resolved type/effect annotation. | Retain the actual annotation occurrence, owner, composed polarity, resolved concrete effect operands and symbolic variables at formation. |
| `yu-solver::EffectEndpointKey`; `yu-types::Leaf`; `candidate_scheme::Atom` | Effect alphabet contains variables and bottom/empty, with no concrete `E` or subtraction/filter view. | Add concrete effect comparison and an executable annotation-owned filtered/allowance view together; metadata alone has no consumer. |
| `candidate_source` and `shadow_apply::admit_candidate_fact` | Construct original source endpoints and four-port demands. | Admit the annotation boundary at that construction, preserving existing upper-use protection direction and provider no-backflow. |
| `candidate_extrusion`, `candidate_scheme`, `candidate_intrusion` | Directional bounds, live recapture, freshening and canonical SCC equality already work in the private candidate. | Transport the executable view and referenced coordinates, retain annotation ownership through equality, and journal its propagation state. |

A boundary-local effect-view constructor is an implementation candidate, not an
approved representation chosen by this record. Resolve its data layout while
implementing the coupled constructor/consumer cut; do not add unused permission
metadata, string-labelled effects, or support-wide cancellation as a substitute.

## 5. Delivery and next implementation cut

This checkpoint integrates policy and existing proof results into one explicit
source-to-successor plan. It makes no compiler-code or runtime integration claim.
The immediate implementation cut is resolved effect annotation formation plus
an executable concrete atom/filter algebra, wired through propagation,
capture/freshening/extrusion, equality and rollback. Full Call registry adoption
and arbitrary-view completeness have not been established as prerequisites for
this local cut.

Required behavior to verify when that cut exists: positive concrete acceptance
and rejection; scoped negative removal; symbolic flow and later concrete lowers;
two boundaries sharing a row; provider no-backflow; independent fresh uses;
parent/copy equality retaining boundary identity; failure rollback. These checks
are a future implementation verification plan and have not run here.

Mode: M1 for this policy/proof mapping, one scoped spec/authority reviewer.
Verification: local document links resolve; `git diff --check` passed; no builds, tests,
execution probes or measurements. Measurement budget: zero samples/processes.
Concrete effect implementation remains a subsequent M2 artifact with semantic
and exact-conformance review; this record does not close its runtime gate or the
full inference/F5 replacement objective.

Delivery record: [policy/proof integration checkpoint](../progress/2026-10-10-annotation-effect-hygiene-integration.md).

## 6. User-supplied callback scenario

Status note (2026-10-10): the user corrected the assistant's interpretation of
“ソレはミス”. The reported inferred scheme below is the mistake; this does
not mean only its extra `int ->` is wrong. The user has not supplied the
correct scheme. Keep the reported pair as a known-wrong historical result, not
as an expected scheme or regression oracle.

The user supplied this source/result pair to clarify the selected boundary:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

```text
(int -> ['b, io] 'c) -> ['b] 'c
```

The intended locality is to subtract the attached `io` from the callback's
effect in this body while preserving independent effect flow. The reported
scheme is wrong, but the correct exact scheme remains unknown. Treating a
variable as “not a concrete annotation atom” must not sever future concrete
effects from its checks. This historical candidate is not a claim that the
current successor accepts the source or that the whole type is already
verified by a runtime test.

This is the same locality requirement as effect hygiene, not a separate semantic
permission: subtraction at this annotation must not mutate a shared canonical
row, erase an independent same-family contribution, or affect another callback
use. The current paired formal constructor still rejects explicit effect rows;
this scenario is an owning target for the open contravariant integration gate.
