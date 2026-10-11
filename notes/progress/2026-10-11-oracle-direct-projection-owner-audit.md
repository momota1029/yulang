# Oracle direct callback: projection and use owner audit

Date: 2026-10-11
Status: frozen, unreviewed research source characterization; original H OPEN
Claim class: bounded owner map and exact missing operational premise
Y3 primary baseline: `afe402a7be1bd0bdfe89a531469927d5788112a2`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation or Git mutation

## Objective and fixed scope

Inspect the actual projection, compact liveness, selector, publication and later
use owners for this selected discriminator:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

The [callback source audit](../theory/2026-10-11-oracle-callback-reuse-source-proof.md),
[identity audit](../theory/2026-10-11-oracle-annotation-scheme-identity-proof.md)
and [frozen probe](2026-10-11-oracle-callback-reuse-projection-probe.md) are
inputs. This pass addresses their concrete missing projection/use facts; it
does not repeat the separate constructive proof obligation.

Authority remains annotation hygiene design §§1–2, original
[H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md) §1 and
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. H retains every successfully lowered program, composed-negative
annotation occurrence, original lexical scope and binder, actual copy/use and
actual call/output route. Instance-local subtraction, independent same-family
survival, connected symbolic tails, current/future retained checks and correlated
lineage remain separate requirements. Successful lowering alone does not prove
successful inference/publication. Complete Call, soundness and principality
remain distinct. No source restriction or selected-language reinterpretation
is proposed.

Let `a` be this formal's concrete row, `i` its original constructor ID and `b`
its row coordinate. These symbols denote actual owner outputs without assuming
numeric allocation order. No identity is inferred from displayed `#0`.

## Exact owners and first stopping branch

Oracle paths below are relative to its checkout, under `crates/infer/src/`.
All statements describe the inspected production paths, not executed records.

| Seam | Actual source owner | Deterministic fact and missing input |
| --- | --- | --- |
| Original row | `lowering/expr/lambda.rs:1244–1307`; `annotation/constraints.rs:424–470` | The parameter connection constructs PUSH/filtered views and registers its stack facts. The lambda also can construct public/erased callable uppers, so a visible stack cannot be identified by a presumed unique allocation. The inherited audit establishes that `direct` never invokes `cb` locally. |
| Projectable record inventory | `constraints/structural_kernel/access/legacy_read_view.rs:214–222,238–244`; `constraints/structural_kernel/access.rs:862–898` | Iterate actual projection lower records and evaluate each. `Excluded` is omitted; both `Unclaimed` and `Included` retain the bound. The frozen evidence supplies no inventory tied to `a` or the returned callback. |
| Projection decision | `constraints/proof/mod.rs:9975–10127`, especially `10015–10031` | An active lower with neither supports nor formula returns `Unclaimed`; mismatched supports/formula return errors; both present enter preflight/evaluation. The first undeduced branch is the actual per-record support/formula presence. |
| Qualified projection | `constraints/proof/mod.rs:10052–10125,11498–11530,11632–11790` | Payload coverage is read from `live_states_by_coverage_root`; actual inclusion is decided separately by the evaluator. Formula arms may use a standalone support, a unary premise, or a conjunction of lower/upper record premises. `Included` may carry exact or fail-open evidence. An empty qualifying payload is insufficient to infer exclusion. |
| Collection | `compact/collect/mod.rs:814–840,848–877`; `compact/collect/type_nodes.rs:1–135,545–562` | Scheme-mode positive collection uses these decisions rather than all raw lowers. Positive Function results receive the carried weight; negative Function arguments receive it. Negative effect-stack compaction can emit concrete prefix items and traverse the tail without that weight. A concrete `tick` prefix is therefore insufficient evidence for ID liveness. |
| Compact preparation | `analysis/session/generalize.rs:430–547` | Final cleanup, alias expansion, stack cleanup and bounded dominance constraint routing precede selection. A raw weighted lower alone does not determine the final compact occurrence. |
| First selector | `generalize/mod.rs:177–238`; `generalize/core/stack_ids.rs:23–49,76–179` | The live branch requires an ID in a nonempty PUSH stack at a covariant compact variable whose TypeVar is quantified. Function argument ports flip sign; result ports preserve sign. Recursive and role bounds also participate. Actual compact paths and the TypeVar quantifier set are missing. |
| All branch | `generalize/mod.rs:867–888` | Add any encountered ID whose current `fact_by_id(id)` resolves to `Subtractability::All`. This is not restricted to annotation-declared provenance. The original concrete `Set(tick)` construction does not establish this branch; the final environment lookup is the relevant fact. |
| Installed selector and scheme | `analysis/session/instantiate.rs:54–83`; `generalize/mod.rs:839–864`; `generalize/finalize.rs:3–26,328–350` | Ancestor simplification and cleanup recompute the final stack quantifiers and prune unquantified weights before `set_def_scheme`. Surviving exported entry keys are intentionally retained across arenas. The installed scheme, rather than an earlier selection, is the use input. |
| Actual scheme use | `analysis/session/instantiate.rs:449–520`; `instantiate.rs:621–647,741–787` | A local definition's installed scheme is cloned. Each selected ID gets one fresh map entry; occurrences reuse it. The root receives POP(MAX) for every selected stack quantifier. The actual `direct` map and cloned returned-callback path are not in the frozen dump. |
| Provider insertion/replay | `constraints/machine/bounds.rs:630–731,2332,3363,3832,4274` | Lower insertion extrudes, filters, may subsume, records insertion/equivalence and projection provenance, then schedules accepted replay. Scheme use may instead queue a subtype predicate at `analysis/session/instantiate.rs:504–520`. Generated demand does not establish its actual surviving provider route. |
| Two applications and effect joins | `lowering/expr/tail.rs:535–624`; `constraints/machine/propagate.rs:210–267` | `(direct provider)` and its final `()` call create distinct result/value/effect coordinates. Function comparison reverses argument weights and preserves result weights. Each app joins callee evaluation effect and its return-effect lower into its result effect. Actual bounds/weights and replay dispositions at these ports remain unknown. |

The pass stops at the concrete owner map and the first undeduced projection
branch. It does not reconstruct the entire proof store, settle loop, compact
normalization or source allocation census.

## Binder call predicate versus exported type weights

The primary requested an additional distinction during this pass. For this bare
Function annotation, `lambda_annotation_predicate_constraints`
(`lowering/expr/lambda.rs:1581–1592`) returns `connection.subtracts`: the
`cb` binder call predicate is populated. The immediate parameter output
predicate is instead empty (`1571–1578`). `mark_lambda_param_call_predicate`
(`919–941`, invoked at `726–735`) stores the call predicate and owning frame on
the local binder. Absence of a local invocation does not mean absence of this
stored predicate.

Its consuming read is `local_callee_call_projection` (`tail.rs:690–705`), used
by application construction (`550–551`) to extend the innermost frame's latent
predicate (`719–726`). A scoped `rg` census of `call_predicate_subtracts` in
`crates/infer/src` found that consuming read, binder initialization sites and
the lambda writer/frame marker. `direct`'s body is the local reference `cb`,
not an application. `lower_local_name` (`lowering/name_ref.rs:145–176`) returns
its value and evaluation effect; it does not copy its call metadata into the
computation. Monomorphic formal instantiation (`tail.rs:855–858`) returns the
same formal value.

`wrap_lambda_param` (`lambda.rs:946–974`) combines
`param.annotation.predicate` and the actual frame; it does not consume
`param.annotation.call_predicate`. Public argument projection
(`987–1040`) requires `local.call_erased_used`, which application construction
sets via `record_local_call_upper` (`tail.rs:707–717`). With no local `cb` call,
this path falls back to the formal's negative variable. The bare Function's
stored call predicate therefore supplies no direct call-induced wrapper around
`direct`'s output from these owners.

The installed `Scheme` (`crates/poly/src/types.rs:17–23`) contains quantifiers,
roles, recursive bounds, stack quantifiers and the type predicate; it has no
field for local binder call metadata. In the final `()` application the callee
is `Expr::App`, while `local_callee_def` (`tail.rs:844–850`) recognizes only an
`Expr::Var`. It cannot recover the old `cb` binder through that application.
Thus the stored call predicate is not directly serialized/activated by these
routes. The paired annotation's type graph already contains ID-bearing PUSH
and NonSubtract weights: their separate compact/export/use behavior remains
the unresolved route, including the quantified-root POP constructor. This
bounded metadata-consumer distinction does not prove that the original ID
survives projection or that later effect subtraction is safe.

## Bounded derivation and its limits

Under the explicit hypotheses of the pinned source bytes, normally completed
owner calls and fresh allocation without exhaustion, the code establishes:

1. A constructed ID-bearing annotation view supplies a candidate path; it
   does not establish a projectable lower after propagation.
2. For a given actual lower record, its projection result determines whether
   collection visits it. Even an included record can subsequently lose its ID
   in compact transformation or cleanup.
3. Given the actual final compact root, roles, TypeVar quantifier set and
   current subtract environment, the selected stack set is the union of the
   live covariant PUSH branch and the encountered-All branch, after the
   finalizer's preparation. These inputs are not supplied by source syntax or
   the printed scheme.
4. Given membership of the intentionally retained original key in the installed
   scheme, normal instantiation consistently maps it and adds its root POP(MAX).
   Membership and a surviving returned-callback PUSH remain unestablished.
5. To attribute the displayed pure `observed_direct` to that POP, the mapped
   ID must occur on the actual later callback effect route. Provider support
   and its independent survival require their own real records.

This is a source-derived conditional characterization of owners. It is not an
established operational witness or a theorem about H. Deterministic source
code can in principle be evaluated by a sufficiently complete derivation;
this bounded pass does not prove such evaluation impossible. It establishes
that the available construction facts and frozen surface observations do not
instantiate the first projection branch, and identifies its exact missing
inputs. Assuming those transitions in a checker would leave this premise open.

## Smallest next evidence at existing owners

For the first obstruction alone, the smallest discriminating capture is the
owner-issued association `(a, i, b, direct DefId/root)` plus the queried
returned-callback lower records `(owner TypeVar, BoundRecordId, endpoint,
weights, decision)`. Capture the returned `ProjectionDecision` from the actual
evaluation, including its reason/evidence when included; neither support counts
nor `uncovered_claims.is_empty()` substitute for that decision. The association
prevents matching an auxiliary ID or an unrelated effect coordinate.

If this shows a surviving ID route, the smallest next joined observations are:

| Existing owner fact | Why it is needed |
| --- | --- |
| Original-ID occurrences at final selector input: compact path, composed sign, TypeVar, full entry; actual TypeVar quantifiers and `fact_by_id(i)`; installed scheme entries and stack set | Separate projection loss, cleanup loss, live-PUSH selection and All selection. Installed membership alone answers selection but does not explain its branch or identify the PUSH output path. |
| Instantiation for this `observed_direct` use: source scheme key, target map entry, cloned root POP and returned latent-effect path | Join original lineage to the actual fresh use; avoid combining witnesses from separate uses. |
| Provider/use roots, the first demand's argument and returned-value ports, final demand's return-effect port; corresponding effective bounds, dispositions, replay parent/premise edges and exact weights | Distinguish provider absence/subsumption, provider replay, returned-callback transport and cancellation on the later call. Full weights distinguish exact-ID cancellation from same-family filtering. |
| Final call-effect and result-effect lower records before projection, followed by their projection decisions | Distinguish solver loss from final compact/export loss. An independent-provider explanation requires a retained independent route here, beyond scheme quantifier membership. |

This is a staged evidence plan, not authorization to instrument or execute.
Record IDs without paths/owner joins are insufficient. A global solver dump is
not required merely to answer the first obstruction. If the *reason* for a
qualified decision is challenged, retain that evaluator's premise/coverage
slice and decisive formula incidence; reimplementing the kernel with assumed
coverage supplies no independent oracle.

Discriminators are precise: no original-ID projectable route defeats the
proposed direct export lineage at the first seam; no final original-ID
membership defeats its quantified-root-POP explanation; membership without a
mapped later PUSH leaves cancellation unproved; absent provider replay points
to an earlier owner; an independently surviving same-family lower requires
checking whether it is removed on the actual final output route. None of
these outcomes alone certifies or refutes every clause of universal H.

## Evidence quality, checks and resource boundary

The audit is independent source inspection of the operational owners. It
shares the pinned source and inherited binary/source correspondence assumptions
with the frozen probe. It supplies no independent execution oracle and does
not revalidate the probe binary's build provenance. No transition checker,
mutation experiment, new source witness, seed/range enumeration or timing
sample ran. The displayed candidate was inherited unchanged.

Commands: bounded `rg -n`, `sed -n` and policy/evidence `cat` reads;
`git rev-parse HEAD`, Oracle revision/status reads; `sha256sum` dependency
snapshot and recheck. A read-only Python integrity pass matched all 24 frozen
dependency hashes, matched the six Y3 dependencies against the pinned baseline,
and checked final newline, balanced code fences and no trailing whitespace.
Only the leased note was written. No Oracle execution,
instrumentation, compiler edit, test, build, Cargo command, formatter, child
launch or Git mutation occurred. Local shell reads were short, with at most
three concurrent lightweight read processes; heavyweight processes and benchmark
samples: zero. CPU/RSS were not measured. Wall time is not a performance
measurement; no long-running search or timeout occurred.

Unverified: actual record inventory, exact qualified projection evaluation,
cleanup survival, final quantifier membership, actual use map, provider replay,
call/output discharge, all-source H, complete Call, soundness and principality.
Independent review has not been assigned to this note. Writes stop at handoff.

Recommended next action: primary separately authorizes a bounded observation
of the original owner association and actual returned-callback projection
decisions for this exact source. Extend capture only if the returned facts show
the next seam is needed; another surface dump leaves the same premise untouched.

## Frozen dependency snapshot

No read dependency was changed by this worker. Oracle paths are relative to
`/tmp/yulang2-oracle-read`; Y3 paths are repository-relative.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/theory/2026-10-11-oracle-callback-reuse-source-proof.md` | `fd4e57a9cf5ab303cafa64fb0d841c25a57673767f61e331b053f7dcce792b3e` |
| `notes/theory/2026-10-11-oracle-annotation-scheme-identity-proof.md` | `cd9ec15a679c456d81e35a8d9c977a9ddf11bc5f00579b7909e917424d71d215` |
| `notes/progress/2026-10-11-oracle-callback-reuse-projection-probe.md` | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| `crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `crates/infer/src/constraints/structural_kernel/access/legacy_read_view.rs` | `d51ab100c247f34ccf94cd75af2c28e1bf845a9b1a8719780843b02ba2bd35a6` |
| `crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-oracle-direct-projection-owner-audit.md`.
- Baseline: Y3 `afe402a7be1bd0bdfe89a531469927d5788112a2`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; frozen values above require recheck before integration.
- Review status: unreviewed source characterization; original H and actual projection/use premises OPEN.
- Checks already run: scoped source/policy inspection, read-only revisions/status, 24 dependency hashes and six pinned Y3 comparisons, note whitespace/fence/newline integrity; no execution/build/test.
- Proposed checkpoint message: `research: map Oracle direct projection and use evidence owners`.
- Shared-record deltas left for primary/curator: record the first support/formula-state obstruction, actual decision versus payload distinction, both selector branches and final installation seam; preserve H OPEN and dispatch owner evidence. No shared record was edited.
