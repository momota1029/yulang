# SOURCE-OWNER-TRACE-REALIZATION-20261027/r1 — proof handoff

Assignment: `SOURCE-OWNER-TRACE-REALIZATION-20261027/r1`, handoff revision 1.
Contract SHA-256: `71ecc354bcd354396ed9b12ce15b9bb8a0070763b1492b08993fb40a92e44bbe`.
Worker: `/root/source_owner_trace_proof`; registered `lean_prover`; session UUID unavailable. Requested model/effort inherit the primary configuration and are not exposed here; observed model/effort **UNKNOWN**. Sole author: this leaf; no descendants. No Git, Rust, Cargo, tests, dependency/configuration, central-state or other-worker writes.

## Outcome and unchanged parent

**Kernel-accepted finite table instance and conditional application; independent review pending.** The consumer constructs the coordinates for the actual frozen trace, proves all row laws and injectivity, constructs `TableToSource` for every fixture subtree and `TableToDeclaration` for the binding, then applies the existing owner/Identity/application equations using one shared coordinate map. No successful table relation is assumed.

The original complete Yulang inference/executor objective remains **OPEN**, with its supported source domain and quantifiers unchanged. Original source authority is `notes/design/2026-10-08-source-generalize-definition.md` §§2–5 selecting `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5 (and local premises L1–L5 in §2). These define symbolic source rules; they do not supply arbitrary semantic success. The whole-language original claim is `docs/yulang-whole-proof-closure-ja.md` §1 and residual bridges §4. The original Simple-sub preservation claim is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, with the authoritative birth-level correction in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. This finite instance closes none of those parent claims.

Code/dependency baseline: `ba58eb4dcaa9d99280e9398b25a9f0d4f3030ac6`; contract admission commit: `f45fa90d273335b6dea52e9c83e4750418d58664`. Luna explicitly distinguished them. Contract, every listed governing pin, and the complete 31-module local import cone plus three project configurations were rehashed. Accepted schema bytes `[0,13698)` / lines 1–292 remain `266e169aaef8e79c41103fecdc7edae939d9059f49edde2e52ac39ffba4a769e`; the original 13-theorem module remains `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`. Neither was edited.

## Frozen input and exact outputs

Luna acknowledged implementation cessation and trace SHA-256 **before** this leaf read/hash-consumed the trace or launched any Lean/Lake process. Input `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean`: `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a`. Implementation handoff: `tasks/agent-loop/inbox/source-owner-trace-realization-20261027-source.md`, `02422b2b4cd3687aec1cfb10abd0f349c799a14a41bd2b1eb5ccac36d464c700`. It records the authentic Rust owner checks and both Cargo failures/successes; those are implementation evidence, not proof executions by this leaf.

Exact leased repository writes:

| File | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationInstance.lean` | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| `notes/theory/lean/AuditOriginalSourceOwnerReificationInstance.lean` | `0553220072c8291bf8b297bcf13f2e93b279692da2f25f9e22f9daf1677e719b` |
| `tasks/agent-loop/inbox/source-owner-trace-realization-20261027.md` | this frozen revision; hash supplied separately to Luna |

Scratch is exclusively `/tmp/yulang-source-owner-trace-realization-20261027/proof/`: private `project/` and `.lake` cache, `construct_consumer.py`, `run_check.py`, `freeze_handoff.py`, `start.json`, `input-pins.json`, `governing-pins.json`, `theorem-names.json`, `source-token-scan.json`, `axiom-results.json`, `check-01/02.log`, `check-01/02.json`, and final `execution-finished.json`. No root import was changed. The private project copied the pinned source/configuration cone and reused a copy of the prior private cache, subsequently checked by Lake's normal build; no cache was shared for writing.

## Source-to-Lean correspondence and represented cases

`OriginalSourceOwnerReificationTrace.originTable` contains nine physical keys, two formal keys, two administrative wild keys, one statement key, one declaration/binding key and three resolved names. `OriginalSourceOwnerReificationInstance.coordinates` is their actual row-index representation: site indices 0–14, name indices 0–2, declaration index 0. These are formal finite reification indices, never a claim that Rust's provenance ordinal is an `OriginalSource.Site` or that native declaration allocation has been exposed.

`coordinates_constructed` checks the exact result of `constructCoordinates originTable`; `site_rows` eliminates every nested payload of all five SiteKey constructors, covering all fifteen keys. `name_rows` covers all three names; `declaration_rows` covers the one declaration. `coordinate_laws` applies the accepted row-to-injectivity theorem, without assumptions supplying row facts.

The explicit constructor proofs retain both shadowed `x` parameters via parameter ordinal/formal/name-owner joins; all three Name occurrences; both Lambda/formal/wild/name joins; raw Group and projected inner Lambda; the complete actual argument; application; containing block; administrative statement and exact ordered two-entry body; outer fixture; and declaration/physical-definition/name ownership. The statement coordinate remains distinct from its expression's coordinate. Membership is proved from actual emitted rows using kernel `decide`; equalities use `rfl`.

Rust path (evidence owned by implementation): selected ParsedFile source keys → HIR occurrence/formal identities → LocalSource root/ordered incidence and Shadow resolution → frozen typed table. Lean path: table → explicit constructor relations/row-index coordinates → `OriginalSource.Source` → `sourceRules`/`owners` and Identity/application equations. Constraint satisfaction, propagation transport, operational execution and native refinement are not established by this table algebra.

Omitted from concrete closure: actual caller module/import Context allocation; original declaration-coordinate interpretation; source-owner root route/ambient provenance; actual runtime Frame/event payloads; all other source forms and inputs; universal frontend refinement; source semantic L1–L5 instances; Simple-sub A/B; effects/soundness/principality/termination; full Call; receipt/admission; production cutover. Their original source scope is preserved, not reduced to the fixture.

## Parent application and precise remaining owner premise

The new `table_to_identity_source` and `table_to_application_source` connect the **proved concrete table relation** to the same constructed `innerIdentity` and complete application. The eleven `realized_*` roots specialize all accepted owner, registration, body-binding, application, scope and introduction equations; they retain universally quantified `rootContext : OriginalSource.Context`, `rootRoute : OriginalSourceEvents.Route`, and `rootAmbient : List ScopeEntry` where applicable. `realized_introduction_scope_binders` additionally retains the genuine `OwnedFrame s View entry` family as an input, including binder/kind evidence.

First remaining premise / owner: **Luna's caller/source owner must construct and authenticate the actual incoming Context, declaration interpretation, root route and ambient scope from the real module/resolver owner; runtime owner must supply the actual OwnedFrame family for that computed scope.** The emitted `originTable.callerContext = none` is proved by `caller_context_unobserved` and means unobserved; it never justifies an empty Context, route, ambient list or Frame. The finite declaration index 0 does not fill that runtime allocation premise. No counterexample was found or claimed.

Stable TODO `SOURCE-OWNER-CALLER-REALIZATION-1`: original parent unchanged; required input is the actual module/import resolver context and source-event root provenance; proposed output is the owner-authenticated interpretation of those four root inputs, followed by actual runtime frames. Falsifier: mismatched selected module/declaration, foreign owner, wrong root route or missing runtime frame. Dispatch/integration remain Luna's responsibility; this TODO grants no new lease.

## Actual checks and complete axiom results

Read-only `elan which lake` from `notes/theory/lean` resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Actual version outputs: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)` and `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.

Call 1 ran the skill checker with `--project /tmp/yulang-source-owner-trace-realization-20261027/proof/project --lake <resolved-native-Lake> --module YulangClosure.OriginalSourceOwnerReificationInstance --timeout 90.0` and all 28 exact `--theorem` arguments in `check-01.json`. It ran version checks, `lake --no-cache build +YulangClosure.OriginalSourceOwnerReificationInstance` (34 jobs, dependencies plus trace/consumer) and the generated full-type/transitive-axiom audit. Exit **0**, `7.9593264470022405` seconds. Complete log SHA-256 `a6868ac8ba9c07fa237666690ca08135d69d57487d5231c31bad48219acfe41c`; exact command/exit/cwd JSON SHA-256 `44dfbe17018d8483d86c4af7d97cfc99a6b3c6f74bdf2c2bbadbd0889929f2bd`.

Call 2 directly executed the exact leased reusable audit: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 AuditOriginalSourceOwnerReificationInstance.lean`, cwd `/tmp/yulang-source-owner-trace-realization-20261027/proof/project`. Exit **0**, `1.4679426180009614` seconds. Complete log SHA-256 `92b56d59550a6b9d4d98f80e2e2bf8ec71726c3c8e5852cd9e6921fc4e261119`; JSON SHA-256 `8983071eff6e38752e0f73cfc0dd18449a222d7629112d3c175b9b690864fdf3`. The reusable audit checks each declaration is a theorem, prints its full type and `#print axioms`, and rejects all transitive axioms except `propext`, `Classical.choice`, `Quot.sound`.

There were no failed Lean checks, repairs or diagnostics; no additional check was run. The first attempt to read the implementation handoff found it absent during publication, before any Lean process; the later frozen handoff was read and hashed. This transient read failure did not alter any proof/source assumption. Source token scanning found only two ordinary comment words (`admit` in `OriginalCheckingAdmission.lean:816` and `axiom` in `OriginalSourceInterpretation.lean:528`), no proof holes, project axioms, native evaluator or checker bypass in the changed dependency cone. Transitive kernel axiom output, not this scan, is the axiom evidence.

Checks spent: **2/4**, `9.427269065003202` / 240 seconds; remaining **2 checks**, `230.5727309349968` seconds, unused. Processes were serialized, `LEAN_NUM_THREADS=1`, project `-j1 -M1024`; no peak RSS measurement was captured. A process-name observation after completion found no Lean/Lake/Cargo process. Overall leaf startup time was not instrumented; `start.json` timestamps private preparation, and `execution-finished.json` records that measured interval. No unmeasured overall active-time receipt is invented. The finite 1200-second worker envelope was not extended.

All names below are fully qualified in namespace `YulangClosure.OriginalSourceOwnerReificationInstance`:

| Root suffix | Complete transitive axiom list |
| --- | --- |
| `coordinates_constructed` | `[]` |
| `site_rows` | `['propext']` |
| `name_rows` | `['propext']` |
| `declaration_rows` | `['propext']` |
| `coordinate_laws` | `['propext']` |
| `inner_name_source` | `['propext']` |
| `argument_source` | `['propext']` |
| `sibling_source` | `['propext']` |
| `inner_source` | `['propext']` |
| `grouped_inner_source` | `['propext']` |
| `application_table_source` | `['propext']` |
| `body_source` | `['propext']` |
| `fixture_source` | `['propext']` |
| `declaration_source` | `['propext']` |
| `caller_context_unobserved` | `[]` |
| `realized_inner_owner_available` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_local_ambient_kinds` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_target_invocation_binder` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_identity_source` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_identity_registration` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_identity_body_binding` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_application_source` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_application_owners` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_identity_invocation_owner` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_target_scope_from_root` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `realized_introduction_scope_binders` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `table_to_identity_source` | `['propext', 'Classical.choice', 'Quot.sound']` |
| `table_to_application_source` | `['propext', 'Classical.choice', 'Quot.sound']` |

Complete types and complete per-root axiom outputs follow verbatim from the successful direct reusable audit. Kernel acceptance is not independent review, source/native refinement or production authority.

```text
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed
YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed : YulangClosure.OriginalSourceOwnerReification.constructCoordinates
    YulangClosure.OriginalSourceOwnerReificationTrace.originTable =
  Option.some YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
'YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.coordinates_constructed
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.site_rows
YulangClosure.OriginalSourceOwnerReificationInstance.site_rows : ∀
  (key : YulangClosure.OriginalSourceOwnerReification.SiteKey),
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable.siteKeys[YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.site
        key]? =
    Option.some key
'YulangClosure.OriginalSourceOwnerReificationInstance.site_rows' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.site_rows
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.name_rows
YulangClosure.OriginalSourceOwnerReificationInstance.name_rows : ∀
  (key : YulangClosure.OriginalSourceOwnerReification.NameKey),
  (List.map YulangClosure.OriginalSourceOwnerReification.NameRow.key
        YulangClosure.OriginalSourceOwnerReificationTrace.originTable.names)[YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.name
        key]? =
    Option.some key
'YulangClosure.OriginalSourceOwnerReificationInstance.name_rows' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.name_rows
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows
YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows : ∀
  (key : YulangClosure.OriginalSourceOwnerReification.DeclarationKey),
  (List.map YulangClosure.OriginalSourceOwnerReification.DeclarationRow.key
        YulangClosure.OriginalSourceOwnerReificationTrace.originTable.declarations)[YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.declaration
        key]? =
    Option.some key
'YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.declaration_rows
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws
YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws : YulangClosure.OriginalSourceOwnerReification.CoordinateLaws
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
'YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.coordinate_laws
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source
YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
    YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerBody
    YulangClosure.OriginalSourceOwnerReification.NameKey.inner)
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
      YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerBody
      YulangClosure.OriginalSourceOwnerReification.NameKey.inner))
'YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.inner_name_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.argument_source
YulangClosure.OriginalSourceOwnerReificationInstance.argument_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
    YulangClosure.OriginalSourceOwnerReification.PhysicalKey.argument
    YulangClosure.OriginalSourceOwnerReification.NameKey.outer)
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
      YulangClosure.OriginalSourceOwnerReification.PhysicalKey.argument
      YulangClosure.OriginalSourceOwnerReification.NameKey.outer))
'YulangClosure.OriginalSourceOwnerReificationInstance.argument_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.argument_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source
YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
    YulangClosure.OriginalSourceOwnerReification.PhysicalKey.sibling
    YulangClosure.OriginalSourceOwnerReification.NameKey.outer)
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.name
      YulangClosure.OriginalSourceOwnerReification.PhysicalKey.sibling
      YulangClosure.OriginalSourceOwnerReification.NameKey.outer))
'YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.sibling_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.inner_source
YulangClosure.OriginalSourceOwnerReificationInstance.inner_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  YulangClosure.OriginalSourceOwnerReification.innerTerm
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.innerTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.inner_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.inner_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source
YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.group
    YulangClosure.OriginalSourceOwnerReification.PhysicalKey.rawCallee
    YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerLambda
    YulangClosure.OriginalSourceOwnerReification.innerTerm)
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.innerTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.grouped_inner_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source
YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  YulangClosure.OriginalSourceOwnerReification.applicationTerm
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.applicationTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.application_table_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.body_source
YulangClosure.OriginalSourceOwnerReificationInstance.body_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates YulangClosure.OriginalSourceOwnerReification.bodyTerm
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.bodyTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.body_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.body_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source
YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source : YulangClosure.OriginalSourceOwnerReification.TableToSource
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  YulangClosure.OriginalSourceOwnerReification.fixtureTerm
  (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.fixtureTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.fixture_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source
YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source : YulangClosure.OriginalSourceOwnerReification.TableToDeclaration
  YulangClosure.OriginalSourceOwnerReificationTrace.originTable
  YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
  YulangClosure.OriginalSourceOwnerReification.DeclarationKey.value
  YulangClosure.OriginalSourceOwnerReification.fixtureTerm
  (YulangClosure.OriginalSourceOwnerReification.bindingSource
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates)
'YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.declaration_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved
YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved : YulangClosure.OriginalSourceOwnerReificationTrace.originTable.callerContext =
  Option.none
'YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.caller_context_unobserved
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available
YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceOwnerReification.innerOwnerQuery
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient).isSome =
    Bool.true
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_inner_owner_available
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds
YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route),
  List.map (fun entry => entry.binder.kind)
      (YulangClosure.OriginalSourceOwnerReification.localAmbient
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute) =
    [YulangClosure.OriginalSource.BinderKind.description, YulangClosure.OriginalSource.BinderKind.viewLogic,
      YulangClosure.OriginalSource.BinderKind.invocation, YulangClosure.OriginalSource.BinderKind.receipt,
      YulangClosure.OriginalSource.BinderKind.returnRebind, YulangClosure.OriginalSource.BinderKind.shared,
      YulangClosure.OriginalSource.BinderKind.eventProof, YulangClosure.OriginalSource.BinderKind.viewLogic]
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_local_ambient_kinds
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder
YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceOwnerReification.innerOwner
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient).binder =
    {
      site :=
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
          YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerLambda,
      kind := YulangClosure.OriginalSource.BinderKind.invocation }
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_invocation_binder
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source
YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceOwnerReification.innerIdentity
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
          rootAmbient).parameter.source =
    YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
      YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
      YulangClosure.OriginalSourceOwnerReification.innerTerm
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration
YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceEvents.sourceEntries
        (YulangClosure.OriginalSourceOwnerReification.innerContext
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
        (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
          YulangClosure.OriginalSourceOwnerReification.innerTerm)).head? =
    Option.some
      (YulangClosure.OriginalSourceOwnerReification.innerIdentity
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
            rootAmbient).parameter.registration
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_registration
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding
YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  YulangClosure.OriginalSource.lookupBinding
      (YulangClosure.OriginalFormalShared.bodyContext
        (YulangClosure.OriginalSourceOwnerReification.innerIdentity
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
            rootAmbient).parameter)
      (YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.name
        YulangClosure.OriginalSourceOwnerReification.NameKey.inner) =
    Option.some
      {
        name :=
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.name
            YulangClosure.OriginalSourceOwnerReification.NameKey.inner,
        owner :=
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.formal
            YulangClosure.OriginalSourceOwnerReification.FormalKey.inner,
        kind := YulangClosure.OriginalSource.BindingKind.formal,
        entry := Option.some YulangClosure.OriginalSource.Entry.value, singleUse := Bool.true }
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_body_binding
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source
YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
      YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
      YulangClosure.OriginalSourceOwnerReification.applicationTerm =
    YulangClosure.OriginalSource.Source.app
      {
        site :=
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
            YulangClosure.OriginalSourceOwnerReification.PhysicalKey.application }
      (YulangClosure.OriginalSourceOwnerReification.innerIdentity
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
            rootAmbient).parameter.source
      (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
        YulangClosure.OriginalSourceOwnerReification.argumentTerm)
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners
YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  YulangClosure.OriginalSourceEnvironment.sourceCallOwners
      (YulangClosure.OriginalSourceOwnerReification.innerContext
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
      (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
        YulangClosure.OriginalSourceOwnerReification.applicationTerm) =
    YulangClosure.OriginalSourceEnvironment.CallOwner.application
        (YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
          YulangClosure.OriginalSourceOwnerReification.PhysicalKey.application)
        (YulangClosure.OriginalSourceOwnerReification.innerContext
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
        (YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
          YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerLambda)
        (YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
          YulangClosure.OriginalSourceOwnerReification.PhysicalKey.argument) ::
      (YulangClosure.OriginalSourceEnvironment.sourceCallOwners
          (YulangClosure.OriginalSourceOwnerReification.innerContext
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
          (YulangClosure.OriginalSourceOwnerReification.innerIdentity
                YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
                rootAmbient).parameter.source ++
        YulangClosure.OriginalSourceEnvironment.sourceCallOwners
          (YulangClosure.OriginalSourceOwnerReification.innerContext
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
          (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
            YulangClosure.OriginalSourceOwnerReification.argumentTerm))
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_application_owners
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner
YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceEvents.sourceOwners
        (YulangClosure.OriginalSourceOwnerReification.innerContext
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext)
        (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
          YulangClosure.OriginalSourceOwnerReification.innerTerm)).head? =
    Option.some
      (YulangClosure.OriginalSourceEvents.lambdaInvocationOwner
        (YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
          YulangClosure.OriginalSourceOwnerReification.PhysicalKey.innerLambda)
        (YulangClosure.OriginalSourceOwnerReification.innerIdentity
              YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
              rootAmbient).parameter.formal)
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_identity_invocation_owner
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root
YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  (YulangClosure.OriginalSourceOwnerReification.innerOwner
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient).telescope =
    (YulangClosure.OriginalSourceOwnerReification.innerIdentity
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient).ambient ++
      List.drop
        ((YulangClosure.OriginalSourceOwnerReification.innerOwner
                YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
                rootAmbient).telescope.length -
          2)
        (YulangClosure.OriginalSourceOwnerReification.innerOwner
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
            rootAmbient).telescope
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_target_scope_from_root
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders
@YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry)
  (frames :
    (entry : YulangClosure.OriginalSourceEvents.ScopeEntry) →
      entry ∈
          (YulangClosure.OriginalSourceOwnerReification.innerIdentity
              YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
              rootAmbient).ambient →
        YulangClosure.OriginalSourceOwnerReification.OwnedFrame s View entry),
  List.map YulangClosure.OriginalSource.Frame.binder
      (YulangClosure.OriginalSourceOwnerReification.introduction
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient
            frames).telescope.frames =
    List.map YulangClosure.OriginalSourceEvents.ScopeEntry.binder
      (YulangClosure.OriginalSourceOwnerReification.innerIdentity
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute rootAmbient).ambient
'YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.realized_introduction_scope_binders
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source
YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  YulangClosure.OriginalSourceOwnerReification.TableToSource
    YulangClosure.OriginalSourceOwnerReificationTrace.originTable
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.innerTerm
    (YulangClosure.OriginalSourceOwnerReification.innerIdentity
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
          rootAmbient).parameter.source
'YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.table_to_identity_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source
YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source : ∀
  (rootContext : YulangClosure.OriginalSource.Context) (rootRoute : YulangClosure.OriginalSourceEvents.Route)
  (rootAmbient : List YulangClosure.OriginalSourceEvents.ScopeEntry),
  YulangClosure.OriginalSourceOwnerReification.TableToSource
    YulangClosure.OriginalSourceOwnerReificationTrace.originTable
    YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
    YulangClosure.OriginalSourceOwnerReification.applicationTerm
    (YulangClosure.OriginalSource.Source.app
      {
        site :=
          YulangClosure.OriginalSourceOwnerReificationInstance.coordinates.physical
            YulangClosure.OriginalSourceOwnerReification.PhysicalKey.application }
      (YulangClosure.OriginalSourceOwnerReification.innerIdentity
            YulangClosure.OriginalSourceOwnerReificationInstance.coordinates rootContext rootRoute
            rootAmbient).parameter.source
      (YulangClosure.OriginalSourceOwnerReification.LocatedExpression.erase
        YulangClosure.OriginalSourceOwnerReificationInstance.coordinates
        YulangClosure.OriginalSourceOwnerReification.argumentTerm))
'YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourceOwnerReificationInstance.table_to_application_source
```

## Frozen cessation

This revision freezes both Lean files and this handoff for Luna's fresh independent review. All authored repository and scratch writes cease after the final receipt; no descendants or unresolved descendant leases exist. No further Lean/Lake/Cargo/test process or construction is pending. Worker **STOPPED**, review/integration pending; every original parent gate remains **OPEN**.
