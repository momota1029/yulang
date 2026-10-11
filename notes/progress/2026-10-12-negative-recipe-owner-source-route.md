# Negative residual recipe: internal source-owner route

Date: 2026-10-12
Status: frozen, independently reviewed bounded source characterization; no runtime or theorem closure
Baseline: `62864a09433a012f7739dbf49a57535a70979ba6`
Branch: `research/simple-sub-intrusion`
Producer: primary-assigned researcher leaf; no delegation
Exclusive lease: this file only

## Objective, authority, and hypotheses

Locate an existing internal operation that creates a lineage-owned negative
residual from authentic annotation/filter/Row-upper inputs, or identify its
earliest missing producer and callable consumer seam. This is a static source
audit, distinct from the prior transport/fiber audit. It does not repeat that
audit's transport attack or independently review its result.

Authority is [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, including §3.1; [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
“Selected policy”; and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and “Authority and integration”. General concrete-formal admission stays
disabled. The retracted callback scheme supplies no expected result. Blanket
abnormal restoration is not an inferred prerequisite.

Inputs include the frozen [delivery audit](2026-10-12-negative-recipe-delivery-falsifier.md),
[transition characterization](../theory/2026-10-12-y3-negative-residual-transition-proof.md),
and [negative owner equation](../theory/2026-10-12-negative-filter-rule-proof.md).
Their conditional premises remain conditional. Static conclusions below assume
the pinned bytes and the inspected candidate feature path. Hypothetical call
results additionally assume valid IDs, completed owners and successful
allocation. Authentic negative view creation, residual reduction, complete
replay/drain, and attachment-to-contribution licensing are not assumed.

## Decisive route and earliest missing operation

No inspected route jointly produces `lambda,J,kappa,g,beta,pi_t` and live
`F_lambda = u <: Row(J,g) @ beta`, `P_lambda = g <: t @ pi_t`.
The earliest internal obstruction is **negative annotation effect formation**,
before any recipe activation:

```text
resolved SourceAnnotation / SourceEffectRow
  -> candidate_source::execute_candidate_action (candidate_source.rs:660)
  -> FormalAnnotation: candidate_formal_annotation (candidate_effect.rs:1073)
     -> candidate_formal_pair (:1034)
     -> candidate_formal_effect_port (:1054)
  OR annotation/ascription/local annotation -> candidate_signature_value
     -> candidate_signature_effect (:1447)
  local annotation also passes preflight_local_annotation (:1131)
  -> when reached, composed-negative concrete guard rejects before x lookup
```

The formal pair guard rejects negative concrete rows at `:1035`; its effect
port accepts only omitted, singleton-symbolic, or composed-positive explicit
rows. The general signature guard at `:1507–1509`, when reached, independently
rejects negative concrete before `candidate_formal_effect_variable(:979)`
resolves `(scope,name)` to `x`. With no concrete atoms, its negative branch at
`:1530–1538` returns the bare symbolic row or empty/bottom leaf. The local
annotation constructor also calls `preflight_local_annotation(:1131)` before
signature construction. Thus bypassing source scheduling preflight alone is
insufficient; an internal route must account for both guards and the local
constructor check. Source scheduling preflight (`candidate_source.rs:117–132`)
is a separate source admission gate.

Original information is retained: HIR `source_annotation.rs:68–93,350–375,
505–561` records annotation owner, exact row occurrence, resolved concrete
operands and symbolic names. On admitted paths, the scoped binder map retains
the original variable. No information-loss claim follows from failure to
construct the negative action.

### Why existing private helpers do not complete the route

`candidate_signature_view(candidate_effect.rs:733)` accepts a supplied head
vector, optional tail and `AttachmentSource`; it can retain scope, composed
polarity and member ordinals through `context::State::source_weight(:2174)`.
There is no polarity guard in that low-level helper. However, its actual
negative-concrete signature caller is blocked above. More decisively, every
open view has `closed_weight=None` (`candidate_effect.rs:758–762`), even when
`source_weight` retains its attachment. `candidate_context_source
(candidate_context.rs:2488)` reads only `closed_weight`, so this open view
introduces no executable filter context. The closed zero-word validator at
`:2649–2656` also requires `boundary.closed_weight == Some(weight)`.

`candidate_copy_effect_view(candidate_effect.rs:806)` can copy an existing
attachment and retarget its tail; it does not change its composed polarity or
create a negative continuation or residual. The direct convenience
`candidate_effect_view(:724)` is `cfg(test)`, and is outside this packet's
authorization. Neither helper is an authentic negative producer by itself.

The smallest structural discriminator is one supplied open view
`v=(C,Some(x),source_weight=s)`: its seed context is identity, and a concrete
`E in C` reaches `candidate_check_effect_operand(:918–948)` and returns
without a `q <: x` emission. Thus this open-Allowance path cannot implement
the required checked-filter continuation merely by assigning negative metadata
to `s`. This is a conditional derivation from actual statements, not a reached
source execution, global deletion claim, or fresh same-family attack.

## Genuine Row-upper demand and the second seam

A negative `FILTER(C)` continuing to annotation binder `x` is distinct from
a demand `u <: Row(I,t)`. Only the reached demand supplies `I` and its actual
tail `t`; neither may be reconstructed from `C` or a chosen binder. The native
rule still needs the actual operation context and licenses before determining
the residual branch and `J`. When `t != x`, any consequence `g <: x` requires
the retained directed/contextual bridge from `t` to `x`.

The callable dispatch route for an actual candidate effect task is:

```text
enqueue_task / enqueue_item (lib.rs:12826,12836)
  -> candidate_enqueue_evidence (candidate_effect.rs:403)
  -> candidate_context_admit (candidate_context.rs:2534)
typed drain (lib.rs:12057 or :12269)
  -> candidate_context_execute -> candidate_context_execute_relation (:2744)
  -> dispatch_live_item (lib.rs:12323)
  -> apply_effect_task (lib.rs:11685), if not current and not consumed
  -> candidate_apply_effect (candidate_extrusion.rs:840)
```

For a row lower and supplied headed `Allowance(I,Some(t))` upper,
`candidate_apply_effect` currently inserts the upper on `u` and replays it.
It does not inspect the retained operation to compute `J`, allocate a gamma,
or construct correlated F/P. For non-row concrete lowers it calls
`candidate_check_effect_operand`, whose head-match/tail-forward arms perform
no residual creation. The existing endpoint alphabet (`lib.rs:755–768`)
contains no residual consumer identity. A search for `ResidualRecipe`,
`constructor_lineage`, and `residual_recipe` in `candidate_*.rs` found no
definition or call. This is bounded absence evidence, not a whole-repository
impossibility proof.

The second missing operation belongs where the reached contextual row demand
is processed: `candidate_apply_effect` together with the context execution
owner, before reducing the supplied demand to generic Allowance acceptance.
The exact F/P contexts must be outputs of that same operation, rather than
separately chosen input contexts. Native live weights currently have empty
left words and right POP words (`candidate_context.rs:113–137`); the detached
unit-PUSH adapter at `:2200–2215` supplies no live residual rule. The Oracle
formula retained in the prior proof note is evidence about Oracle, not an
implemented Y3 equation.

## What relation installation already supplies

The next constructor can reuse existing owners for physical bounds and
context fibers, subject to its own proved association and activation:

| Owner | Actual retained output | Missing residual association |
| --- | --- | --- |
| `candidate_bound_origin_with_evidence`, `candidate_effect.rs:420` | Joint `(BoundKey,origin,RelationId,cause)` admission through `candidate_context_bound(:2814)` and evidence `admit(:530)` | The same authentic constructor lineage owning both F/P and its actual demand/attachment license |
| `candidate_context_bound`, `candidate_context.rs:2814` | Post-check parent context, Derived dependency, attached relation fiber | Residual reduction's jointly produced `beta`/`pi_t`; generic fallback cannot invent them |
| `candidate_insert_bound_with_evidence`, `candidate_extrusion.rs:406` | Canonical physical bound and exact emission slot | Replay invocation and semantic completion |
| `candidate_apply_effect`, `candidate_extrusion.rs:840` | Insertion followed by `candidate_replay_bound(:763)` | Actual lineage consumer and joint F/P construction |
| `candidate_context_begin_replay`, `candidate_context.rs:2911` | Ordered lower/upper fibers and Replay dependency/context | Recipe applicability and consumer discharge |

This is more than origin-only retention: evidence admissions are grouped by
`(BoundKey,RelationId)` (`candidate_context.rs:551–565`). Their authentication
gaps remain explicit and the records are inert. No Cartesian product of
independent origins and fibers is justified. The prior transport finding is
not rederived here.

For a *supplied* feedback upper, completed `candidate_apply_effect` plus replay
visits existing opposite lowers; later completed lower application visits that
upper. `State::attach(:2409)` itself only adds a relation fiber and schedules
no replay. The closed registration owner at `:2776–2795` explicitly replays
an existing upper after adding its occurrence. Thus installing both bounds
or attaching F/P does not by itself establish activation. A future residual
owner must explicitly activate each source-owner/lineage pair using applicable
current fibers and each future insertion; ordinary helpers are conditional
infrastructure, not proof that this owner exists or every recipe is delivered.

`RelationKey=(pair,context)` retains no separate residual lineage. Correlated
F/P derived from one creation need an owning association surviving allowed
structural sharing; equal rows or contexts cannot establish that association.
This note selects no new endpoint representation and does not reattack
lifecycle transport, capture or intrusion.

## Old route, private opportunity, and handoff

The old route supplies a covariant headed-row view, optional symbolic tail,
closed-filter execution and ordinary bound replay. Those operations do not
form an executable negative filter or a lineage residual from authentic
negative inputs.

The exact new private opportunity under attachment/admission §§3–6 is the
coupled source-owned internal constructor/consumer slice: resolve original
`x` and attachment at the negative signature/formal effect owner; construct
its checked continuation; then, only for an actually reached residual Row
demand, apply the proved joint equation and retain/activate its F/P lineage.
Existing source preflight can remain disabled for general concrete formals;
the internal callable owner can be implemented independently of broad HIR
admission. Removing guards alone, adding unused recipe metadata, or copying
an open positive view does not implement that slice.

This is a source correspondence handoff, not implementation permission from
this researcher. Top-level principle §3 still requires the central native
equation/invariant before its dependent implementation strategy. A smaller
provisional internal constructor slice may establish the missing source
evidence only when the primary explicitly authorizes its exact code/test
scope; its dependent gate remains OPEN.

One recommended next action: the primary should pair the prover's native
negative filter/residual equation with an explicitly authorized internal
constructor/consumer packet at the two seams above, retaining source
preflight and general concrete-formal admission as later gates.

## Checks, resources, and omitted coverage

Commands: bounded `cat`, `rg`, `sed`; read-only Git HEAD/branch/status and
`git show <baseline>:<path>`; in-memory Python SHA-256 comparison. Initial
combined captures included truncated task/status/source output; all governing
sections and decisive owner statements were subsequently read in bounded
captures. Search coverage is the named HIR annotation and private candidate
effect/context/source/extrusion owners and their live dispatch seam. No
exhaustive caller inventory or full task-history read is claimed.

At most three lightweight reads ran concurrently; subsequent dependent reads
were sequential. No temporary files, builds, tests, Oracle run, transition
checker, runtime mutations, seeds/ranges, timing samples, child agents, Git
mutations or shared-record writes. CPU/RAM and cumulative subprocess count
were not measured; inspection remained within the assigned 30-minute wall
budget. Only this leased note changed. An independent `compiler_referee` review
found no blocking or major issue and identified two minor route-precision
corrections: the local constructor rechecks `preflight_local_annotation`, and
`dispatch_live_item` runs before its current/consumed guard on `apply_effect_task`.
Both are reflected above. Review does not certify source reachability, the
native residual equation, H, soundness or principality. Writes stop here.

Oracle independence: the negative-operation distinction is inherited from
the frozen prior proof, while the present obstruction follows directly from
Y3 constructor and consumer statements. No separate Oracle execution validates
Y3. Shared assumptions are pinned source bytes, valid/completed hypothetical
calls and unchanged meaning; no checker assuming transitions was used.

Omitted: non-nullary effect operands, all lifecycle transport and replay
callers, branch mutation/runtime reachability, reverse gamma feedback,
generalization, unsupported recursive context classes, source admission,
whole Call/handler execution, soundness, principality, and F5 cutover. A new
negative constructor or residual branch, changed live weight alphabet, or
changed association/activation owner invalidates the corresponding absence
claim and requires a narrow recheck.

All complete-file dependencies below matched baseline bytes:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/progress/2026-10-12-negative-recipe-delivery-falsifier.md` | `357404e0ccac2e01cc0900798d5dcecb70b3531357732231b2541833dc4bd0c0` |
| `notes/theory/2026-10-12-y3-negative-residual-transition-proof.md` | `4a29e91ed916ecb87584f063e4c5885f7e19cb6a5706357c64e4557bc1ca2893` |
| `notes/theory/2026-10-12-negative-filter-rule-proof.md` | `9052ecb544ae378fe63c958023e564bdf0edc185e18aec74a07a9973f452f9f2` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |

## Commit packet

- Exact completed lease: `notes/progress/2026-10-12-negative-recipe-owner-source-route.md`.
- Baseline SHA: `62864a09433a012f7739dbf49a57535a70979ba6`.
- Changed dependency hashes: none; complete identities above.
- Claim/review: independently reviewed bounded source characterization and
  conditional structural discriminator; original negative recipe, H and
  implementation gates remain OPEN. No runtime result claimed.
- Checks run: exact owner reads/search, baseline SHA-256 comparison, leased
  artifact relative-link/whitespace/final-newline and dependency recheck;
  no builds/tests/Oracle/runtime experiments.
- Proposed checkpoint message: `research: map negative recipe source constructor and activation seams`.
- Shared-record deltas intentionally left to primary/curator: record negative
  signature/formal construction as the earliest missing operation; separate
  supplied headed Allowance from checked filter continuation; keep actual
  demand tail `t` distinct from binder `x`; record correlated lineage/F/P
  construction and explicit activation as remaining source-owner evidence.
  No shared task, theory map, index, authority or question record was edited.
