# Omitted formal: structural extrusion and the Argument consumer frontier

Date: 2026-10-15
Status: independently reviewed bounded static source derivation; one minor
precision repair integrated; no theorem or parent-gate promotion
Branch: `research/simple-sub-intrusion`
Frozen HEAD: `eb8c607cc4b0191896d3cfa0155841733f0bd3c4`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Lease: this file only; complementary source audit, no delegation
Parent status: H1/H2/U OPEN; H3/P disabled

## Objective and premises

Trace the exact source fixture

```yulang
my outer cb = { my inner x = cb x; inner }
```

from source slots to raw Value rows, negative application demand, actual
extrusion copies and the Function Argument consumer. The result is a bounded
construction-directed characterization, not a proof of hygiene, source-wide
incidence preservation, or complete execution. It supplies the exact dispatch
premise missing from an attempted copy-to-Argument chain.

Authority is [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§1.1 and [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5. Unknown formals remain variables constrained by their uses; constraint
formation does not require prior solving. Retain actual copying occurrences
and their Value associations. Reuse established hygiene with its actual
hypotheses. Canonical equality supplies no annotation grant or source-boundary
identity. The exact omitted-formal protection-position inventory is still
unselected; this note selects no inventory and narrows neither H1 nor U.

Operational dependencies are [effects handoff](../../tasks/effects-handler-next.md)
§§1–5, the [D-only structural certificate](../progress/2026-10-15-omitted-formal-structural-incidence.md),
the [copy-correlation record](../progress/2026-10-15-omitted-formal-copy-correlation.md),
and the [hygiene constructor bridge](2026-10-15-shallow-catch-hygiene-constructor-bridge.md).
The theory copy-correlation and shortened hygiene-bridge paths in the packet
are absent; the linked actual committed paths were used.

Explicit hypotheses for the numbered row derivation below:

1. The exact single-binding fixture above, with the successful parsed shape
   used by `candidate_context_tests.rs::session_with_source` (:370–395): one
   outer formal, one Block/local initializer, one inner formal, one Apply and
   three parameter/local Names; no extra Group or annotation facade.
2. `collect_candidate_mode(hir, true, true)`, a fresh session, empty semantic
   imports and syntax environment, and successful relevant fallible constructors.
3. The pinned source construction order below. Numeric rows are specific to
   this fixture/session layout, not stable semantic identifiers or expectations
   for another program, collector, CLI display, or session.

The previous passing test supplies premise 1's successful source admission;
this pass did not parse or execute it again. Production files are unchanged
from `427d1ff5d`. The sole compiler-tree difference at frozen HEAD is the
87-line test-only addition in `candidate_context_tests.rs`, including its
comparison-identity wording repair. That test is read at frozen HEAD, not
misrepresented as identical to the older production baseline.

## Source-qualified row ownership

`yu-hir/src/module/local_source.rs::slot` (:553–563) assigns consecutive
source-expression slots. Root formation (:381–413) allocates outer Lambda
slot 0 and body slot 1. Block formation (:960–1059) allocates the final Name
slot 2 before local initializer slot 3. `Work::Initializer` (:432–470) makes
slot 3 the inner Lambda and allocates body slot 4. Apply formation (:661–679)
uses that existing body slot and allocates callee 5, argument 6. OperatorChain
and identifier lowering add no further facade for these expressions.

Collection first adds the sole definition Value (`lib.rs:998–1000`,
`:1688–1706`, `:1907–1928`), then `candidate_source.rs:267–284` allocates one
Value/Effect component pair per source expression, in slot order. Dense live
Value ordinals (`lib.rs:10064–10120`) therefore map expression slot i to raw
Value row i+1; parameter recipes follow the eight collected Value components.
Parameter registration in source-slot order gives cb recipe 0 and x recipe 1.
`candidate_endpoint` (`shadow_apply.rs:1412–1425`) maps a Parameter recipe p to
`parameter_live_base + p`, rather than the Name's allocated component facade.

| Source construction | Source slot | Raw Value / endpoint | Initial source level | Owner and use |
| --- | ---: | --- | ---: | --- |
| Definition `outer` | separate root | 0 | 1 | Definition root, distinct from Lambda/domain |
| Outer Lambda | 0 | 1 | 1 | `LambdaRecipe.root_component`; positive Function lower targets this row |
| Outer body Block | 1 | 2 | 1 | Group relation from final Name to Block result |
| Final Name `inner` | 2 | 3 | 1 | Local/FreshUse action; no Apply at this source position |
| Inner Lambda initializer | 3 | 4 | 2 | Positive Function lower targets this row |
| Apply `cb x` | 4 | 5 | 2 | Application result; `ApplySourceInput.result`, negative `native.result` |
| Callee Name `cb` | 5 | facade 6; used endpoint **8** | 2 for facade; 1 for formal | `CandidateEndpoint::Parameter(0)`; positive `native.callee` |
| Argument Name `x` | 6 | facade 7; used endpoint **9** | 2 | `CandidateEndpoint::Parameter(1)`; positive `native.argument` |
| Original formal `cb` | Lambda 0, recipe 0 | **8** | 1 | Original negative outer Function domain child |
| Original formal `x` | Lambda 3, recipe 1 | **9** | 2 | Original negative inner Function domain child |

These are **initial constructor levels**, established by
`candidate_source.rs:377–407,409–416,748–756`; they are not the levels at a
later copying occurrence. `FormalConstruction` authenticates a raw original
Function child at `lib.rs:11372–11389`, independently of a canonical row.
Parameter-Name facade rows 6/7 are allocated but do not replace domain 8/9.

Consequently, under the exact fixture premises, raw5 has a source constructor:
it is the application result, not the argument or either omitted formal's
domain. This advances the earlier record's deliberately unresolved raw5
ownership by a static slot/allocation derivation. It does **not** authenticate
the contextual relation that copied raw5, its direct Function field path, or
the retained pair's eventual consumer. Numeric agreement alone supplies none
of those later claims.

## Exact transition derivation

Write V8/V9/V5 for the original raw rows, with signs denoting their polar views.
Write F− for a negative Function demand, and F+ for a positive Function lower.

1. `candidate_source.rs:602–621` retains source Apply inputs and its recipe:
   callee Parameter(0), argument Parameter(1), result Apply slot 4's component.
   Its checking occurrence is the Apply occurrence at local slot 0. The source
   formal-name registration belongs to cb, not to x or the result.

2. `shadow_apply.rs::admit_candidate_fact` (:1426–1522) checks the retained
   source/recipe fields, resolves callee V8+, argument V9+ and result V5−,
   allocates the invocation Effect row, and constructs

   ```text
   F− = Function(argument = V9+, argument_effect = actual argument Effect+,
                result_effect = invocation Effect−, result = V5−)
   checking task = V8 <: F−
   ```

   `ApplySourceInput.native` retains those actual Terms, demand and distinct
   invocation/application Effects before constraint admission. The authentic
   positive Function for the **inner Lambda** has domain V9− and result V5+;
   it is a separate constructor targeting root row 4. Likewise the **outer
   Lambda** Function has domain V8− and targets row 1. Neither constructor is
   a positive Function endpoint merely because V8 occurs inside its domain.

3. During typed draining, transport and context execution precede
   `dispatch_live_item` (`lib.rs:12315–12340`). After memo/canonical handling,
   dispatch destructures **both** a positive Function lower and a negative
   Function upper (`:12463–12466`). At task `V8 <: F−`, the lower is a Value
   variable, so that destructuring fails even though the upper is a Function.

4. The failed-destructuring branch performs structural-bound extrusion
   (`lib.rs:12486–12498`): extrude F− with Negative polarity to the receiving
   row V8's **current** level. The observed target 1 is consistent with this
   branch. Function traversal (`candidate_extrusion.rs:212–255`) reverses
   polarity on Argument/ArgumentEffect and preserves it on Result/ResultEffect.
   Thus the raw Value ports are V9 and V5. The copying call passes each through
   `value_endpoint` (:230, :247), which canonicalizes it; the actual visits are
   `Visit(rep(V9), Positive, target)` and
   `Visit(rep(V5), Negative, target)`, where `rep` is the live representative
   at that copying call. A child copy is allocated only if that representative's
   level **at the Visit** exceeds target (:83–123). This predicts the polarity
   and raw source ports, but does not by itself identify the observed parent
   rows 9 and 5 or infer copy-time levels from snapshots. Bounds of a visited
   row are also traversed; Parent alone records no field path.

5. Each actual copying Visit calls `retain_extrusion_parent` before inserting
   its one-sided source link. The record (`candidate_intrusion.rs:229–289`)
   retains raw parent/copy, polarity, target, copying occurrence, source set,
   and `effect_algebra.processing` as an optional **TypedPairKey**. The source
   association can qualify an intrusion candidate; it does not itself create
   a FunctionPort dependency. The code explicitly keeps this provenance out
   of the dependency adjacency. Function reconstruction creates F−′ when its
   children changed (`candidate_extrusion.rs:327–363`).

6. If extrusion changes the endpoint, dispatch records a diagnostic edge and
   enqueues `V8 <: F−′`, then returns (`lib.rs:12501–12516`). With no further
   change, `apply_value_task` routes to `candidate_apply_value`
   (`lib.rs:13809–13811`; `candidate_extrusion.rs:811–840`). This stores F−′ as
   a Negative bound on V8 and replays it against existing opposite Positive
   bounds. The extrusion child's diagnostic field is `None`; it is not an
   authenticated Argument edge.

7. `candidate_replay_bound` (`candidate_extrusion.rs:766–809`) forms comparisons
   from the actual lower/upper bounds. A later **positive Function** lower on
   the receiving owner could yield `F+ <: F−′`. Only when a task reaches the
   successful paired Function destructuring, and survives memo/shape gates,
   are four Function children created (`lib.rs:12555–12583`). Argument is
   `negative-demand.argument+ <: positive-lower.domain−`. Result goes from
   the positive lower's result to the negative demand's result. These child
   roles cannot be exchanged.

8. `candidate_step_function_dispatch` (`lib.rs:12701–12725`) admits each child
   before enqueue. `candidate_function_port_admit`
   (`candidate_context.rs:2777–2835`) uses the retained processing **RelationId**,
   applies Swap for Argument/ArgumentEffect, preserves result fields, and
   records `Dependency::FunctionPort { child, parent, field, operation }`.
   This is the authentic Argument consumer incidence. It requires the
   dispatched paired Function comparison, not merely a negative demand or
   one of its extrusion copies.

Steps 1–2 and the row table give a source-qualified Apply construction. Steps
3–8 are code-derived transition characterizations conditioned on actual tasks,
current levels and successful admissions. The existing run's parent/copy
records select candidate copying comparisons by pair key; this pass establishes
no exact runtime RelationId→copy→Argument chain.

## What zero Argument dependencies establishes

The prior same-session test inspected zero retained
`Dependency::FunctionPort(Argument)` entries. Its Argument-inspection loop
therefore had no consumer to authenticate. In that inspected final context,
there is no retained Argument dependency to join to either copy.

This is compatible with ordinary constraint accumulation: the source calls an
unknown formal cb, returns a local Function by Name, and supplies no source
receiving Apply that passes a positive Function into cb. The native Apply
necessarily starts at `V8 <: F−`; that task reaches the structural-bound
branch rather than Function child dispatch. A negative Function demand is
sufficient to copy its argument/result rows, but insufficient to construct
an Argument relation. This distinction removes the implication “copy exists,
therefore an Argument edge was lost.” It does not prove global absence of
future Function comparisons, complete propagation, or correct preservation
through every intrusion/capture/replay route.

There is a second independent authentication frontier. `Parent.comparison`
stores only a pair key, whereas `RelationKey`
(`candidate_context.rs:203–207,2403–2424`) contains pair, context and source
set. Distinct RelationIds can share the pair. Even a future Argument dependency
whose parent has that pair would not uniquely identify the copying contextual
comparison. The bounded D-only reader (:298–377) authenticates a different,
captured FreshUse/optional source-Name route with both Replay inputs and the
original Function/domain child; it intentionally does not authenticate earlier
extrusion. Neither equality of rows nor equality of pair keys extends it.

## Smallest observation proposed to the primary

If the primary needs the exact runtime copy owner, authorize a separate bounded
copy-time observation at the existing structural-bound/copy constructors:

- At the structural extrusion call, retain `context.processing: RelationId`,
  original raw task endpoints and endpoint kinds, source checking occurrence,
  initial extrusion endpoint/polarity/target, and the exact matching Apply's
  already retained `native.callee`, `native.argument`, `native.result` and
  `native.demand` Terms. Keep the original raw constructor identities alongside
  any canonical endpoint used by dispatch.
- At the copying Visit immediately before `retain_extrusion_parent`, retain
  its copying occurrence, parent/copy, **original_level read there**, polarity
  and target, and associate it with the retained initiating RelationId. To
  distinguish direct demand ports from selected bound descendants, record the
  direct Argument/Result child endpoint vector before traversal; any inferred
  direct-path attribution must match those raw endpoints, not row shape.
- Retain the transformed extrusion output and dispatch branch disposition.
  Compare its replay/FunctionPort parent RelationId through actual retained
  dependency edges if a paired Function dispatch later occurs. An absent
  positive Function lower/Argument edge remains an explicit result.

This is a proposed observation, not a representation or production decision;
no instrumentation was implemented. Capturing only pair keys, increasing probe
counts, or printing initial/final levels would leave the same premise untouched.
One recommended next action is this exact bounded observation packet if runtime
relation authentication is needed, after independent review of this static map.
It needs separate test/compiler write authorization and primary-owned execution.

## Evidence, limits and commit packet

Commands used: read-only `git rev-parse`, `git branch --show-current`,
`git status --short`, `git diff --name-only 427d1ff5d HEAD -- crates`,
`git diff --name-only HEAD -- crates`, `git diff --numstat`, narrow `rg`, `sed`
and `sha256sum` on the named dependencies. The compiler comparison showed only
the known test file changed from the production baseline, with no live compiler
diff. No Cargo, parse/executable probe, mutation test, search enumeration,
measurement, network lookup, child launch or Git mutation ran. There are no
seeds/ranges or executable oracle: the independent grounding is the actual HIR,
collector, admission, extrusion, retained-record and dispatch owners. This
static derivation shares their source assumptions and the supplied successful
fixture parse; it is not an independent correctness oracle for those rules.

Budget: one static pass, at most twenty minutes, zero heavy processes and zero
measurement samples. CPU/peak RAM and precise elapsed time were not measured.
Unverified: copy-time RelationIds/levels and selected bound paths, runtime lower
bound inventory, all-path transport, dynamic Receive/Observe, source profile
introduction, H2 protection preservation, U selection/coverage/bypass, full Call,
generic opening, soundness, principality and production/F5. All retain their
original status. No profile-position matrix or source restriction follows.

Pinned direct dependency SHA-256 values:

```text
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
664999082a17e59457f0de7cca21a0cf6be6a968285f95c5e074f320ac576015  crates/yu-solver/src/candidate_call.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  crates/yu-solver/src/candidate_intrusion.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
2d52f3f40fc0bcef76b946c9494e5dce3a4b9e8d0eb97f0ad2036b7303e365d0  crates/yu-solver/src/candidate_context_tests.rs
e6c5aee3e149c15c810282f03d3a827001783cef24a4ee034e6d12934045d5aa  notes/progress/2026-10-15-omitted-formal-copy-correlation.md
28d1d8f30a7bf4a6a80f120ed287db2b8a35ba75972eeb7c76121dd0238c0875  notes/progress/2026-10-15-omitted-formal-structural-incidence.md
712c28cd51089d8c30bddced2134b758041decb2ec88b6bc6c0062a756abe64d  notes/theory/2026-10-15-shallow-catch-hygiene-constructor-bridge.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
```

Commit packet:

- Exact leased path: `notes/theory/2026-10-15-omitted-formal-extrusion-consumer-frontier.md`.
- Baseline SHA: `eb8c607cc4b0191896d3cfa0155841733f0bd3c4`; production baseline
  `427d1ff5daab866fa7d89cb513a077063cc6454d` with the known frozen test-only
  dependency delta above. Changed dependency hashes during this packet: none.
- Claim/review status: bounded static source derivation; independent review
  accepted the stated scope and found one minor raw-versus-canonical Visit
  precision issue, repaired above. No theorem or parent-gate promotion.
- Checks already run: source baseline/live-diff comparisons, dependency hashes,
  and leased artifact whitespace/fence/newline inspection; zero tests/builds.
- Proposed message: `research: trace omitted-formal extrusion to Function consumer frontier`.
- Shared deltas left to primary/curator: qualify raw5 as the Apply-result
  constructor under this exact fixture's allocation premises; record paired
  Function dispatch as the missing consumer premise and pair-key/RelationId
  distinction as an independent copy-identity gap. Keep H1/H2/U OPEN and H3/P
  disabled; preserve the undecided profile positions and all original scopes.
  `tasks/current.md`, `tasks/research-lab.md`, prior progress/theory records and
  indexes were not edited. Writes stop before review handoff.
