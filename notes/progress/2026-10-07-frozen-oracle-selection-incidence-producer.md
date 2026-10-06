# Frozen Oracle selection incidence: source registration and its consumers

Date: 2026-10-07
Yulang3 baseline: `b23405e84d0e314817c30c20c44c0a89ee28e703`
Branch: `research/simple-sub-intrusion`
Oracle checkout: `/tmp/yulang2-oracle-rebuild`
Oracle pin: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: frozen, independently compiler-referee-reviewed research-only source characterization; no findings
Method: bounded actual source/control-path archaeology and local inversion discriminator
Exclusive lease: this note only
Semantic/implementation authority: none
Review: compiler_referee PASS on the bounded source/consumer trace, local conversion discriminator, novelty check, and non-closure boundary; no language-semantic or current-source theorem certified

## Exact current gate and scope

The normalized [DAG](../theory/successor-proof-obligations.md),
`ORIGINAL_ASSOC` at lines 562–571, names the missing source producer:
an inhabited original fiber in `I_orig(X)` with an original static slot,
typed position `p0`, source ownership and complete invocation contribution
covering `F_C(X)`. Its prerequisites are `CALL_TYPE` and `SIG_RULES`;
`ATTACH`, then both licensing directions, remain downstream. The
[constructor derivation](2026-10-07-original-association-constructor-derivation-attempt.md)
minimizes the proof cut to
`call(result(name f),result(name x))`. `H_gen` constructs its source skeleton;
the stronger supplied `H_typed` constructs reached-read transport; neither
constructs `H_assoc`. The [kernel audit](2026-10-07-original-association-source-kernel-audit.md)
finds no introducing clause in its bounded displayed inventory, without
claiming repository-wide nonderivability.

Current governing premises are inferred call views §§1.1–5,
source contracts §§2.2, 3, 10, and directional protection §§2–4. Retain one
original X and `xi=(nu,K,D)`, source/public/internal distinctions, stable
original ownership, Q-independent formation and upper protection without
provider-lower backflow. No language meaning or slot-sharing law is selected.

The distinct historical seam inspected here is **dot-selection registration**:
source syntax creates a typed hidden method demand and an occurrence-keyed
record before method resolution; resolution consumes it, retains selected
endpoints, and source hover consumes the retained result. This traces a
source-generation mechanism rather than the previous signature-diagnostic or
solver-transfer seam. A search of the `2026-10-06`/`2026-10-07` Oracle-note
family for `SelectionUse`, `ResolvedSelectionUse`,
`register_selection_use`, `ApplySelectionResolution`,
`lower_field_selection`, and `lower_synthetic_selection` found no prior
trace. This is a bounded novelty check, not a complete literature search.

## Hypotheses and claim classes

H1: the cited source has the recorded bytes in the checkout whose resolved
HEAD is the supplied Oracle pin. Oracle is non-authoritative historical
evidence; no execution, acceptance observation or semantic rule is imported.

H2: an ordinary unqualified Field tail with a valid DotField token is reached
after its receiver has been lowered, and the special sub-label `.return`
branch does not apply. Source recording is enabled with an available range.
The receiver is a supplied historical `Computation`; no current complete
Call typing/admission theorem follows from that Rust value.

H3: for the inversion discriminator, resolution reaches a method target equal
to the record's `parent`. Compare two local `SelectionUse` records identical
except for `recursive_self_value=None` versus `Some(v_self)`. This is a
bounded data/control witness; two admitted source programs realizing these
states are not supplied.

Established result: an actual historical source-to-registration-to-resolution-
to-display path, with distinct method/result/receiver coordinates. Conditional
theorem: conversion to `ResolvedSelectionUse` is non-injective in the H3
field even though the method-use consumer distinguishes it. No current
`OriginalAssocType_X`, complete row, profile, licensing theorem or source
counterexample is established.

## End-to-end source path

Every code locator is under the pinned Oracle checkout.

1. **Source occurrence.**
   `crates/infer/src/lowering/expr/chain.rs:131–149` recognizes a
   `SyntaxKind::Field` tail and calls `lower_field_selection` for the
   unqualified case. `lowering/expr_syntax.rs:107–113` extracts its DotField
   token's name, removing the leading dot. `lowering/expr/tail.rs:157–170`
   obtains this name and source range before entering the shared selection
   producer. `tail.rs:1113–1123` derives the token range and advances its start
   by one when a dot is present. This is the field-name span, not the whole
   receiver expression or complete invocation span.

2. **Typed producer before resolution.**
   `tail.rs:290–314` allocates fresh `method_value`, `result_value`,
   `result_effect`, and `call_effect`. It constructs and submits

   ```text
   Pos::Var(method_value) <:
     Neg::Fun(arg=Pos::Var(receiver.value),
              arg_eff=Pos::Var(receiver.effect),
              ret_eff=Neg::Var(call_effect),
              ret=Neg::Var(result_value))
   call_effect <: result_effect
   ```

   The supplied origin is `OriginId::internal()` in this ordinary caller
   (`:276–287`). Subtype requests have already occurred before registration;
   this ordering is not a claim of Q independence for every historical rule.
   The typed hidden Function is an old constraint demand, not a current
   complete receiver-invocation contribution contract.

3. **Retained occurrence association.**
   `tail.rs:315–339` allocates a `SelectId`, registers

   ```text
   SelectId -> SelectionUse {
     parent, method_value, selected_value=result_value,
     receiver_value=receiver.value, receiver_effect=receiver.effect,
     local_method_scope, recursive_self_value
   }
   ```

   and separately records `SelectId -> SourceSpan`, then creates
   `Expr::Select(receiver.expr,select)` and returns the selected computation.
   `lowering/expr/mod.rs:193–201` makes the span conditional on recording and
   applies the source-range offset. `uses.rs:146–196` holds unresolved uses,
   source spans and resolved uses in separate maps. Registration does not
   require an already selected method definition.

4. **Scheduled consumer.**
   `analysis/session/lifecycle.rs:224–244` stores the use, records the
   owner's method dependency and enqueues `ProbeSelect`.
   `analysis/session/selection.rs:87–112` reads that same record, probes
   receiver effects and then method-value bounds, and enqueues a resolution
   only if a target is found. The internal candidate-search logic is outside
   this trace; its correctness/completeness is not assumed as current law.

5. **Resolution and retained typed artifact.**
   `lifecycle.rs:1102–1132` writes the resolution into the poly selection,
   removes the unresolved use, stores `use_site.into()` in the resolved map,
   and dispatches by target kind. For a method target,
   `:1136–1148` consumes `method_value` as the hidden method's use endpoint:
   the matching recursive-self case calls
   `constrain_open_use(v_self,method_value)`; otherwise it submits
   `SccInput::UseResolved { parent,target,use_value:method_value }`.
   `analysis/session/instantiate.rs:4–11` implements the first route as
   `Pos::Var(v_self) <: Neg::Var(method_value)` with UnknownInternal origin.
   The other route enters the SCC machine via
   `analysis/session/selection.rs:4–40`. Its later instantiation/generalization
   is not re-investigated here.

   `uses.rs:313–333` shows the exact resolved artifact: it retains parent,
   method/selected/receiver value, receiver effect and local method scope;
   it omits `recursive_self_value`. The removal routine at `uses.rs:192–196`
   removes the unresolved map entry and upper tracking, leaving the separate
   source-span and resolved maps. The nearby comment claiming no resolved
   use is retained is narrower than the actual fields/operations; this trace
   follows executable code, not that stale comment.

6. **Source-facing consumer.**
   `crates/yulang/src/source/mod.rs:3204–3218` finds selections by file and
   source span, then calls `hover_for_select`. At `:4183–4192` that consumer
   dispatches on the retained resolution. A selected method delegates to
   `hover_for_selected_method`, which prefers the resolved selected-value
   hover (`:4232–4235`). `:4196–4214` reads the resolved table and formats
   `selected_value`, not `method_value`. Thus this retained source occurrence
   really joins a source span to a selected result endpoint after resolution.
   Formatting is observation of inference artifacts, not their semantic
   validation or production authority.

The path is source Field token -> typed hidden demand -> SelectId use/span
record -> resolution/method-use connection -> resolved endpoint record ->
source hover. Method, selected result and receiver remain separate coordinates.
No conversion identifies one of these TypeVars or SelectId with a current
original static signature slot.

## Minimal discriminator: retained result cannot invert method-use introduction

H3 is reachable as a producer-state distinction in the code: constructors
initialize `recursive_self_value=None` (`expr/mod.rs:83,129`), while
`expr/method_body.rs:149–170` conditionally installs a recursive-self
Function endpoint during receiver-body lowering and restores it afterward.
Selections inside that body copy the active value at `tail.rs:326`.
This establishes real producers for the two field states; it does not prove
two complete source derivations identical in every other coordinate.

Write U0 and U1 for H3's two records. Direct reduction gives:

```text
ResolvedSelectionUse::from(U0) = ResolvedSelectionUse::from(U1)

apply_selection_method_use(U0,parent)
  -> SCC UseResolved(parent,parent,method_value)

apply_selection_method_use(U1,parent)
  -> constrain_open_use(v_self,method_value)
  -> subtype Var(v_self) <: Var(method_value)
```

One SelectId and one optional-field change suffice. The consumer paths differ
although the retained resolved artifact is identical. This disproves a local
inversion shortcut that reconstructs the original method-use introduction
from that artifact alone. It does not prove a different final inferred type,
acceptance, slot count, effect behavior or semantic observation. Other
retained state may still explain the branch.

Failure conditions: a target different from parent bypasses the distinction;
the absent recursive-self field takes the SCC route; a pre-resolved selection
can return before this consumer; no target leaves registration unresolved.
A mutation preserving recursive_self_value in the resolved type removes
this particular erasure witness. Replacing `method_value` with
`selected_value` in the use consumer changes the demanded port and is not a
permitted coordinate cast. These are code reductions and named mutations;
none was executed or asserted to be a language counterexample.

## Correspondence boundary and next action

This mechanism provides a genuine historical occurrence-to-typed-port
association before method resolution, and its consumers preserve the
method/result distinction. It can inform how to check a proposed source
association without deriving it from a displayed type or final result.
It does not supply the target `OriginalAssocType_X(beta,p0,j_call;s,c)`:
the record has no original static `(s,c)` interpretation, complete invocation
fiber, stage/view licensing inventory or shared original xi. Its target is
also a dot selection with hidden method resolution, whereas the selected
five-node `f x` cut contains no dot selection. Replacing that cut by this
mechanism would change the assigned source, so no such bridge is claimed.

Oracle independence is limited to inspecting real historical code rather
than implementing a checker from the proposed current association rule.
All reductions share the exact historical fields/control rules with their
reference. They validate neither those source rules as current semantics nor
the current independent owner/view kernel. This producer has not independently
reviewed its own note.

Recommended next action: construct the independent original slot/contribution
introduction for the fixed five-node ordinary Call, preserving separate
method/provider, result and source-occurrence coordinates; prove forward
attachment and exhaustive original inversion. Further selection-state probes
would leave that same premise untouched, so this lane stops here.

## Verification, coverage, resources and frozen dependencies

Commands: bounded `cat`, `sed -n`, `rg -n`, `rg --files`, and inline Python
HEAD/ref metadata reads plus SHA-256. Rules read earlier in this assignment
remain byte-identical by hash. Initial aggregate document captures truncated;
the gate and decisive code were reread in bounded windows. A speculative
`analysis/session/scc.rs` locator failed; the actual dispatch was found in
`selection.rs`. No result depends on that failed locator.

No tests/builds, Oracle execution, Git commands/mutations, compiler edits,
formatting, scratch outputs, user questions or children. One new leased note
is the entire write set. No seed/range search, runtime mutation or measurement
sample was run. Heavyweight process count: zero. CPU time, RAM peak and elapsed
wall time were not instrumented; no numeric resource budget was supplied.
Source reads are bounded to the listed producer/consumer windows; candidate
selection correctness, full SCC lifecycle, runtime selection, source-pair
realizability and complete solver output remain unverified. Current
ORIGINAL_ASSOC, CALL_TYPE/SIG_RULES, attachment/licensing, profile/admission,
principality and production gates remain open.

Hashes below fix the inspected bytes. HEAD resolution checks do not establish
Oracle worktree cleanliness; no comparison against packed committed blobs was
performed. The primary can validate those bytes against the pin independently.

| Current dependency | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.md` | `fc5b1c9c72dc0bb262f7cbbd314923fb43c729b7ce33c43a52261150f0ffec4c` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md` | `bfd197a094a6fa3e813325a40c361687ed609ad45aa89af9908f58ce240b5435` |
| `notes/progress/2026-10-07-original-association-source-kernel-audit.md` | `509e9af6be0ae3b3560f1fd7ca8e9c06572bb65e1351b114b0e2e5e13061b202` |

| Oracle dependency | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr_syntax.rs` | `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` |
| `crates/infer/src/lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `crates/infer/src/lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `crates/infer/src/uses.rs` | `e3492318c6cb788097b350f1cd692023ffa7454b8a7c2f8fc448a0293520fdf3` |
| `crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `crates/infer/src/analysis/session/selection.rs` | `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/yulang/src/source/mod.rs` | `0ac0d078323428abf42292e765d2987fb072cc89afb140cb3a86bb98129af3f9` |

## Commit packet

- Exact lease/change: `notes/progress/2026-10-07-frozen-oracle-selection-incidence-producer.md`.
- Baseline SHA: `b23405e84d0e314817c30c20c44c0a89ee28e703`;
  Oracle pin `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed direct dependency hashes: none at freeze; task navigation is
  primary-owned and may move independently of these current governing inputs.
- Review: compiler_referee PASS; the local inversion discriminator remains
  conditional and historical. No theorem gate or implementation authority.
- Checks already run: current DAG/proof-cut identification, novelty search,
  exact source/producer/artifact/consumer trace, direct conversion/branch
  reduction, lease absence and file-integrity/hash/HEAD rechecks. No runtime
  verification or independent review.
- Proposed one-line checkpoint message:
  `research: trace Oracle selection incidence registration and consumption`.
- Shared-record delta left for primary/curator: optionally record this
  historical typed-port association and resolved-artifact inversion boundary;
  leave ORIGINAL_ASSOC and every dependent gate open. No shared file changed.

Writing stops before review submission.
