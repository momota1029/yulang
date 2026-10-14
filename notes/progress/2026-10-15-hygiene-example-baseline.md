# Concrete hygiene examples: native baseline and open observation

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Baseline: `9dc31c86294189e2e0929722f39d0d2b50ba0cc0`
Status: executable baseline; no live protection or Catch subtraction implemented

## Requested outcome and authority

The user requested collaborative development from concrete programs and asked
for a working hygiene example. The current scope uses the real parser, source
carrier and private candidate through `yu-playground`. Governing sources are
the top-level inference principles, the directional protection addendum
sections 1–4, and the Authoritative research-playground direction. The
annotation-hygiene integration section 6 result remains withdrawn.

The three baseline examples distinguish direct operation handling, an omitted
callback, and an independently emitted same-family effect in an outside arm.
A fourth example places the direct operation in a callback argument. Their
sources are retained under `tools/inference-playground/examples/hygiene-*.yu`.
Successful execution below means source admission and constraint solving;
it does not mean that the desired hygiene behavior works.

## Executed baseline

The primary built the current source with:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo build -q -p yu-playground
```

The build passed without warnings. Each example was then executed using
`target/debug/yu-playground --intrusion <source>`, with a 30-second process
timeout. The direct, callback and outside-arm cases were also executed with
an explicit `[] int` annotation on their final binding.

| Source | Unrestricted source | Final binding requires `[] int` |
| --- | --- | --- |
| `hygiene-direct.yu` | Exit 0 | Exit 1: `IncompatibleEffect` |
| `hygiene-callback.yu` | Exit 0 | Exit 1: `IncompatibleEffect` |
| `hygiene-outside-arm.yu` | Exit 0 | Exit 1: two `IncompatibleEffect` reports |
| `hygiene-argument.yu` | Exit 0 | Not run |

Seven initial source executions ran. The four saved fixture files were then
executed once each and all exited 0: eleven CLI executions in total.
No effect has been certified as consumed by
these results. Catch currently forwards its scrutinee effect and joins arm
effects separately, so retaining an effect alone cannot demonstrate protection.
The direct case's failed empty-effect check establishes the missing removal
behavior. The graph printer also does not expose a principal effect scheme.

## Discarded diagnostic experiment

A temporary unit test attempted to establish that the exact operation member
from the original callback argument reached the **original template** invocation
row after `relay id`. It used actual source execution and inspected stored
effect-bound ancestry without synthesizing the critical bounds.

Its focused command was:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver \
  --features shadow-f5,shadow-apply-candidate --lib \
  candidate_context::tests::source_callback_direct_argument_member_reaches_original_invocation \
  -- --exact --test-threads=1
```

The discarded assertion was:

```rust
assert!(members.iter().all(|member| invocation_ancestors.contains(member)),
    "the exact direct-argument members reach the original cb invocation Eout");
```

This compiled and failed its new reachability assertion. A second run with
`--nocapture` reproduced the failure and supplied the bounded observations:

- Original argument: `EffectRow(8)`, with `AnnotationMember(0, 0)` among its
  ancestors.
- Original callback invocation: `EffectRow(19)`, whose ancestry contained only
  that row.
- Original `id` entry-to-return relation: `EffectRow(14) <= EffectRow(15)`.

These ordinals describe that experiment only. Fresh use allocates new rows
and remaps effect views/members; raw template identities cannot establish
the corresponding instantiated route. The test asserted an unsupported
template relationship, rather than an approved program-output contract.
This failure does not establish that the compiler is correct, or that argument
effects need not propagate. Correspondence between the original template and
the fresh use remains unresolved.
The independent semantic reviewer accepted discarding this new diagnostic
after preserving its source, assertion and observations. Pre-write specification
review by `spec_auditor` approved that exact disposal conditional on preserving
the complete source, assertion and observations first, and making no compiler
correctness claim. This record and the linked complete source satisfy those
conditions. Existing tests and expected output
remain intact; no family-equality approximation replaces the failed assertion.

The guard-construction note initially overclaimed an original-Eout
source-qualified obstruction. New runtime evidence exposed that correspondence
gap; the review was revised to a major finding. The repaired claim is only a
conditional route argument for a matched instantiated Function comparison.
No native original-Eout counterexample or mandatory repair follows yet.

## Proposed constructions and remaining question

The [guard construction](../theory/2026-10-15-executable-hygiene-guard-construction.md)
and [paired Function-port calculation](../theory/2026-10-15-paired-entry-output-hygiene-construction.md)
are research artifacts, checkpointed in `dc7cd3424`. Neither is an adopted
implementation design. The paired
calculation has an unresolved operational ordering premise: detached replay's
`g;pop` cancellation does not by itself justify a chronological `pop;g` route.
Its independent proof review remains pending.

Read-only inspection of the pinned Oracle found both a special pure-argument
transfer and different concrete/symbolic row consumers. Copying the former
would reintroduce a withdrawn source-shape rule; the inspection does not settle
the native example's final effect.

The primary asked the user to fix one concrete expected observation:
does `relay signal::ping`, where `relay cb` contains `catch cb()`, retain
`signal` outside relay or allow the inner handler to remove the now-concrete
effect? Directional protection of the original upper occurrence is already
selected. The addendum explicitly does not establish blanket protection of
provider events, so the primary has not invented either final result.
This is a pending conversational clarification, not a new approved rule.

## Review, resources and status

Mode: M2 for the bounded source/semantic investigation, with `compiler_referee`
for the conditional construction and `spec_auditor` for experimental-test
disposal. Read-only fixture mapping and architecture investigation ran alongside
the constructive lane. The initial semantic review was superseded by the
runtime-informed major finding. A fresh independent `compiler_referee` delta
review closed the repaired scope finding with no new findings. The separate
paired calculation remains explicitly unreviewed research. No implementation
or parent-proof certification follows from either review.

Verification: one bounded Cargo build, two focused diagnostic-test runs
(both failed), eleven bounded CLI executions. No broad suite, workspace check
or benchmark ran. Benchmark budget consumed: zero samples and processes.

No live protection, Catch subtraction, compiler behavior or production route
changed. H1/H2/U and full hygiene remain open; H3/P and F5 cutover remain
disabled. The meaningful current checkpoint is these reproducible source
examples and the corrected evidence boundary. `tasks/current.md` and
`tasks/research-lab.md` link this record; design authority/status is unchanged.
