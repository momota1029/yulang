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

## Proposed constructions and resolved source question

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
The subsequent explicit answer is recorded below; this question is no longer
pending.

## Variable binding and block escape clarification

The user answered:

> signalはrelay内で処理されず，answerは変数なのでそれもすり抜けて自由になる（ブロックに出る）．

The [directional addendum, section 2.1](../design/2026-10-06-directional-inferred-effect-protection-addendum.md#21-concrete-relay-and-variable-binding-clarification-2026-10-15)
records this exact source outcome. `signal` must survive relay's Catch and the
variable binding and reach the enclosing block computation.

The saved `hygiene-callback-block.yu` makes the observation explicit:

```yu
my program = {
    my answer = relay signal::ping;
    answer as [] int
}
```

The final ascription checks reading the already bound value. It does not assert
that the whole block is pure. At baseline `8dc4368bd`, the existing playground
binary executed three inputs using `target/debug/yu-playground <source>`,
each with a 30-second process timeout:

| Input | Result |
| --- | --- |
| The block above, with the existing `signal` and `relay` declarations | Exit 0 |
| Same source with `my program:[] int =` | Exit 1, `IncompatibleEffect` |
| Empty-effect block control, replacing the initializer with `1` | Exit 0 |

These are three additional CLI executions; no new Cargo invocation, test suite
or benchmark was run. Scratch sources and output are under
`/tmp/yulang-hygiene-block-45vg22lv/`. The first input is preserved in the new
fixture. Its expected behavior follows the user clarification and the existing
initializer/Name distinction, rather than adopting current output as a contract.

The implementation already routes local initialization effects into the block:
`candidate_source.rs::Work::Install` emits slot 20 from `init.effect` to the
owning block effect before installing the generalized value. A later Name
lookup has its own empty computation effect. Expression ascription checks the
actual child's computation; a definition's root effect annotation checks its
entire initializer. No compiler change is required for this particular escape
route.

The three results establish that the current example exposes this distinction.
They do not establish hygiene: current Catch still forwards all scrutinee
effects. The next behavioral gap remains the distinction between subtracting
an eligible direct effect and retaining the omitted callback's effect, with
the direct-argument and outside-arm controls intact. Paired-pop ordering,
live protection and source-qualified subtraction remain unresolved.

This clarification/fixture slice uses M1 with one independent `spec_auditor`
for faithful decision transcription and observation scope. Review found no
findings; global inference, the paired-pop construction and production
readiness were outside its scope. The saved fixture was also checked byte for
byte against the executed source, and changed Markdown fences and whitespace
were checked. Compiler code and existing test expectations are unchanged.

## Annotated counterparts: selected expectations

The user subsequently supplied two annotated variants, both returning `1`:
`cb: () -> [signal] int` with `catch cb()`, applied to `signal::ping`, and
`thunk: [signal] int` with `catch thunk`, applied to `signal::ping()`.
The complete programs and the user's clarification are preserved in
[annotation policy §1.1](../design/2026-10-10-annotation-effect-hygiene-integration.md#11-annotated-callback-and-computation-arguments-2026-10-15).
The contravariant `[signal]` permits local subtraction and accepts an otherwise
compatible `[signal, write] int` argument; `write` remains outward.

This append-only semantic record uses M0 with one scoped `spec_auditor` for
faithful transcription and scope. Review found no findings. Verification is limited
to document links, fences and `git diff --check`; no compiler changes, builds,
tests, source executions or performance measurements accompany this update.
It establishes expected behavior, not successful native execution.

## Compose: scoped release and identity forwarding

The user then selected the [compose scope-release rule](../design/2026-10-15-compose-scoped-effect-release.md)
and expected output `['e?, 'f] 'b`. Release must reach occurrences of `'e`
inside output effect `'f`, including `f = id`, and remove only the `'e`
scope's protection. Internal push/pop-like processing remains a possible
implementation; the earlier paired proposal is not thereby adopted.

The active compose acceptance criterion is updated under the explicit user
decision and pre-write `spec_auditor` review. Its old factorization discussion
is marked historical; other examples are unchanged. Mode M2, one scoped
spec reviewer; final transcription/supersession review found no findings.
Document-only checks are
links, fences and `git diff --check`; builds, tests, executions and measurements
are not part of this update. No compiler code or proof gate changed.

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
`tasks/research-lab.md` link this record. The later clarification updates the
scoped expected source outcome in the directional addendum; implementation and
proof status remain unchanged.
