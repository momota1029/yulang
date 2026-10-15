# Playground initializer handler boundary

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Authority: [approved initialization decision](../design/2026-10-16-initialization-order-global-effects.md),
exact q1/a1 revision-2 bundle `885012b42`, escaping-effect clause only
Mode: M2; local proof plus semantic and specification implementation reviews
Status: local handler-boundary implementation/proof gate complete;
initialization order and whole source/runtime materialization remain OPEN

## Change and constructive correspondence

`Machine::propagate_request` finishes its unchanged top-Catch candidate search,
then stops an escaping request before popping a pending GlobalRead. The same
existing unhandled-request constructor serves this boundary and the old empty
stack case. Inner handlers remain eligible; nested B initialization stops before
A's handler around Name(B). The original event, declaration, payload, operation
source and observations remain authentic. The saved suffix contains only the
already-unwound initializer segment; GlobalRead and the caller prefix stay live.
No initialization marker, owner, execution view, store cell or cache write is
reset, abandoned or published. Normal Return/Observe and later cached latent
execution use their existing rules.

The [constructive stack-cut proof](../theory/2026-10-16-initializer-handler-boundary-preservation.md)
was independently CLEAN at producer
`7157da6cd4bd9d74b22cbfd1ff133a4574ff1948e0e9badb2fc103e86c63c61e`.
Fresh actual-source delta review `runtime_semantic_review` confirms the code
implements it. `ordinary_carrier_contract` returned CLEAN for exact scope and
pre/post test-contract conformance. One minor coverage finding was repaired:
two new internal-handler fixtures use a computed main block, so they actually
enter a pending GlobalRead before the later initializer's scheduled root.
Their expected 19/17 results and assertions are unchanged. Primary inspected
that exact two-line fixture repair and reran both controls before the package gate.

Reviewed machine SHA-256:
`04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c`.
Final runtime_resume.rs SHA-256:
`1c1a4f402c87088454bf31eee2c1eee8d5ff9ec716fe2282ed4fe421b6469859`.
The production source is unchanged since its CLEAN review; only those two new
fixture paths changed after the initial test-delta review.

## Causal test-contract update

The old temporary `captured_definition_materialization_keeps_its_separate_decision_gate_open`
fixture expected ContinuationMaterialization after searching the caller's Catch.
The approved new boundary stops before that search, so the fixture now checks
an authentic UnhandledRequest, exact resolved operation, same-HIR initializer
application occurrence/range and payload 7. Its approved new name is
`forward_initializer_request_does_not_enter_the_name_callers_handler`.
This change had pre-write specification clearance and records the semantic cause;
it does not preserve a now-forbidden search to retain an obsolete diagnostic.
The fixture remains a low-level runtime boundary reproduction, not a valid-source
cache-bearing Resume witness, accepted dependency-first timing or an old A/B choice.

Added controls cover internal initializer Resume and discard, nested initializer
exclusion, later cached function handling, and exact private live-prefix/marker/
owner/view/unpublished-cell/no-caller-template state. Existing pure forwards remain.

## Verification

Primary serialized Cargo work with two jobs and a 180-second timeout per command:

```text
timeout 180s cargo test -p yu-playground --test runtime_resume -j 2
timeout 180s cargo test -p yu-playground --lib initializer_stop_retains_the_cache_write_and_live_caller_prefix -j 2
timeout 180s cargo test -p yu-playground --test runtime_resume initializer_internal_handler -j 2
timeout 180s cargo test -p yu-playground -j 2
rustfmt --edition 2024 --check tools/inference-playground/src/runtime/machine.rs tools/inference-playground/tests/runtime_resume.rs
git diff --check
```

Results: initial runtime_resume 13 passed; private invariant 1 passed; strengthened
inner-handler controls 2 passed; final complete playground package **108 passed,
zero failed, zero ignored**. No warnings or timeout. Logs:
`/tmp/yulang-initializer-boundary-{resume,state,inner,package}-20261016.log`.
No full solver/workspace suite repeated: no shared compiler/dependency code changed.
The package gate is the single broader check for this local tool phase.

Added structural cost is one O(1) top-frame check per request-forwarding fallback;
no successful ordinary-path allocation, stack scan or registry is added. The
terminal path uses its existing suffix allocation. Performance budget consumed:
zero experiments, samples or measurement processes.

## Remaining scope

No automatic global consumer is fabricated from an Act spelling such as io;
without an authenticated consumer this tool reports the existing unhandled error.
The terminal opaque unhandled handle is not a newly resumable global protocol.
No early-entry timing, effect-order detector, arbitrary global-handler registry,
owner switch, signature cache, cancellation or repeated-publication law is added.
The later [approved observation](../../questions/2026-10-16-initialization-effect-order-observation/receipt.md)
selects actual outward initializer effects. The independently reviewed
[current-runtime theorem](../theory/2026-10-16-initialization-outward-order-current-runtime.md)
now establishes at most one distinct escape per fresh public run, none on
completion, and therefore no observed pair inversion. This consumes the selected
boundary without changing code or repeating its 108-test package check.
Full typed-source admission, entry timing/source-prefix refinement, successful
initialization scheduling, whole materialization, general inference and
production/F5 gates remain OPEN. Future automatic global consumption requires
new order correspondence before use.
Current task, research queue, design index, governing decision and consumed-answer
receipt are synchronized with this local gate. Pending questions/draft history
remain outside this commit.
