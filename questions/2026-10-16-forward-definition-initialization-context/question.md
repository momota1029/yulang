# Forward definition demand: initialization execution context

Question ID: 2026-10-16-forward-definition-initialization-context
Question revision: 1
Predecessor/history: source-premise correction 2026-10-16-resumed-definition-materialization, integrated at 1e62dfdc3; this is a distinct foundational context question
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision: runtime 35e87f844; inspected HEAD 66202b0da; later solver change 3be1ae365 is test-only
Task/thread locator: continuing playground/inference/execution completion conversation; stable message URL unavailable
Status: reviewed and pending user decision; no decision presumed

Independent prepublication review: `compiler_referee` runtime_semantic_review
and `spec_auditor` ordinary_carrier_contract returned CLEAN for revision 1.
Their review establishes question coherence/scope, not source proof closure.

## Exact missing rule

A source Name denotes the definition's stored value. If that value is not yet
available because its initializer lies later in the module's root schedule,
which execution context governs the required initialization?

This asks for the original initializer's entry/return rule, including early
dependency timing and handler eligibility. It does not ask how to publish a
definition repeatedly through a reusable continuation.

## Established premises and retained limits

- The approved module-expression design interleaves ordinary root demands in
  source order, evaluates expression roots, and caches completed definitions.
  It explicitly leaves whole typed-source materialization adequacy open.
- The reviewed [Name-role proof](../../notes/theory/2026-10-16-definition-name-computation-role.md)
  establishes a pure value reference and `Delay(original Name)`, retaining
  original value/effect identities. It proves the populated-cache path, not
  the extra empty-cache initialization transition. Name purity alone does not
  decide handler eligibility during synchronous initialization.
- The reviewed [Oracle artifact](../../notes/progress/2026-10-16-forward-initializer-artifact-correspondence.md)
  has different thunk and Int specializations of the same definition. Its later
  root failure supplies no valid example of capturing one pending publication.
- The rejected example from the consumed correction remains invalid. No valid
  cache-bearing Resume witness or unreachability theorem has been established.
  The earlier A/B publication alternatives remain unselected.

Governing sources: the module-expression source-owner design's Runtime handoff;
the consumed correction's approved answer; source-call scheduling choice §§1–2;
Oracle mono contract “Program と roots”; current annotation policy. The
architecture audit found no existing clause specifying this forward-demand
execution context. New semantics require approval under `rules/design-authority.md`.

## Proposed rule: separate module initialization (recommended)

1. An unavailable forward dependency may initialize **when first demanded**,
   before its later scheduled root. The ordinary root cursor is retained;
   that later root uses the completed cache instead of reexecuting the body.
   This makes dependency-first timing explicit rather than assuming it from
   source-ordered root demands.
2. Evaluate the original initializer as a separate module initialization
   demand, using the current shared store and its independently justified
   module/host effect consumer. Handlers installed solely in the suspended
   demanding caller are not eligible for initializer requests.
3. At this materialization entry, the root computation uses its ModuleRun
   context. Genuine Calls, argument Force, function bodies and handler
   installations inside it keep their normal actual owners. The suspended
   caller's owners remain live; this does not reset every owner or snapshot
   and restore the store. The new rule is confined to the previously open
   empty-definition entry/return seam.
4. Handlers installed inside the initializer remain eligible under ordinary
   rules. This does not require pure initializers: any module/host effect
   permission is a separate existing obligation, not supplied by the Name.
   Without an independently justified consumer, an escaping request is not
   made valid by a handler around that Name.
5. On normal initialization completion, publish the stored value and return
   to the original Name/Observe in its caller configuration. Later execution
   of a cached function or computation uses that caller's ordinary handlers.

This selects no signature-keyed global cache, store snapshot, repeated
publication, cancellation/reinitialization or raw-continuation law. Existing
cycle/failure handling is not extended by this decision. Any such additional
issue must retain its own proof and authority gate.

## Alternative: initialize in the demanding context

Keep the same explicit dependency-first timing, but make the demanding caller's
handlers eligible while the original initializer runs. This requires an
independent source rule accounting for the initializer's effects and handler
eligibility; the pure Name interface cannot supply it. A caller handler alone
still does not discharge the definition's original initialization obligation.
Ambient handling does not itself place cache publication in a raw continuation.
This option therefore also leaves the old A/B publication choices unresolved.

## Requested decision and blocked scope

Approve the proposed separate-initialization rule, choose demanding-context
initialization with its required effect-accounting rule, or supply a replacement
for this exact entry/return seam. Both stated alternatives explicitly include
dependency-first timing; a different timing policy needs its compatibility with
approved forward references and ordered root demands stated.

Approval supplies a source rule to prove against the actual constructors; it
does not prove reachability, soundness, handler correctness or production
readiness. Before implementation, derive materialization entry/return, handler
eligibility, current-store preservation, publication and later latent-value
consumption correspondence under the selected rule.

Blocked work: completing empty-global source/runtime correspondence and any
dependent materialization repair. Native inference proof work continues
independently. Keep this directory unstaged/uncommitted until an exact approved
question/draft/answer bundle is validated and integrated by the questioning primary.
