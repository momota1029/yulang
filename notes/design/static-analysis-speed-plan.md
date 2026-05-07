# Static Analysis Speed Plan

This note tracks the root-level speed work after the compiled-std cache path.
The goal is to remove repeated analysis work, not to add more local shortcuts.

Current benchmark entrypoint:

```text
bench/static_analysis_bench.sh --repeat 3
```

## Current Hot Spots

The CLI source path is still dominated by `lower`, mostly std source lowering.
The playground embedded-std path should remove most of that std cost, so the
next broad wins are:

- `principal_unify` root/body rewrite duplication;
- name/path/operator resolution during entry/user lowering;
- repeated expression projection/refresh during runtime rewrite.

## Phase 1: Principal Rewrite Observability

Status: started.

Add profile data that answers:

- which call targets are visited most often during principal rewrite;
- whether visits happen from root expressions, binding bodies, interned
  specialization bodies, effect-context bodies, or surviving template bodies;
- how many visits actually rewrite, hit cached incomplete plans, or remain
  incomplete;
- how deep the active specialization stack is for repeated visits.

This is intentionally before structural rewrites. If a target has thousands of
visits but only a few successful rewrites, the next pass should avoid recursive
tree attempts and move that target into one-shot request processing.

## Phase 2: Specialization Request Graph

Target shape:

```text
root/body scan
  -> collect SpecializationRequest {
       target,
       substitutions,
       handler_plan,
       result context,
     }
  -> intern each request key once
  -> rewrite emitted bodies from request queue
  -> rewrite callsites to known specialized paths
```

The important change is ownership: root traversal should not recursively clone
and rewrite every discovered specialization body as a side effect. It should
register requests, then a queue should process each request key once.

Small safe intermediate steps:

- suppress partial callee rewrite attempts when the outer apply spine can make
  the full request;
- keep `specializations` as the request-key dedupe table;
- add counters for skipped partial callee rewrites and verify whether they move
  `root_rw`;
- process specialization bodies from an explicit request queue instead of
  recursively cloning/rebuilding them during root traversal;
- keep block-local rewrite responsibilities inside the block-local context pass
  so large helper bodies do not pay for a scope-poor pre-walk before the real
  block pass;
- profile queued body rewrite by target and expression kind before changing
  traversal shape again;
- if that does not move timings, split `rewrite_expr` into:
  - `rewrite_expr_collect_requests`;
  - `rewrite_expr_apply_known_specializations`.

Success condition:

- `principal-unify-apply` and target visit counts drop with unchanged
  specialization count and unchanged runtime output;
- `root_rw` drops on `examples/showcase.yu`;
- strict-mode behavior is unchanged for incomplete principal plans.

## Phase 3: NameResolvePass Boundary

Target shape:

```text
parse/lower items enough to build scopes
  -> NameResolvePass
       path/operator use -> ResolvedValueUse | UnresolvedValueUse
       type path use -> ResolvedTypeUse | UnresolvedTypeUse
       syntax operator use -> parser-facing operator entry
  -> expression lowering consumes resolved ids
  -> diagnostics consume unresolved refs with original path/use context
```

The pass should not serialize or fake lower state. It is a source-layer
pre-lowering boundary that owns scope lookup, use-search order, visibility, and
operator identity.

First implementation boundary:

- introduce a small resolved-use representation beside `LowerCtx`;
- keep unresolved-ref recording behavior equivalent to the current
  `resolve_path_expr`;
- route only value path expressions through the new boundary first;
- leave operator/type resolution on the existing path until value resolution is
  proven equivalent.

Success condition:

- lowering no longer repeatedly searches locals/modules/use paths for already
  resolved value path expressions;
- `detail.resolve_path_expr` drops on entry/user files;
- diagnostics still report unresolved paths with the same use-path context.

## Non-Goals

- Do not replace inference with a parallel graph solver in this step.
- Do not revive the old demand-driven monomorphize fixpoint as the fast path.
- Do not hide missing principal evidence behind runtime shape inference.
- Do not make std-only assumptions; entry/user dependency files must benefit
  from the same boundaries.
