# Cycle63: declaration capture and independent head models

Status: Draft implementation boundary, 2026-11-10.

## Objective

Close the semantic bridge from the existing structural declaration-head capture to source-named interval batches: all ordinary models must correspond exactly to one shared mathematical valuation that fits the original heads and preserves all old source demands. A binder valuation is proof-level only; the executable path only retains original endpoints and emits comparisons.

## Data and independent judgment

Use the existing `Form`, `Declaration`, `Goal` and `captureArguments`. A job carries a declaration, an original endpoint goal, and an explicit map from declaration-local binder names to resolved source identities. This map is supplied by the enclosing elaboration boundary; this cycle does not claim to compute the general source allocator. Ambient endpoint slots are a separate `Nat → α` map. Equal binder spelling in different jobs is not automatically source equality.

`HeadFits ambient locals forms arguments` is a recursive conjunction of original endpoint interval membership of each interpreted original head. It does not call capture, constraint generation or the driver. Capture correctness is structural: variables retain both original endpoints, int retains its rigid shape, pair and tick decompose their existing Common subtype rules. The existing capture does not match join heads or unresolved rigid constructors. Repeated variable occurrences are retained and reconciled, not equated syntactically. This does not expand the existing candidate scanner's supported grammar or decide K2 eligibility.

## Theorem shape and shortest chain

1. For every independent `Capture form argument bindings`, every ambient assignment and every local valuation: original head interval membership iff every original captured binding fits the same local valuation.
2. Lift to `CaptureArguments`, then to a role-checked actual declaration capture, lowering endpoints with a caller-provided slot map and names with the resolved source map.
3. For arbitrary old demands and any finite actual capture sequence, generated delta atoms hold iff there exists one mathematical source valuation fitting every old demand and every original head in that sequence. Captures are obtained by the executable collector; no chosen center, solver-success premise or assumed semantic invariant is used at the public entry.
4. Compose with the existing shared presence graph compiler, preserving all existing ordinary atoms, all old demands and literal endpoint/row readback. Reflect every graph model, not just a canonical witness.

The exact independent structural capture boundary remains visible in a return theorem. Failure to structurally capture is outside this kernel, not semantic rejection. General declarations, state-dependent materialization, source-node allocation, complete ordinary solving, saturation and final classification remain open. The five B4 bridges remain incomplete.

## Source comparison

Read `work/dots-audit:notes/audit/x-oracle.md` X13–X16 and C3-PARENT before implementing. These establish motivation for sharing and sibling requirements, not the general theorem below. No new Yulang2 run or semantic choice is needed. The governing existing interval semantics and spec 6.3 are retained.

## Implemented boundary

The partial goal is closed by `CommonRoleCaptureBatchModels`: 13 public theorems connect actual finite capture to independent original-head models and all graph models. Declaration requirements remain in each input job but are not materialized by this collector. The supplied source map must come from the enclosing source boundary; this theorem is exact for every such map, but does not establish that map’s provenance. There is no claim that all mathematical head fits can be structurally captured.
