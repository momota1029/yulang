# Evidence VM native close invariants

This note records runtime invariants for permission-native close paths in the
Evidence VM. These branches are not generic handler optimizations. They are
semantic shortcuts that are valid only when the signal already carries enough
permission evidence to replace the legacy marker close.

## NativeProviderPair

`NativeProviderPair` skips `close_marker_frame(markers, resume_plan)` for a
`DirectTailResumptive` signal when the signal already carries a provider
guard-boundary permission and the surrounding marker frame has no handler path.

The branch is valid only if all of the following hold:

- the signal is `DirectTailResumptive`
- `EvidenceSignalHygiene` has provider guard-boundary permission
- `resume_plan.handler_path` is absent
- the marker slice has no carry-after-frame `AddId`
- the signal is not using a legacy guard bridge
- the permission transform has no resume delta

All value results, generic requests, routed yields, handler-path marker frames,
carry-after-frame markers, legacy bridge signals, and resume-delta signals must
fall back to the legacy marker close.

## NativeProviderPrefixBoundary

`NativeProviderPrefixBoundary` is the handler-path variant of the same idea. It
is valid only for the narrow prefix-boundary case observed by the shadow stats
on 2026-06-28.

The branch is valid iff all of the following hold:

- the signal is `DirectTailResumptive`
- `EvidenceSignalHygiene` has provider guard-boundary permission
- `resume_plan.handler_path` exists
- `call.hygiene.handler_boundary` exists
- `handler_boundary.blocked == false`
- `handler_boundary.path == resume_plan.handler_path`
- `resume_plan.handler_path` is a strict prefix of the provider permission family
- the provider permission family is exactly the operation request path
- the marker slice has no carry-after-frame `AddId`
- the signal is not using a legacy guard bridge
- the permission transform has no resume delta

This is a prefix-boundary permission exposure. It is not a handler-id equality
rule and must not be generalized to foreign-family or `ProviderEnv` boundaries.

## Regression Guards

The following stats are the first line of defense when changing this area:

- `resume_marker_provider_pair_close_native_hits`
- `resume_marker_provider_prefix_boundary_native_hits`
- `resume_marker_provider_prefix_boundary_legacy_fallbacks`
- `resume_marker_provider_prefix_boundary_reject_permission_family_request_mismatch`
- `resume_marker_provider_prefix_boundary_reject_carry_after_frame`

`permission_family_request_mismatch` and `carry_after_frame` are safety rails.
If they become nonzero in representative workloads, do not widen the native
branch to cover them without a new shadow phase and an explicit invariant.

## Current Remaining Fallback Shape

After `NativeProviderPrefixBoundary`, the representative workloads still have
prefix-boundary legacy fallback counts, but they are foreign-family cases:

- `bench/nondet_20_discard.yu`: `legacy_fallbacks = 840`,
  `reject_foreign_family = 840`
- `examples/showcase.yu`: `legacy_fallbacks = 1644`,
  `reject_foreign_family = 1644`

Those cases are not append-scope `ProviderEnv` blockers. Profiling after the
native prefix close showed:

- `provider_foreign_boundary_with_provider_env_blocker = 0`
- `provider_foreign_boundary_with_any_provider_env` equals the foreign-family
  candidate count
- half of those any-provider-env frames grant the same permission handler, and
  half miss it, in the current nondet/showcase workloads

So the remaining cases are not a simple "skip ProviderEnv boundary" extension.
They are a separate foreign-family / provider-env-placement problem. They must
not be folded into the prefix-boundary branch.
