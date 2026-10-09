# Review: Function-only formal attachment debt certificate

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Reviewed artifact: `notes/progress/2026-10-10-formal-effect-admission-falsify.md`
Artifact SHA-256: `545f71dd9c343e38ed380ec491ef9fb95b13176c7b8aa4b93cb0c1a85e35c659`
Baseline: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`
Role: `compiler_referee`
Status: no blocking, major, or minor findings within the declared conditional scope

## Scope reviewed

The review checked the pinned Oracle source correspondence for
`my knot (f: 'c -> [io] 'c) = f (f f)`: paired annotation construction, shared
`'c`, both application demands, Function polarity, `Neg::Row([],Top)`, concrete
Function lower replay, filter registration and consumption, same-variable
omission, alias subsumption, and natural-count debt recurrence. It also checked
that the certificate distinguishes source-generated constraint structure from
successful parsing/execution and from the prospective successor constructor.

## Findings

The pinned owners support the certificate:

- Paired seed and shared `'c`: Oracle
  `annotation/constraints.rs:124–138,251–283,316–322,363–389,835–845`.
- Both application demands and fresh result `R`:
  `lowering/expr/tail.rs:543–563,855–858`; Function argument reversal and
  result preservation: `constraints/machine/propagate.rs:226–270`.
- The absent argument-effect interface is `Neg::Row([],Top)` at
  `annotation/constraints.rs:492–497`, not `Neg::Bot`; it does not enter the
  `Neg::Bot` passthrough branch at `propagate.rs:234–255`.
- `C -> R` checks/registers its filter and retains POP with All:
  `bounds.rs:630–646,815–831,3174–3255`. Concrete `Pos::Fun` checking does not
  traverse its ports: `bounds.rs:3303–3360`.
- Concrete Function replay survives the inspected alias-only guards:
  `bounds.rs:3450–3470,3648–3709,3814–3830,4274–4317`; terminal erasure does
  not cover Function-to-variable endpoints: `bounds.rs:1799–1808`. Same-variable
  omission at `entry.rs:1101–1105` removes derived `C <: C`, not the distinct
  primitive `C -> R` and `R -> C` aliases.
- Empty-right replay preserves left debt:
  `constraints/mod.rs:3598–3606,3624–3626`; same-ID count composition gives
  the recurrence and finite PUSH challenge:
  `constraints/directed_weight.rs:137–169,290–294,399–404`.

Relevant pinned annotation-test evidence was read, not run:
`annotation/tests.rs:561–625` asserts matching return PUSH, result
NonSubtract, and negative filter construction.

## Limits retained

This closes only the source-local constructor/demand correspondence and the
conditional `C -> R -> C` natural-count debt-growth derivation. It does not
establish ordered acceptance for every source edge, source parsing or runtime
acceptance, all generated paths, successor construction/admission, resource or
proof-terminal guards, equality/reindexing, extrusion/freshening, rollback,
support projection, or returning PUSH transport. No source divergence or full
termination result follows. The current successor's explicit-row refusal was
confirmed at baseline `candidate_source.rs:77–81` and
`candidate_effect.rs:845–847`.

No edits, builds, tests, execution probes, or Git operations were performed by
the reviewer. The reviewed artifact and its dependencies were frozen; no other
reviewer was assigned to this artifact.
