# R224 — Apply demand to LocalFreshRoute term bridge

## Disposition

The ordinary candidate mode retains terms for both exact LocalFreshRoutes, but
neither route term maps to the provider Apply's native argument, and the
provider argument has no fact/function-structure path to the callback formal
root. Source-to-native correspondence remains open; this is not a semantic
counterexample.

## Exact term evidence

The R221 fixture is admitted in ordinary candidate mode with no solver errors.
The authentic LocalFreshRoute for the actual `loop` Name at occurrence 28 maps
the positive function node with source result-effect Effect(41) to Term(413), a
`PositiveFunction`. The authentic `repeat` Name route at occurrence 27 maps
the callback function node with source argument-effect Effect(31) to Term(386),
also a `PositiveFunction`.

The native interface for Apply occurrence 26 has actual argument Term(452),
which is a positive live Value variable (ordinal 28), and callee Term(451). The
callback Apply at occurrence 19 has native callee Term(258), identical to its
registered formal root. Neither Term(413) to Term(452) nor Term(452) to
Term(258) has a path through all retained constraint facts plus recursively
expanded function components. Term(386) reaches Term(258) only by way of shared
`IntNegative` leaf Term(1) and FactId(44); the generic leaf does not establish
an actual-provider relationship. The two route function terms are not identical.

Thus the earliest absent witness is the actual-argument route term to Apply 26's
native argument term. Existing `RetainedFreshUseMaps.terms` records each route
inside its owner, but no source-owned edge joins the actual loop route to the
Apply interface. The callback route-to-formal relation is separately visible;
it cannot repair the missing provider edge.

## Verification and remaining scope

- `cargo test -p yu-solver --features shadow-apply-candidate r224_apply_fresh_route_terms -- --nocapture` — passed.
- The source/native path audit used ordinary candidate mode with scoped
  experiment disabled. No production behavior changed and no independent review
  is claimed.
- R71, R72, and the original computation-forwarding preservation theorem remain
  OPEN.

## Next evidence target

Inspect the owning ordinary Apply constraint construction and its source event
consumer to determine whether the actual argument endpoint can be paired with
its LocalFreshRoute term map using an existing invariant. If the pairing is not
already justified, document the minimal owner-side evidence required and check
it against the inference design's proof-obligation-economy rules before adding
another retained bridge.
