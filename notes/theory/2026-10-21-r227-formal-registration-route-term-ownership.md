# R227 — Formal registration to LocalFreshRoute term ownership

Status: closed as a test-only audit. Parent computation-forwarding theorem, R71 and R72 remain OPEN.

## Exact source and observations

The test uses the exact R221 higher-order loop source in ordinary candidate mode. Callback Apply occurrence 19 resolves through the R226 occurrence-to-formal-registration index to registration 2, whose recipe position is 2. Its native root is `Term258`, a positive value live variable with ordinal 31; the recipe at position 2 names the same source parameter.

The `repeat` LocalFreshRoute is the route for local occurrence 27. Its graph rows are `Value(5)`, `Value(17)`, and effect rows; its reconstructed rows are `Value(39)`, `Value(40)`, and effect rows. Neither graph nor reconstructed route rows carries source `Value(31)`. The route does retain `Term377`, also the provider Apply occurrence 26 expected callback function from typed relation 362. In the route graph, `Term377` is the negative function child of the positive callback function term `Term381`.

The callback-body WorkBound demand from source-origin relation 146 is `Term340`; it is not among the route's retained terms. R226 also established that callback-body Apply occurrence 19's demand has no FunctionPort dependency. These facts do not provide an owner-qualified edge from registration 2 / native root `Term258` to route term `Term377`, nor from that registration to the WorkBound demand `Term340`.

## Result and falsifier

The first missing owner fact is the registration-to-route-row/term association: recipe position and native root identify the formal parameter, and the route independently retains the provider expected function, but the route has no row keyed by the registration's source live-variable ordinal and retains no owner-qualified relation linking that registration to `Term377`. This is a provenance gap, not evidence that the native terms differ or that provider/formal forwarding is sound. The executable falsifier for any proposed direct mapping is that registration 2 has root ordinal 31 while the exact route rows omit `Value(31)`; matching function shape or term occurrence alone cannot fill that gap. The callback WorkBound branch is separately falsified as a direct route-term lookup because `Term340` is absent from retained route terms.

The R227 regression test records these checks only. No inference semantics, relation construction, or public API changed. No independent review was performed. This audit does not close R71, R72, or the parent theorem.
