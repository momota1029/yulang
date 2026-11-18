# Cycle250: mixed owner command compilation

Status: Draft finite executor adapter.

Once handles are registered, compile a request by its stable (root,declaration)
lookup. Generate the raw equations from the returned handle and actual bindings;
keep its post-install Delta as input. Unknown handles fail preparation. Registered
supplies coverage and concrete actual entries supply coherence, including traces
that alternate different owners. Exact target lists remain fixed through those
updates, so coverage does not need to be re-assumed at every step.

The delta is not yet generated or shown complete from an actual source step.
Lookup is not declaration validation. Neither finite request lists nor handle
uniqueness prove source termination or future allocator/public-name separation.
