# R151 source trace — intrinsic Support through Function ports

Assignment: `R151-SOURCE`; baseline `225c5519943fc490c3d5620683918674f4f6afd5`.
Classification: source-path characterization; not an initialization law, proof,
counterexample, or implementation authorization.

## Exact intrinsic member route

At `candidate_effect.rs:2398–2411`, signature traversal identifies an operation
family only when the current signature node is the declaration's actual
signature. `candidate_signature_effect` at `:2429–2448` creates a one-member
view from that family, retaining `context.owner()`, `context.position()`, and
`context.operation()`; the view has no explicit annotation attachment. The view
is connected to a fresh effect row by `candidate_insert_bound` with the current
polarity. Thus this is an intrinsic operation signature Support member with an
operation origin, not an emitted request or an initialized event state.

`candidate_check_effect_operand` at `:1437–1465` expands a Support endpoint to
`AnnotationMember(view, ordinal)` for every concrete member and separately
enqueues its symbolic tail. The endpoint retains view identity and ordinal;
this does not add inputs or protections to that member.

`candidate_insert_bound` is implemented at `candidate_extrusion.rs:635–643`;
its evidence-carrying implementation at `:702 onward` canonicalizes the
endpoints, appends the selected physical bound, and retains emission evidence.
For an ordinary owner emission the evidence names the currently processing
relation. The emitted bound records owner, polarity, item, and relation
provenance; it has no member-specific `ScopeState` or authenticated event-prefix
field. A retained relation is therefore useful identity evidence but is not by
itself the missing incoming state.

## Function-port projection and FreshUse

At `candidate_context.rs:3924–3987`, Function argument/argument-effect ports
apply `Swap`; result/result-effect ports preserve context. The child relation
inherits `scoped_flow(parent)`. When a source demand is authenticated against
the parent negative Function root, the argument-effect port creates
`stamp_input(demand.input)` and the result-effect port creates
`protect_body(demand.output_scope, demand.input)` (`:3964–3977`). The dependency
retains parent, child, field, and operation (`:3981–3986`). This is an owner-local
transport of an already retained demand. It does not initialize the intrinsic
member from an arbitrary incoming state.

FreshUse at `candidate_scheme.rs:4773–4797` remaps a retained relation's
transformer and demand coordinates using the one `scope_remap`; the mapped
relation is supplied to restoration at `:4888–4907` with that same use origin
and source bound. This preserves a conditional transport route when an
authenticated input state already exists. It does not construct that state.

Structural Value-to-Effect links are explicitly handled separately in
`candidate_context.rs:3456–3479`: the ordinary conversion returns default
`ScopedFlow` for the Effect child. This reset is phase-specific and should not
be removed wholesale. Function-port projection separately consumes an
authenticated demand, above. No evidence in this route proves that a default
flow is the complete ordered prefix of a real provider event.

## Required contrasts and exact gap

The intrinsic operation view is identifiable by operation origin and family.
A latent signature member is an interface operand: Support expansion alone
does not activate it as a request. An explicit annotation Support retains its
annotation attachment/origin and local variance permission, but that permission
does not create actual inflow. Neither contrast supplies the missing
member-to-event input/protection association. Their identity/role distinction
must be retained rather than deduplicated by family.

The first missing construction is before the consumer can evaluate a complete
incoming event state: the retained Support/member and bound/relation route do
not supply an authenticated seed plus complete ordered source prefix for each
actual event. The later Function-port path transports available `ScopedFlow`
and derived demand, while the actual observation helper uses empty sets; neither
is evidence for an arbitrary incoming event state. Therefore this trace does not
justify initializing the member with empty inputs/protections. It also does not
establish a jointly selected/consumed Catch residual; R150 CONSUMER remains a
separate dependent obligation.

This is a conditional source/native boundary, not a claim that every other
bounded Rust repair must stop. The next useful discriminator is a source-owned
event constructor that joins one intrinsic Support member to its actual
provider/event occurrence and complete prefix. If no such constructor exists,
the first missing owner is the source-to-candidate construction boundary before
member evaluation, not the later FreshUse map.

## Checks and limits

All Rust reads used `git show` at the fixed baseline. No dirty Rust diff,
`candidate_receiver.rs`, or quarantined runtime path was read. Six pinned Rust
hashes matched the contract. The R150 proof, source, and review hashes were
authenticated as admitted context. Original rule interpretations and exact
blocker classification remain subject to the separate R151 proof lane and fresh
review. No tests, builds, Lean, execution, scratch/cache, or code changes ran.
Writer STOPPED on freeze.
