# R89 — method/role syntax triage under the approved grammar

Status: ACTIVE; primary-only diagnostic sprint.  
Branch / baseline: `research/simple-sub-intrusion`, `6eb68efa47a8272981aca84ad091c61e28868f2b`.  
Scope: locate why the experimental parser reports a structural diagnostic for the exact role member signature below, which the Authoritative RLD grammar expresses as an ordinary Binding with a Pattern TypeExpression annotation. This sprint does not implement or approve role resolution, conformance, method selection, HIR, inference, or runtime dispatch.

## Exact input and success

```yu
role Pick 'container 'key:
    type value
    our container.pick: 'key -> value
my answer = 1
```

Success is one of: (a) the diagnostic probe reaches candidate inference/runtime, proving the parser accepted this role signature; or (b) it produces an exact parser-owned source/range and a constructive owner trace showing whether the source is inside RLD authority. If a code correction is indicated, stop and replan with a versioned contract naming the exact write and test paths before editing. Do not suppress diagnostics, admit unsupported HIR, or infer role semantics from names.

Authority: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, RLD-G/RLD-J/RLD-T, especially the role signature composition `our x.eq: T` → ordinary Binding + PatternTypeAnnotation. The type-attached `with:` companion in `attached_impl_pick` is explicitly outside the cited TAI addendum and is not part of this input. R85 remains AWAITING_USER_ADOPTION; its exact member-call semantics are not exercised.

## One authorized probe

Luna owns exactly one CLI probe, with the input above:

```sh
printf "role Pick 'container 'key:\\n    type value\\n    our container.pick: 'key -> value\\nmy answer = 1\\n" | CARGO_BUILD_JOBS=2 timeout 120s cargo run -q -p yu-playground -- --run answer -
```

No tests/builds beyond this command, no code/test edits in this revision, and no second probe. Cargo may compile as part of `cargo run`. Record warnings separately from the parser/candidate result. The previous full stable-core fixture probe had diagnostics at `137..157` (the role signature), `171..171` and `171..376` (the deferred `struct ... with:` companion); R89's reduced input isolates the first site.

## Resources, boundary and closeout

Primary-only cap: 300 seconds, including one command (120-second timeout), owner trace and closeout. No child assignments or Astra. Exact primary writes: this contract, `tasks/agent-loop/current.json`, and `notes/progress/2026-10-19-r89-method-role-syntax.md`. No other path is leased. If the exact parser owner is found and a correction is authorized by existing RLD, return to Luna for a revisioned implementation sprint with disjoint proof/implementation leases and fresh pins; do not edit under this triage.

Falsifiers: treating `struct ... with:` as RLD/TAI-authorized; changing expected output; adding a parser exception based on semantic role shape; claiming parser acceptance proves conformance/inference/execution; or expanding to R85's unadopted dispatch semantics. Preserve the original inference/evaluator and A/B claims and the six OPEN effect-hygiene fronts. At sprint end consult the dispatcher, record the exact result, and keep the tree clean through Luna-only checkpoints.
