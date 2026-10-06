# Frozen Oracle source-side producer mechanisms: bounded follow-up

Date: 2026-10-06
Status: frozen, independently spec-reviewed (no findings); bounded historical characterization only
Yulang3 baseline: `1718c8763`
Historical source: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Method: read-only source archaeology; no Oracle execution

## Question and authority boundary

The current open source leaf is query-independent registration of an original
role-indexed Function contract/profile and typed source incidences, followed by
typed capture association preserving the original joint `(nu,K,D)` relation.
The existing [producer archaeology](2026-10-06-frozen-oracle-annotation-call-producer-archaeology.md)
records historical annotation/frame flow and formal-identity call collection.
This follow-up locates additional old-side structures closest to that missing
producer.

Everything below describes frozen implementation mechanisms only. It does not
select or prove Yulang3 meaning, establish Oracle soundness, or authorize
successor rules. Conditional historical metadata and subtype constraints are
not substitutes for the approved source judgment. No claim is made that every
listed branch runs for the selected nested-block candidate.

## Additional historical mechanisms

### Annotation markers retained under formal identity

`crates/infer/src/lowering/expr/lambda.rs:1357–1434` traverses a parameter's
`AnnType::Function` and collects effect-family paths with a function nesting
depth and `PreserveMatchingPath` resume policy. `:897–909` stores a nonempty
contract in `poly.arg_effect_contracts` under the parameter `DefId` for
variable/as-pattern parameters (`:912–916`). The annotation absence branch
returns `argument_effect_contract: None` (`:1252–1264`). The retained poly data
is `path`, `depth`, and `resume` (`crates/poly/src/expr.rs:76–81,147–162`).

This is a durable annotation-to-formal association, but not the current
typed-slot relation: it has no demonstrated full structural type path,
`beta`/`Slots(beta)`, capture/read association, or original joint
`(nu,K,D)` contribution.

### Observed call uppers flow back to a formal's exported Function shape

For annotated parameter contracts, `lambda.rs:1278–1303` connects the
parameter computation annotation and may construct public/erased callable
uppers. The formal's local record receives those fields at `:919–943`. In the
guarded erased-upper path (`tail.rs:603–613`), `record_local_call_upper`
retrieves the local by resolved `DefId`, marks use/nesting, and accumulates
distinct call `NegId`s (`:690–715`). Lambda construction consults that state
when selecting the public argument (`lambda.rs:978–1039`); wildcard argument
and return ports can be filled from observed calls (`:1041–1109`), with nested
return-effect projection behind additional guards (`:1015–1027,1111–1124`).

This is a concrete historical use-to-formal-to-export route. It is guarded by
annotation and frame state, and it consumes call uppers created in the
subtype-producing application path. It therefore does not establish complete
query-independent profile registration, independent admission, typed capture
association, or a source-level correlation theorem.

### Sparse occurrence provenance records structural owners and paths

`crates/poly/src/provenance.rs:1–4,24–97,100–104` defines portable
semantically inert occurrence metadata, keyed by definition/expression/pattern
owner, role, and structural type-position path. Inference registers roots in
`crates/infer/src/analysis/session/occurrence_provenance.rs:15–68`; empty roots
degrade completeness. Generalized witnesses are appended by owner and path at
`:228–322`, then exported with their completeness flags at `:119–181`.
Application expected provenance is registered after application subtype
submission in `tail.rs:552–586`. Generalized whole-scheme completeness is
explicitly `Incomplete` (`crates/infer/src/generalize/provenance.rs:67–78`),
and the root-function collector retains the root argument while skipping the
root return/effect witnesses (`:308–338`).

This provides historical owner/path/provenance plumbing, including explicit
partial-coverage representation. It is a diagnostic/evidence sidecar rather
than the original source contract or a complete static profile inventory;
the post-submission application root also cannot establish query-independent
admission.

## Annotation frame-flow qualification

The prior [annotation/call producer note](2026-10-06-frozen-oracle-annotation-call-producer-archaeology.md)
was independently compiler-referee reviewed. The review found one minor scope
qualification: annotation constraints accumulate only if a current function
frame exists, and the export chain described there applies to a Defined frame.
Historical `tail.rs:1064–1080` treats anonymous frames separately and does not
export their `subtracts` in the same way. This qualification does not change
the characterization of the guarded defined-function path.

## Stop point

These additional mechanisms explain how historical annotation markers, some
use-derived call constraints, and sparse structural provenance were attached
to formal identities and exported shapes. None constructs the current
comparison-independent complete source contract/profile plus typed
capture/rebind/read evidence under one original joint relation. The first
current source producer remains open; these Oracle facts are not premises for
closing it. Existing soundness, principality, adequacy, and production gates
remain unchanged.

Checks: exact historical HEAD verified at the pinned SHA; cited mechanism files
were inspected read-only. No build, test, benchmark, or Oracle run.
