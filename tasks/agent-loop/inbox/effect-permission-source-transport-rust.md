# EFFECT-PERMISSION-SOURCE-TRANSPORT-20261028/r1 — Rust handoff

Sprint / contract: `EFFECT-PERMISSION-SOURCE-TRANSPORT-20261028/r1`,
`tasks/agent-loop/sprints/effect-permission-source-transport-20261028-r1.md`,
SHA-256 `024c9ac19b1d7658767f2bf5e70bd2bef38c2fdb66326b8e941295777d05606e`.
Assignment: `/root/effect_permission_source_transport_rust`; handoff revision 1.
Outcome class: bounded source-owner classification. Requested role/model/effort:
registered implementer, Luna/high. Observed model/effort: UNKNOWN to this worker
interface. No descendants.

## Intake and exact inputs

The contract was ACKed before analysis. Every listed candidate, owner/dependency,
Lean, and prior-history pin matched at intake. Writable candidate source hashes
were unchanged at stop:

- `crates/yu-solver/src/candidate_effect.rs` —
  `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1`
- `crates/yu-solver/src/candidate_scheme.rs` —
  `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`

The exact read-only pins were rehashed and matched the contract:
`candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`,
`candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`,
`lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
`shadow_apply.rs` `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`,
`Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`,
`FormalPermissionExportWitness.lean` `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`, and
`FormalPermissionExportWitnessNative.lean` `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`.

Reused frozen evidence:

- Prior Rust reachability handoff `d2562c3e8be3ec1633f47adde6add41d4d92bf361b71d25d0eba3582a24cfe5c`.
- Canonical-export Rust handoff `ea9d9e74f383adefb120abcc619c8395404e20f41d0f1acc71764df0fba20d8e`.
- Canonical-export outcome `f3c634072dd5affadc720af11ed3b6b5ec653d370cbc34cf929520323a84bbc5` and fresh review `4961ea42bb3ad09579ecf0bff2899af1b2d229cb4067d86dfcbc3d9508c687d8`.

## Source-to-constraints-to-write classification

The ordinary-source fixture in the pinned candidate test is
`my f(pair:((int -> [io] ()), (int, int -> [io] ()))) = f pair`. Its
`candidate_formal_annotation` constructor selects the live Value row for the
formal parameter and uses that row's level for the recursive formal shape.
For each nested negative concrete Effect row it allocates the permission row
with `fresh_effect_at_level(level)`. The retained permission records the
concrete source operands, owner, occurrence, parameter and full structural
port path. Thus the observed row `r` starts at the same level as its enclosing
parameter Value row in this construction.

The pinned dispatch passes the receiving Value-row level as `candidate_extrude`
target. The pinned extrusion owner branches on the exact nested Effect row's
`original_level > target`: only that strict branch creates a fresh Effect copy
and calls `retain_extrusion_parent`; the `<=` branch retains the original
endpoint and creates no Parent for later qualification. Parent retention adds
an index to `pending` only if a current source event passes
`candidate_source.references.qualifies`; recapture activation has the same
source-reference qualification requirement. Settlement calls the merge writer
for activated pending parents. That writer canonicalizes `(copy,parent)`,
returns when equal, and writes the copy representative's forest link to the
parent representative.

No attributable ordinary-source transition was found in the frozen evidence
that satisfies all of these conditions for this permission row: (1) demand
reaches its nested Effect row with `original_level > target`; (2) the retained
source event qualifies and its pending Parent activates; and (3) the copy-side
write changes `r`'s own representative chain before the result is joined to
independently materialized captured `q`. The existing recursive fixture does
not establish the strict-level branch. Prior canonical-export runs observed
only `r=q`: run 1 `[(19,19),(21,21)]`, run 2 `[(21,21),(23,23)]`. These are
bounded observations, not proof of all-source unreachability. An internal
manual Parent/merge fixture would not supply the missing source route.

Exact first missing transition: an ordinary source demand must reach the
specific allocated nested permission Effect row at a strictly lower receiving
Value-row target, then preserve a qualifying reference through pending
activation so that settlement writes on the copy side of `r`'s representative
chain. The source-demand/level relation belongs to the source construction and
dispatch upstream of the pinned `candidate_extrude` owner. The pinned evidence
does not include an attributable source action/call path establishing that
transition.

## Nested row / annotation / path association

`FormalEffectSite` records the actual nested `SourceEffectRow.position` as
`source_row` and records its formal constructor, owner, occurrence, parameter,
and structural port `path`. `DelegatedTail` and `DelegatedPort` record
`SignatureContext::position()`, which for an annotation is the enclosing
`SourceAnnotation.position`. These are different coordinates. Equality of the
two position values is not a valid join; the canonical-export review also
observed the resulting zero/one delegated site mismatch.

The available frozen events do not carry the source-tree traversal that would
prove the nested row is below the enclosing annotation at the recorded path.
The exact remaining evidence is an AST/HIR walk from the particular
`SourceAnnotation` (keyed by the same constructor and wrapped owner), through
the recorded formal port path, to the `SourceEffectRow` whose position is
`FormalEffectSite.source_row`. The handoff does not infer this relation from
numeric position equality, owner equality alone, or an internal fixture.

## Outcome, scope and budgets

No Rust source edit was made; the diff contribution is this handoff only. No
Cargo/build/check command ran and no scratch path or raw run receipt was
created. The single Cargo slot remains unspent because the required route and
exact attributable inputs were not established. No expected output, semantics,
public API, recovery, preflight or source domain was changed. Existing q,
concrete operand, owner, origin, polarity, capture, node and returned-port
joins remain as frozen prior evidence; they do not fill the missing
source-qualified representative write.

Source/native correspondence, the original parent and A/B claims,
effect-hygiene, principality, termination and production gates remain OPEN.
No new Lean evidence is asserted. Writer STOPPED; all three leased paths are
frozen. New path: this handoff only. No disposable scratch outputs.

Next related in-envelope step: obtain a pinned source-owner action/call path
showing strict lowering of this exact nested permission Effect row and its
qualified activated Parent, or retain this bounded no-route-found result.
Then derive the nested-row/annotation mapping by traversing the actual source
annotation at the recorded structural path. Do not weaken `r != q`, synthesize
a representative, or call the one-shot Cargo command without that evidence.
