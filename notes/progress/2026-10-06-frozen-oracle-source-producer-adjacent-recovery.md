# Frozen Oracle source-producer-adjacent recovery mechanisms

Date: 2026-10-06
Status: frozen research-only historical characterization; independently compiler-referee-reviewed, findings closed
Yulang3 baseline: `b9237483b47cfe9745e0ba21e6995a29af1fd6ce`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Semantic and implementation authority: none
Review: compiler-referee found one major discriminator mismatch and one minor state-label overclaim; the two-edge discriminator and bridge-discovery wording were repaired and delta-checked, then the remaining local wording was corrected by the primary.

## Question and result

The current missing source producer is the original source-owned
`Attach_C(X,e,t)` clause for signature contribution licensing, with sound
forward construction and exhaustive rooted inversion on the same original
`xi=(nu,K,D)`. The existing Oracle archaeology already found source
application/frame grouping, source-boundary ownership classification,
annotation feedback, post-projection claim certificates, and sparse
occurrence provenance.

This bounded follow-up found two additional historical mechanisms adjacent to
that gap:

1. An explanation consumer can recover body-requirement origins below a
   caller-selected parameter bound through exact generalized-witness paths
   and scheme-instantiation bridges. Its deduplication key discards distinct
   witness paths when they reach the same `(instantiation, origin)` pair.
2. Generalization can emit explicit recursive-bound witness paths, and use-time
   instantiation reconstructs the recursive constraints with coordinated
   variable freshening. The inspected witness projector has no matching
   `RecursiveBound` path case, so such a supplied complete witness is counted
   incomplete and omitted from the mapping.

These are historical provenance consumers and preservation mechanisms, not a
pre-query source constructor. They show how some identity was recovered and
where it could be lost. Neither constructs current `Attach_C`/`Lic_C`, a
complete `beta/Slots(beta)` profile, typed owner/receiver/path incidence,
independent admission, or both licensing coverage directions. Frozen Oracle
semantics and outputs are not premises or authority.

## Governing boundary

The current binding sources are [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [directional inferred-effect protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4, and [source contracts/common allowance](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2, §3 opening, §6.1 and §§8–9. The exact open constructor and its required
same-row soundness/inversion directions are stated in
[original signature licensing](2026-10-06-original-signature-licensing-construction.md).
No approved rule was reopened. Oracle implementation details below do not
choose a source role, effect rule, slot quotient, admission predicate, or
evidence lifetime.

## 1. Body-requirement recovery through a callee parameter bound

All locations are relative to the pinned Oracle tree.

`constraints/mod.rs:3118–3148` represents a generalized scheme record and
witnesses. A witness retains its scheme, generalized type path, role, incoming
derivation and completeness. An instantiation derivation names an
instantiation, source witness and path. The explanation layer's
`ParameterBodyRequirementWitness` additionally retains that instantiation,
generalized witness, path, role, origin, source boundary, requirement kind and
graph path (`constraints/explain.rs:442–451`).

The consumer `project_parameter_body_requirements` is anchored by a specific
producer constraint and caller-selected parameter bound. It rejects missing
or unreachable anchors, discovers scheme-instantiation bridges reachable
below that bound, and checks exact witness-ID/path equality before traversing
the witness explanation (`explain.rs:454–525`). The traversal stays within the
selected bridge and does not cross a nested instantiation edge. A reachable
`BodyRequirement` origin with a source boundary can then be reported together
with its witness path (`explain.rs:2249–2310`). It does not scan a global list
of source leaves and select an arbitrary origin.

The recovery is not occurrence-exhaustive even under a supplied graph. The
collector's shared `seen` set is keyed only by
`(SchemeInstantiationId, OriginId)`; the inserted record includes the
generalized witness and path, but these are not part of the deduplication key
(`explain.rs:480–482,2254–2255,2279–2289`). A bridge derivation identifies one
source witness and one path, so the discriminator needs two distinct
reachable bridge edges. Assume they carry `(I,W1,P1)` and `(I,W2,P2)`, with
`P1 != P2`; each edge exactly matches its own witness and both witness
explanations reach the same located body origin `O`. The first collector emits
`(I,O)` and the second is suppressed. Distinct origins or instantiations
avoid that suppression; changing only the witness or path does not. This is a
conditional representation-level discriminator, not an accepted-source
counterexample.

The returned state is also weaker than its name may suggest: the implementation
sets `MatchedSchemePath` whenever the reachable bridge list is nonempty
(`explain.rs:514–525`), even if a bridge's witness is absent or fails the exact
path check and is skipped (`:483–503`). The state records bridge discovery;
successful local recovery requires an emitted requirement. A nonempty bridge
list can therefore return no requirements.

Capture is already partial before this consumer: whole-scheme provenance is
marked `Incomplete`, and witness, incoming-edge and path-depth budgets are
bounded (`generalize/provenance.rs:19–21,67–78`). The explanation can also be
truncated or lack exact anchors. `MatchedSchemePath` only reports a nonempty
reachable bridge set; neither that state nor local recovered requirements
establish exhaustive source licensing.

## 2. Recursive-bound witness projection versus reconstructed constraints

Generalization can create `RecursiveLowerBound` and `RecursiveUpperBound`
witnesses at `RecursiveBound(index)` paths, but marks these drafts incomplete
(`generalize/provenance.rs:45–64,67–74`). At use time one instantiator
coordinates freshening through its shared variable map and clones quantifiers,
recursive variables, the predicate and role predicates
(`instantiate.rs:620–648,732–738`). The Scheme stores recursive bounds as a
side table of variable/bound pairs (`poly/src/types.rs:17–33`).

The projector recognizes a singleton `RecursiveBound(_)` path as belonging to
the legacy mapping category (`instantiate.rs:219–227`). It then calls
`project_path`; that path interpreter covers Function ports and several
structural forms, but has no `RecursiveBound` arm and ends in a wildcard
returning `None` (`instantiate.rs:258–495`). Thus, under supplied state with
one complete recursive-bound witness whose path is exactly
`[RecursiveBound(0)]`, it is counted as incomplete and no witness mapping is
emitted (`instantiate.rs:228–242`). One bound, one complete witness and one
path step suffice for this branch derivation. The normal emitted recursive
witnesses are already marked incomplete, so this is a conditional
representation discriminator, not a claim that the current normal producer
emits a complete instance.

Meanwhile `clone_recursive_bounds` still clones each bound, projects its lower
and upper sides, and submits both constraints under `OriginId::unknown_internal()`
(`instantiate.rs:1002–1030`). The same-use freshening preserves repeated
symbolic-variable identity, but this reconstruction does not recover the
original source contribution identity through the omitted witness mapping.
This is not proof that other sidecars or callers cannot retain more identity;
it is the exact boundary of the inspected path.

## Relation to the current missing producer

The two mechanisms clarify distinct downstream steps:

| Historical mechanism | Preserves | Does not construct |
|---|---|---|
| Parameter-bound explanation recovery | Some source-bound body origins tied to a particular generalized witness/path and use | Original pre-query contribution licensing, all occurrence-to-slot incidences, or exhaustive inversion |
| Recursive Scheme freshening and bound replay | Shared fresh-variable identity and recursive bounds at a use | A source-owned recursive contribution certificate; the inspected witness path is not projected |

This evidence supports a narrow implementation-independent lesson: if the
successor has an original source contribution witness, later projection and
recursive transport need explicit identities and honest completeness. It does
not supply the missing source formation rule. In particular, post-query
explanation cannot be used as the constructor for Q-independent licensing,
and loss in one historical sidecar cannot be read as semantic absence.

Current complete-profile existence, independent initial admission on the same
`xi`, soundness, principality, source adequacy, production membership and
cutover remain open. No successor implementation or test behavior changed.

## Inspection and limitations

Frozen Oracle HEAD was read as
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. Primary inspection covered
`constraints/explain.rs`, `constraints/mod.rs`, `instantiate.rs`,
`generalize/provenance.rs`, and `poly/types.rs`, plus their bounded direct
callers. These files' SHA-256 values matched the previously recorded hashes
where inventories existed; no source files were modified. No Oracle execution,
build, tests, mutation, benchmark, or Git operation occurred in the Oracle
worktree. Claims are static code-path characterization under the stated
premises; no full-repository absence or source-acceptance result is claimed.

The producer reports were used as locators, then the cited branches and
deduplication/projector behavior were reread directly. The compiler-referee
review and delta review found no remaining substantive issue in scope; the
primary closed the final minor wording inconsistency. No theorem edge or
semantic authority is asserted by this note.
