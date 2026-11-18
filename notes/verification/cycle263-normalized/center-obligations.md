# Remaining source-center agreement

Investigation after `RegisteredPlan263.source_compatible`:

The same-owner pair contains root invocation identity and declaration id, not the actual center vector. Thus its definitional equality alone cannot discharge the remaining premise. The current source Models constrain actual head schemas of registered plans; they do not directly expose a cross-plan center equivalence field.

There is a promising non-vacuous route, rather than evidence of a counterexample:

1. Prove actual mixed-kernel `state.core.sites` origin: each site is the initial rootSite or emitted by an actual retained versioned plan. Administrative enqueue is impossible on these traces by MixedTrace235.generated_registered; other administrative actions retain centered sites.
2. Prove each registered versioned plan's input site remains in the final centered sites. Its actual installation Frame.center_recorded establishes membership and MixedGrowth234 preserves it.
3. Induct on numeric invocation identity across *two* source paths. Child identity is strictly greater than parent identity; same child identity plus common seed identifies parent, declaration and clause through ChildCoherence184.producer_declarations. Root/child overlap needs its own mixed-path identity-lower-bound lemma.
4. Inductive center agreement yields actual input binder agreement by HeadSupport263.input_binder, using the already proved registered metadata/Inputs. ChildSemantic186.child_centers_list then transports child centers. Frame231.childSite_center_eq reduces versioned child centers to those original childSite centers.
5. Apply to the two registered input sites and their equal owner identities, eliminating source_compatible's explicit centers argument.

The existing HeadIdentityInduction186.trace_identity_centers has the right mathematical induction but applies to a single old-kernel path and old journal membership. It is NOT a theorem about mixed versioned source paths, and cannot simply be cited for step 3. Likewise a finite identity cover does not imply semantic center coherence. Cross-path source model satisfaction is stronger than arbitrary Plan agreement, and no counterexample to that full hypothesis has been established here.

This note records proof obligations, not a completed source-center theorem.

## Resolved later in the same cycle

`GeneralRebaseRegisteredSites263` now proves steps 1–3's provenance/input retention/root lower bound from actual mixed steps. `GeneralRebaseSourceCenters263.centers` performs the two-path numeric identity induction and proves positional semantic center equivalence from actual Models alone. `compatible` and `source_compatible` eliminate the explicit center/binder equivalence premise. The focused strict build and axiom audit cover these proofs.

Remaining integration boundary: each compared assignment must satisfy *both* reachable snapshots' Models. Independent reachability alone does not imply that a model of one branch satisfies an unrelated branch or a classically chosen representative's snapshot. No such inclusion is claimed. `RegisteredPlan263.source_layout`, separately, needs no Models at all.

The support premise has subsequently been weakened to `Heads`, actual head-schema satisfaction for every registered producer in each of the two snapshots. The production `source_compatible_from_heads` no longer assumes full Models (which included output ClassEffects). This distinction is essential for a non-circular finite-write integration. It remains a head-support theorem, not a proof that all arbitrary assignments satisfy actual head schemas.
