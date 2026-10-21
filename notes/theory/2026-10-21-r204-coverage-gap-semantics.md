# R204 — Meaning of R203 Capture coverage masks

R203 observed the following masks on four Capture snapshots: relation 53 had `120`; relations 56, 57 and 62 had `56`. The bit positions follow `CoverageGap` declaration order in `candidate_context.rs`:

| Bit value | Gap | Mask 56 | Mask 120 |
|---:|---|:---:|:---:|
| 1 | MissingBoundRelation | | |
| 2 | MissingBoundGroup | | |
| 4 | MissingPhysicalEmission | | |
| 8 | MissingAntecedent | yes | yes |
| 16 | ProcessingAntecedentsUnavailable | yes | yes |
| 32 | OrdinarySeedAuthenticationUnavailable | yes | yes |
| 64 | ReplayUseAntecedentsNotRetained | | yes |
| 128 | MissingOriginAssociation | | |

## Constructor origin

`BoundEvidence::admit` sets bits 8, 16 and 32 for every `OwnerEmission` or `ExtrusionLink`, independent of the fixture's actual source history. These flags mean the passive evidence record does not contain the processing antecedents, authenticated ordinary seed, or retained admission antecedent. They do not say that the physical bound or source program is invalid.

For a `FreshUse` admission, the observer copies the antecedent snapshot's mask and adds bit 64. Thus relation 53's mask 120 is the same three inherited gaps plus `ReplayUseAntecedentsNotRetained`. Its printed cause identifies antecedent snapshot 10, source bound Effect(22) −≤ Effect(9), and mapped relation 53; the Capture snapshot bound is Effect(29) −≤ Effect(9). The test joined that physical output to the admission and emission, but the retained summary does not authenticate the complete transformation from antecedent to output.

The masks contain no MissingBoundRelation, MissingBoundGroup, MissingPhysicalEmission, or MissingOriginAssociation bit for these rows. The readback confirms each row has a recorded relation, group, admission, and physical emission. A nonzero mask here is therefore a precise limit on provenance evidence, not evidence that those constructor events failed.

## Source-set interpretation

The readback found no source event on relations 53, 56 and 57; relation 62 carried event 1, whose checking occurrence is ordinal 13, slot 0. Relation source sets are metadata attached to interned relation keys and propagated by relation operations. Their absence on these exact relation IDs establishes that these rows do not directly carry an event ID in the observed source-set field. It does not establish that the original Name/Lambda edge has no path through another relation, a shared anchor, or an accepted transport. Likewise event 1 at relation 62 does not alone establish the original provider-to-use lower-bound chain.

## R183 application

R203 and R204 add a fixture-specific join among Capture snapshot, bound admission, physical emission/readback, relation source-set metadata, and checking occurrence. They do not satisfy R183-FRONTIER-COVERAGE-1, whose universal quantifiers range over actual providers and uses and require the accepted source history, canonical/local owner decisions, and both ordered inputs. No source-qualified counterexample has been produced. R183 stays OPEN with its exact original missing law: prove the actual source-generated frontier path or exhibit a fully joined emitted source history that loses it without a compensating path.

This interpretation identifies what evidence a future exact source-history join would need: the admission's real antecedent and processing relation; its registered origin/source slot; the complete bound-transport chain; and the same provider/use's mapped endpoints through Capture and Replay. It does not authorize production instrumentation or change the language/source domain.
