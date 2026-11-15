# Cycle198: mixed execution, current reuse, finite completion

Target: the I32 WF/V6 Evidence boundary, soundness side only.

A finite recorded packet is sound after a mixed ordinary/same-slot nominal refresh path from the actual initial state (cycle197). A current reusable plan is sound without requiring a new operational installation (cycle195). Combine these two nonrecursive sources in a single node rule. The state itself bounds all source identifiers: recorded packets use the journal ceiling, while reusable plans use the registered-site ceiling. Child identifiers strictly increase, hence a decreasing natural-number rank supplies a finite dictionary. No caller list of plans, accessibility certificate, complete Evidence, or prebuilt dictionary is assumed.

The remaining completion obligation says each generated node has either a recorded packet at that occurrence or a current reusable plan. It is deliberately NOT claimed from Stable: earlier counterexamples still apply. A selected-only version suffices for soundness of actual classified payloads; the total version supplies a uniform finite dictionary. Both preserve the actual final state/models, not models of a fabricated catalogue.

This does not change operational Step, language semantics, or the general EvidenceNode target. Slot-growing refinements and non-nominal query syntax remain outside cycle197's mixed path classification.

## Executable scope checks

`GeneralNominalMixedNonleaf198` instantiates mixed completion with an actual initial installation: the nonleaf parent is recorded and its terminal child is provably absent from the journal but currently reusable. It yields the actual classified payload `node 1 [node 3 []]` in an inhabited final model. This fixture has no descriptor refresh.

`GeneralNominalInstalledRefresh198` separately constructs an actual initial installation followed by an actual same-slot descriptor refresh, from explicit operational enabling, freshness, generatedness, refresh-certificate, nominal/variable syntax and unknown-to-known premises. Its installed packet is recovered from the real journal, with no final parent Instance assumption; a leaf then needs no child Evidence premise. This generic two-edge theorem is not presented as a closed concrete example discharging every operational premise. Slot growth remains excluded.

## Certified remaining obstruction

`GeneralNominalMixedObstruction198` rechecks the existing reachable, inhabited, stable selected multi-tag source against the new mixed rule. Its initial journal is empty and every current candidate fails request materialization, so neither arm supplies a node. Both selected and total mixed completion fail there. This is a counterexample to inferring the completion contract from those source facts, not a refutation of general semantic EvidenceNode or of the language specification.
