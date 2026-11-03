# Effect-support follow-up

After `72d77856b`, an exploratory extension of the existing operation
rewrite/capture test attempted to connect the original Support payload to the
captured graph and two FreshUse maps. The extension did not pass and was
removed; it produced no new verified support-content claim.

The worker reported that the source-cache tail had raw row 3 while the
captured Support tail had raw row 9. It also reported that a copied view's
position did not equal `declaration.signature_position`; the correct source
position correspondence was not established. These are observations from a
discarded experiment, not independently authenticated general properties.
Do not assume either raw tail equality or equality with the declaration's
signature position. The next source investigation should trace the exact
source row position and signed extrusion mapping through the actual bound and
same-use route before adding assertions.

The worker restored `candidate_effect.rs` to SHA-256
`ba9016eb41789f554df60c6b612573d4742d27ac2e05251f662ee95aee6eee3c`
and reran the existing focused test with offline, locked Cargo and the
`shadow-apply-candidate` feature: one test passed. That existing test proves
the finite rewrite/capture and Function reconstruction checks documented in
its prior review; it does not establish Support contents or tail lineage.
