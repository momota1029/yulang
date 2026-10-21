# R273 — public closed ordered Tuple nodes

Status: provisional `yu-types` implementation packet; unreviewed. R149 and all end-to-end sample/proof gates remain OPEN.

## Design correspondence

R149 requires arbitrary finite positional products. The unified design plan §3.3 calls for one ordered product constructor across constraint generation, capture, public types and evaluation; R254 fixes exact arity and same-index child correspondence in the live solver. `yu-types` currently exposes only scalar/function constructors plus union/intersection child ranges, so closed scheme views cannot yet name a product.

This packet adds a distinct positive and negative Tuple constructor across the existing closed arena pipeline. Tuple child spans reuse the established checked ordered child lanes, but remain semantically distinct from Union/Intersection. This is an API/value-construction slice only; it does not connect candidate graph export into this arena.

## Evidence

Pending implementation and focused finalization/alpha-equivalence checks. Public type display from accepted Yulang source, source/native correspondence, soundness, principality, R149 sample outputs and production remain OPEN. No independent review under the user's solo-work instruction.
