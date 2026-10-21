# R270 result — source tuples in candidate inference

Primary-only provisional implementation checkpoint. See `notes/theory/2026-10-21-r270-source-tuple-candidate-graph.md`.

Implemented source-ordered tuple relation admission, per-element effect edges with wide local slots, candidate graph tuple capture and ordered fresh reconstruction, and accounted tuple graph/term storage.

Focused evidence passes for arities 1/2/3, polymorphic `id` freshening, nested source tuple admission, and an `io::tick()` child effect edge. The existing native ordered comparison test passed in the feature-enabled full run before its later stack overflow. Sprint tooling check and 57 agent-sprint unit tests pass.

Full suite is unresolved: the default parallel run overflowed a worker stack; a 16 MiB stack retry reported several failures then overflowed; serial run remained CPU-bound for over two minutes and was stopped. One failing normalization test also reproduces without the candidate feature. The candidate graph child/source identity correspondence and exported nested shape still need a targeted proof/test. No independent review. Public closed tuple types, runtime tuples, and R149 playground samples remain open.
Source-order audit: HIR tuple elements are retained in syntax order; candidate collection maps each source index to its value endpoint and child effect in parallel ordered vectors; tuple-term construction, effect slots (`index + 1`), graph capture offsets, and FreshUse reconstruction all traverse those vectors in order. This proves the static ordering path for retained terms/effect edges. The source index is not stored as an explicit post-selection field, and exported row nodes do not expose a source-child receipt. A stronger assertion expecting child literal leaves directly in export failed because graph children are local rows; it was removed as an invalid assertion, not treated as a tuple reorder. Direct exported source-child identity and nested exported shape remain open.
