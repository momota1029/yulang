# Draft: ancestor-correlated candidate paths

Cycle24's node-keyed mask loses information when different ancestor choices reach
one source node. Retain the full reverse list of (parent source node, candidate)
alongside the current node. A path-specific mask sees that history and cannot be
silently reused for a different ancestor route. No candidate-selection semantics
is chosen: mask and observation remain explicit inputs.

For every checked registry, root, observation and history-dependent mask, enumerate
paths to the derived sourceWeight(root) bound. The independent Path judgment uses
Inspect and declaration source substitution; prove enumeration iff Path. Checked
Paterson descent derives the bound (no external fuel or acyclicity certificate).
Annotations may depend on the entire path. Filtering the path-keyed metadata and
running actual associated equations should have exactly the seed models satisfying
every active path's independent associated derivation (with AssocWellFormed).

This closes a metadata/provenance subgoal, not candidate choice, source lowering,
feedback convergence, language acceptance, general B4, or X13–X16. Conjoining an
incompatible set of enabled paths is not language typing. Sibling correlations
inside a shared global branch assignment and guard preservation under feedback
remain separate obligations.

## Implemented boundary

The stored carrier enumerates structural source paths independently of observation
and mask. Every active Path at any observation/mask is retained in this fixed list.
Activation uses the complete history both for the mask and annotation lookup.
Duplicate occurrence positions with identical (parent,candidate,child) data are
not distinguished. The computed depth bound does not claim practical complexity;
branching can make the finite carrier large. No source-level typing is asserted.
