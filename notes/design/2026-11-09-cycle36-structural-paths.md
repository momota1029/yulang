# Cycle36: structural conflicts through directed paths

Partial goal: retain arbitrary structural payloads while detecting incompatible rigid endpoints separated by any finite chain of actual directed variable atoms. This is certificate search, not complete satisfiability or language classification.

Data: finite slot pairs (i,j), seed reflexivity, propagation along actual tyLe(var i,var j). Independent Path is reflexive/transitive edge derivation. FiniteHorn saturates a universe of n*n pairs; independent certificates contain lower and upper atoms and a Path between their slots.

For every n, actual State n, assignment a, and candidate output list: check=true iff independent certificate; every certificate excludes All a atoms; filtering by check preserves the entire output model family. The new filter follows the previous scalar/structural filter and reuses its full declaration-model iff. No assumptions of satisfiability or an oracle for reachability.

Limits: same-head internals, union/intersection, general satisfiability, source generation, receiver generation and driver termination remain outside this fragment. General B4 still has five incomplete bridges.
