# Cycle 148: exact constraints of actual support traces

Scope: an auxiliary finite-trace semantic audit, not a V5 bridge. Record installation
packets and merge output atoms from actual guarded support steps; administrative
steps contribute no semantic constraint. Prove that a fixed assignment survives
exactly when it models the initial state and every recorded constraint. Extract
such a record for every actual finite trace. This distinguishes existential
inhabitedness preservation of installations from preservation of each original
assignment. Event permutation only compares already-realized traces with matching
constraints, not arbitrary scheduling or reachability. No definitions or frozen
Audit.lean / README.md are changed; general V5 remains 6/14 with eight residuals.
