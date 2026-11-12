# A stale journal can block a selected packet

Status: Draft diagnostic, 2026-11-12. Scope: the raw Astra saturation State;
not a reachable-state counterexample and not a refutation of B4.

Reuse the checked terminal source from GeneralDictionaryRecursiveObstruction.
The unique visible declaration has key 40 and requests an int-valued output.
Insert a journal packet with the same occurrence identity 300, declaration key
41, and no requested outputs. A raw Packet need not belong to the current
registry or its site's registered occurrences. Its branch conditions can hold
in the original string-valued model because it requests no output equation.

The intended finite theorem combines a genuine journal model, the unchanged
safe unique selection of key 40, failure of the selected packet's universal
commitment, and failure of Installable for any packet at that root. The last
claim follows from the visible declaration's key 40 versus the prior packet's
key 41 and reflexive Alias on occurrence identity 300.

This isolates why stable-implies-committed requires compatibility of journal
choices with current local selection. It does not assert Stable: the reused
context still has an unknown source slot, and Refresh is a separate possible
transition. Reachability invariants, or a suitably validated carrier, remain
necessary questions; no Astra definition or Evidence predicate is weakened.
