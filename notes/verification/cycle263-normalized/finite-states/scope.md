# Explicit finite state enumeration

`states basis` enumerates all canonical remaining sublists by recursively skipping or retaining each basis position. Each result carries the required Sublist proof. Completeness is proved by induction on the actual Sublist witness, with proof irrelevance handled by Lean's structure equality. The list has exactly `2 ^ basis.length` entries, including duplicates when repeated basis facts make different positional choices yield the same state. This is a list length, not a claim of that many distinct states.

`image_exact` gives the exact image of any inspector on the enumerated states, and `forall_image_iff` equates universal inspector predicates with predicates on the finite image list. `heads_image_iff` specializes this to actual versioned source Heads. Consequently the local meaning theorem's all-inspector-image head premise concerns an explicitly finite family, even though it is larger than the one visited execution history.

Enumeration is exponential and is not used to claim efficient execution. It does not decide semantic Heads, prove head satisfaction, guarantee reachable observations, or establish source Models/SAT/M1. It exposes the finite domain; all semantic and source reachability assumptions remain separate.

Focused strict build and six axiom probes pass. Audit examples kernel-reduce an empty basis, a duplicate two-fact basis, and a three-fact basis of length8. No native_decide/sorry/new axiom or frozen edits.
