# Cycle47: slot equality evidence in the finite string Index adapter
Status: Draft, 2026-11-09. Scope: internal finite named-source adapter, not parser lowering.

Partial goal: explicit input type equalities must transport string evidence in both directions, independently of whether the slots share a source name. Distinguish transport along equality from actual Index requests.

Data: arbitrary finite source table, seed occurrences, slot equality pairs, named Index requests. Independent judgment has seed, source-alias, equality (both directions), and Index constructors. Executable closure compiles all these edges into the existing finite saturation. Prove exactness, concrete model existence in the string fragment, and actual checked producer execution at reachable receivers. No assertion that every receiver is reachable.

Spec 6.3 associated equalities supply ordinary constraints; this adds no new language rule. Existing audit X13–X17 provides limited source sharing evidence but not this arbitrary finite closure theorem. No new runtime test.

General B4 still needs five bridges. This result only strengthens finite source/evidence closure. Parsing, arbitrary role/where generation, non-string receiver semantics and general classification remain outside scope.
