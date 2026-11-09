# Cycle21 feedback confluence boundary (Draft)

Scope: B4 bridge2, finite source feedback of cycles19–20. Existing Reach/Trace definitions are reused.
Data: all registry/root, finite update IDs, decode, emit. Independent judgement: Closed s means every token emitted at Reach(decode s) belongs to s. Trace is the existing independently defined legal history.
Missing hypothesis made explicit: EmissionMonotone means if a ⊆ b and an actual Reach(decode a) node emits f, some actual Reach(decode b) node emits the same f. It need not preserve the same node.
Goal: for all a,b, Trace [] a and Closed b imply a ⊆ b under EmissionMonotone. Thus every two closed legal histories have the same token membership. The concrete collect execution is a least closed result and agrees with every closed legal history.
This is a conditional bridge, not an unconditional resolve_exact. The actual associated adapter has NOT been proved EmissionMonotone: source reach can disappear after constraint refinement. That hypothesis cannot be silently assumed from spec6.3's order independence. This cycle isolates exactly what remains to connect; no language rejection rule or semantics is added.
Yulang2: x-oracle does not observe internal feedback traces. No executable correspondence claimed for this internal result.
