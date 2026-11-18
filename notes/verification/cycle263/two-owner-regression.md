# Actual two-owner regression

`GeneralRebaseTwoOwnerRegression263` uses the existing allocation/merge fixture's actual aSite and bSite, with a separate zero-arity leaf Plan rooted at each observed site. Selection.ofPlan derives both owner and root from that Plan. Child identity separation proves the owner codes differ; no concrete enormous identity computation is used.

Both actual executable request lists are exactly the fixture's two named target outputs. All selected requests are checked at the initial, intermediate, and terminal states. The full constant selection [first,last] remains nonempty throughout. The observer's first proposal removes only its own tagged table; the second owner's table remains intact, so the scheduler performs a second effective write. The checked execution trace is exactly [start,middle], then terminal success. An explicit event trace records both actual snapshots/roots/Plans.

The final Models theorem holds simultaneously for every assignment, with arbitrary base, and is exactly base AND actual first-root ClassEffects AND actual last-root ClassEffects. Success does not prove satisfiability. It also does not prove that these supplied Plans are registered by a complete source compiler, nor Frame, old-Step simulation, or source-machine termination.

Verification: new module strict Lean --trust=0 -DwarningAsError=true PASS; standalone lake usage audit 5 examples PASS; 8 public theorem axiom audits only propext/Classical.choice/Quot.sound. Required new observer/run/trace dependencies were independently rebuilt in this worktree; no whole repository build was claimed.
