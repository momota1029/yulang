# Plan-free basis: actual two-owner, unused-unknown regression

GeneralRebaseUniversalRegression263 runs UniversalObserver.run using the actual allocation/merge fixture and two distinct owner/root/Plan selections inherited from TwoOwnerRegression263. The pool is the two actual requested outputs plus unused output (name 1, first target), whose body lookup is unknown. This tests a Plan-free universal address basis, not the earlier representative-Plan basis.

Both selected Plans are checked before every effective write and at the terminal state. There are exactly two effective writes, each necessary by nonempty disjoint owner tables. The actual executable request lists stay the original two outputs, and the selector remains [first,last] throughout. The additional unused unknown output is not selected and does not cause a layout failure. Its reserved universal body address is present initially and remains present after terminal success. Therefore successful terminal state is explicitly not done/empty.

No global representative family, layout equality, normalized compatibility or assignment premise is used for this operational result. The two actual Plans still supply their selected proposals; this is not a claim of a Plan-free source compiler. Operational completion and checked readiness do not by themselves assert satisfiability or a universal-basis ClassEffects interpretation. That semantic bridge is separate work.

Strict new-module compile PASS. Standalone lake audit: 7 usage examples, 6 theorem axiom audits PASS, standard axioms only. See universal-regression-audit.txt.
