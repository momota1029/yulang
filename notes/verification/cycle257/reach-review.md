# Selected-root dependency review

Reach audit traverses proof/definition dependencies for 17 selected final roots.
150 of 171 explicit declarations are reachable. This is not a code-coverage
percentage or proof that every useful statement must occur under those roots.

The 21 remaining declarations are listed verbatim in reach-final.txt. They
include adapter failures and repairs, length/bound statements, raw public
projection wrappers, row metadata/private-read facts, projection noninjectivity,
no-strict-view-rank, report origin preservation and explicit exclusion of the
binder counterexample. These are regression or boundary results, not missing
lemmas required to close the selected final roots. Full axiom/type audits still
cover all 171; no declaration is omitted on the basis of root reachability.
