# Read-only specification/runtime-oracle check

Re-read spec/06-roles.md invariant intervals, centers, point revision, and K2.
No spec or runtime source was modified. The new fixed representative keeps
source2 andsource4 separate; semantic equivalence is not used to turn arbitrary
invariant intervals into matching points. Public-model preservation is not a
claim about Known/RootPending/PointDescriptor or the operational scheduler.

work/dots-audit remains55574b6052ef1534fd0fc36d6d3617ebede59a0e. Read its x-oracle
entries around X8/X12/X13. X8 does not establish an actual recursive structural
mu in the runtime; named-recursive examples do not validate arbitrary interval
rewriting. None directly tests the ordered-history/slot representation proved
here. No Yulang2 runtime was run, and no runtime equivalence or runtime termination
result is claimed. The established runtime-oracle limitations are not new bugs.
