# Cycle248: actual origin transport under ordered definition readback

Implement GeneralNominalOrderedOrigin248 against actual OriginView243, not a
replacement observation semantics. Exact mapping read = sequential solve and
compile/subst observation iff need no SafeOrder. Compatible assignments give
an Equivalent witness for arbitrary origins; nominal/structural outer paths
retain the same actual witness by transporting only their parent observation.
Source leaves do not in general retain a literal syntax representative.

Actual Test.Holds is equivalence-stable for scalar, structural and nominal
constructors. Thus Head and Same are invariant under Compatible assignments,
including source leaves. Ordered rebase combines these with old SafeOrder,
fresh targets within old targets, and satisfaction of the old block. Fresh
SafeOrder is unnecessary for observation transport alone, but remains needed
in the separate fresh-block-model existence theorem.

No actual metadata coverage, operational-law producer, source reachability,
termination, or EvidenceNode claim is made. Current/history/cache and report
bounds require a common-model field adapter beyond this file. No older Lean
source is edited. Verification is pending the parent's bounded dependency
cache preparation; this note does not claim a completed build.
