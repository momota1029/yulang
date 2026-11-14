# Cycle185: actual HeadStep observed-site support

The carrier is HeadStepEffects.State, the transition is HeadStepKernel.Step,
and the final wrapper is B4TargetV6.Reachable HeadWFBoundary.boundary.
No old-centered-Step simulation is assumed. Reuse the syntactic child-site
separation theorem from184, but prove its historical premises by induction
on this actual transition.

For every InitialSource, installed-depth bound, and finite trace from the
head initial state: every fresh name with purpose>=7 is absent from the raw
current context sources and every registered observed site's rawSiteSources.
The install branch uses Frame.context_eq and Frame.raw_recorded; the impossible
administrative enqueue branch uses actual generated_registered. Refresh,
equate, reobserve and merge retain the relevant site structure.

The WF wrappers eliminate source/depth assumptions: destruct Initial, derive
installed_depth_bound from its point+GroundRoots fields, and retain seed with
configuration_trace. This is an auxiliary allocation result for EvidenceNode,
not the V6 EvidenceNode bridge, a candidate compatibility theorem, or evidence
that all effect-ledger source names are excluded. HeadLedgerFrame182 remains
the stronger model frame; the separate effect ledger still matters.
