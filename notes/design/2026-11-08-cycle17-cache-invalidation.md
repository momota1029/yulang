# Cycle 17: source-dependent cache invalidation

Draft, 2026-11-08. B4 saturation subcomponent, not its completion.
For arbitrary registry, ordinary before/after states and source request, collect the finite source slots actually read by its two endpoints. A cache is reusable if the int-materialization bit agrees at every such slot. Prove evaluation and actual producer child-list unchanged under this executable condition. Conversely, changed producer implies a changed bit at a dependency. Under atom inclusion and a model of the later state, int persistence turns this into newly materialized int evidence, not disappearance. This is a finite invalidation trigger for a later state-changing driver; it does not yet prove that driver terminates or has independent final classification.

The int-only unary template restriction is inherited from cycle13–16, not a language specification restriction. No syntax/semantics choice is made. Yulang2 integrated x-oracle is only corroborating source material; this internal cache rule has no runtime equivalence claim.

Proved extension: invalidating slots cannot repeat under consistent monotone growth; any k-step trace in which the actual producer changes on every transition satisfies k ≤ n (n source slots). Non-changing ordinary transitions and dynamic sibling/parent scheduling still need their own termination/closure argument.
