# Draft: structural occurrence addresses for shared captures

Status: Draft. Date: 2026-11-10. Scope: the finite structural interval capture boundary, B4 bridges 1 and 2.

Close an actual finite trace from root occurrence and nested where positions to the persistent capture registry and independent original shared models. An obligation address is a root occurrence number plus a path of parent declaration and original where-list index pairs. A capture invocation additionally carries its actual declaration. The full declaration is retained, so reused declaration labels cannot alias distinct declarations. Endpoint observations do not participate in identity. Re-expansion with refined endpoints preserves every original where position, including duplicate sibling goals.

The finite trace computes its own invocation table. A visit uses the first table index as the existing registry's numeric invocation. Appending visits preserves earlier indices. This is a finite-trace compiler, not an online scheduler: the entire finite visit list is input. No claim is made that all source-generated visits are finite, that source syntax produces these root numbers, or that every supplied visit is reachable. A separate indexed child construction connects actual `expand` children to provenance without silently identifying equal goals.

The independent judgment shares one valuation indexed by structural invocation and binder. It uses original accepted head and where judgments, not registry positions, generated atoms, or executable success. For every finite addressed trace, assignment and initial demand list, the computed runner succeeds with a final model iff the initial demands have a model and this independent judgment holds for one valuation. The source map and model compatibility are constructed, not premises. Permuting the finite visits preserves model existence because the independent judgment is conjunction, although actual request and registry orders may differ.

Proof chain: indexed child projection and provenance; first-position identity and prefix stability; transport between structural and numeric shared valuations on the computed finite table; finite original-model iff; permutation invariance. Read spec 6.3 and audit x-oracle X13–X16 / C3-PARENT before changes. No new Yulang2 run. All five main B4 bridges remain; associated feedback, root elaboration, generated-work closure and saturation remain open.


## Implementation boundary after proof

The actual registered runner is wrapped by `step`, whose provenance projection introduces no new failure. Every positive output's tagged children equal the real expansion using its captured bindings. `children_at` and `children_addresses` retain original where positions, including duplicate goals. `follow_append` additionally proves that a completed prefix resumes with later visits using the combined finite table, without replay or renumbering. `repeat_models` removes only an unchanged repeated finite pass, not refined endpoint constraints. Permuting already addressed visits is not a proof about rewriting source declarations or where-list positions.
