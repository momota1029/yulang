# Review of the proposed TerminalPairResidual

**Unproved / 未証明.** `tools/Cycle177NextNominalGoal.lean` defines a proposition and checks its type. It supplies neither a proof nor an axiom nor an exported library theorem. Successful type checking is not evidence that the proposition is true.

The proposed statement appears mathematically well-targeted under its explicit assumptions; no immediate missing semantic premise was identified by source review. Its important new proof obligation is cross-endpoint capture coherence, not just reuse of the existing point-bound lemma.

- Both distinct endpoint slots have recorded nominal descriptors with the same constructor name and exactly `count` type arguments. The successful report should therefore consist of both endpoint capture lists, with each injective binder name repeated once across the two lists.
- Within an endpoint, injective names and nominal observation uniqueness supply coherence. Across endpoints, the explicit subtype assumption plus the source-model nominal witnesses can be composed into nominal-to-nominal subtyping. `CommonNominalFullCarrier.nominal_regular_invariant_exact` then supplies argument equivalence. This is the substantive reason that one-way endpoint order can suffice here: nominal arguments are invariant in the existing carrier. Injectivity alone would not establish cross-endpoint coherence.
- The source model supplies each projected argument's Fits bounds. Cross-endpoint equivalence should transfer Fits between the paired bounds, discharging ProjectionModels and capture compatibility; endpoint ordering also handles the top-level interval check.
- Terminal requirements and an empty requested-output list make the generated materialization schema empty via `GeneralDictionaryLinearLeaf.generated_empty`. No universal materialization assumption is being hidden.
- The fresh allocation merge equations intentionally remain on the right side. Forward extraction is supported by the existing private-state decomposition; the reverse implication still requires the actual cross-endpoint report/projection proof. This is a residual equivalence, not a producer of the merge equations or a proof of full EvidenceNode.

The proposition does not require a root-role match or an argument lookup because its conclusion is BranchModels for explicitly supplied bounds, not Prepared, Local selected, Candidate or Instance. Those premises would need to be restored in a later consumer. It also does not claim existence of a source model, a common centered plan model, or exact G reachability/stability.

Recommendation: retain this as a planning-only **unproved** next lemma, with the first implementation milestone being cross-endpoint argument equivalence and ProjectionModels. Do not report it as verified coverage or as a completed nominal producer.
