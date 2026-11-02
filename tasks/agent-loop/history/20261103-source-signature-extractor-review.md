# Finite source signature extractor: independent review

`/root/extractor_review` and `/root/extractor_parent_audit` independently
reviewed `tools/inline-authentic-extraction/src/bin/source_signature_r300.rs`,
SHA-256 `e72138e1982bebe2ca6fe1e867b4cc8d70126524b1946875e05deb8a7cc35c18`.
The source reviewer independently ran the offline isolated Cargo build and all
seven unit tests, plus CLI cases for private/ambiguous resolution, malformed
source and unresolved rows. Output parses as JSON; invalid cases publish no
stdout. No blocking, major or minor finding within the finite research scope.

Native keys are checked against the selected parse and interned by complete
native equality within a run. Direct operation uses authenticate HIR occurrence
ownership and join the declaration table by `Arc::ptr_eq`. Recursive syntax,
row order/duplicates, omitted versus explicit rows, holes and tuples are
retained. Function argument signs flip; the root Function Self marker goes to
its result effect port. Artifact-local integer keys are not identities across
executions. The extractor retains errors rather than claiming solver acceptance.

The result covers a selected single parse/module and direct top-level source
operation uses; catch patterns and imported modules are outside its use
inventory. It is finite HIR evidence, not an authenticated Rust–Lean theorem,
complete native lowering, IF/EI semantics or a discharged R159 premise.
The parent-edge reviewer checked these limits and found no semantic parent
delta. The producer checked one emitted Lean data file with Lean 4.35.0; the
independent source reviewer did not independently run that Lean check. No
production inference or expected outputs were changed.
