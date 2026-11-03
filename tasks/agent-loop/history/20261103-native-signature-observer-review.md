# Native operation signature observer: independent review

`/root/native_observer_review` independently reviewed the frozen observer and
reproduced it against isolated frozen crates, then independently rebuilt the
packaged version offline with its own read-only lock. The packaged source has
SHA-256 `cb33d461e2559c163484a3c23713976ca47e4cccd8e1fa62f3c726775ac30bfb`;
all three fixture bytes match the reviewed originals. The 326 dependency files
matched the frozen baseline. All three runs succeeded and reproduced reviewed
logs after substituting the different input/module paths. The package has its
own lock; the unrelated inline-extraction lock was not included or modified.

For the one positive fixture, the retained exported graph identifies a unique
outer Function through the actual root bound and then its nested Functions
through their actual four children. Root and nested result-effect rows link to
Support bounds with the reported source declaration/occurrence/row provenance
and ordered families. `same_identity` means same session plus canonical
representative, not the same raw allocation. Same-parse/HIR/Arc checks support
only that run. The unchanged full R301 fixture and a negative-concrete-row
mutation returned `Unsupported`; both controls accept any solver error, and the
full fixture contains multiple potentially unsupported features.

This is finite captured-graph evidence. It does not prove general native-to-Lean
correspondence, native Term-to-export-node equality, a name-to-row certificate,
EI/Union semantics or any R159 premise. Dependency changes require revalidation.
The reviewer performed no repository writes or Git operations.
