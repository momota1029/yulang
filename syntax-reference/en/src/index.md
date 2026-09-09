# Yulang syntax and CST reference

This reference defines the accepted Yulang surface forms and their lossless,
source-order Rowan CST. The CST-conventions slice specifies nodes, token
leaves, trivia, and recovery placement without documenting parser control flow
or internal maintenance work.

The [CST conventions](conventions/index.md) section defines the common tree
notation and the ownership of source-root, header, and recovery diagnostics.
Existing construct pages are legacy implementation material pending phased
reconstruction. They may still describe parser behavior, ASTs, implementation
paths, and fixtures; they are not yet reconstructed construct schemas.
Reviewed batches will replace them with the language and CST reference.

The Authoritative design records govern this reference. When an approved CST
target has not yet been implemented, the page identifies that status rather
than treating the current implementation as the language specification.
