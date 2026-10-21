# R263 result — no in-repository Y2 parser/registration path found

Primary-only; no independent review.

The repository has the current Y3 `yu-syntax` parser and single-file `yu-hir`
lowerer, but no Y2 parser package, `crates/infer`, or `module_map` registration
implementation. The playground README disclaims Yulang2 compatibility and
stdlib imports. `ModuleId` is only `SourceRoot(FileId)` and `SemanticImports`
is opaque caller evidence, not a resolver. The Y2 source implementation hashes
in previous notes do not mean those sources are present here.

No code/test changed and no external checkout was read. R149 and R168 remain
open. Next step: specify and implement an in-repository source-preserving Y2
parser bridge, then establish source-to-root correspondence before runtime
publication. See the R263 contract and theory note.
