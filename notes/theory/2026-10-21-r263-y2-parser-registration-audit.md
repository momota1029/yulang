# R263 — no in-repository Y2 parser or ModuleMap implementation

The tracked Rust source tree has the current `yu-syntax` parser and the
single-file `yu-hir` lowerer. The repository search found no Y2 parser package,
`crates/infer`, or `module_map::register_block` implementation. The old Y2
owners and blob hashes in R258/R260 notes are provenance records; their source
implementations are not present in this repository.

The executable path confirms the distinction. `tools/inference-playground`
uses `yu_syntax::parse_file`; its README explicitly says the playground does
not provide Yulang2 compatibility or standard-library imports. The pinned
stdlib loader also feeds its Y2 source bytes to that Y3 parser to discover
module declarations. R261/R262 show why that loader parse cannot be used as a
Y2 root witness.

`yu_hir::ModuleId` currently has only `SourceRoot(FileId)`. Its
`SemanticImports` retains at most one opaque caller-evidence payload attached
to one binding; it does not resolve imported modules. `lower_module` lowers one
parsed file's direct bindings and expressions against one local namespace.
This is not a Y2 module registration table or cross-module evaluation path.

Bounded result: **NO_IN_REPOSITORY_Y2_PARSER** and no authentic Y2
registration interface was found in the searched `crates/`, `tools/`, and
`apps/` sources. This is a primary-only audit, not proof that no Y2 parser
exists outside the repository. No code or tests changed. R149 remains open;
the next implementation/evidence seam must create an explicit source-preserving
Y2 parser bridge in this repository and establish its source/root relation
before using it for runtime publication. See the R263 contract.
