# R292 — Authenticate public module paths and retain imported name identities

Status: solo primary continuation; subagents are forbidden by the user's goal.
The sprint dispatcher is therefore not launched or simulated through a nested
CLI. Luna records the selected action from current source evidence.

## Parent and fixed outcome

Parent remains the unchanged Yulang2 Types and Console samples in R149, with
their original acceptance, public type, ordered output and source/native proof
requirements. R291 established source-only export routes for the exact pinned
stdlib set. It did not validate intermediate `pub mod` declarations or bind
those identities into HIR.

Add source-backed public module-path validation to export resolution. Then add
an opt-in HIR import carrier that resolves imported names from exact
parse-owned use declarations and export results, while preserving local
lexical/module shadowing and reporting ambiguity/recovery. Exercise the
unchanged Console source and the prelude names needed by Types/Console. Continue
into the candidate-source seam if the carrier has an existing, exact owner;
do not use external `DefId` ordinals as local HIR definition indexes.

## Source meaning and proof boundary

Use only the pinned source closure and the existing implicit-prelude behavior
recorded in R149. Public re-export resolution requires every concrete module
segment to be declared public by its indexed parent module. Virtual enum/act
member namespaces remain tied to their containing source declaration. Lexical
bindings take precedence over imported names; a local `id` must shadow the
prelude's `id` without removing either source declaration.

The proof target is finite syntax correspondence: every accepted imported name
has one visible public declaration and a finite route whose module segments,
use leaves, aliases, visibility, declaration identity and source ranges are
retained from the supplied parsed files. A parser `Missing` node attached to a
`ModDeclaration` represents an unresolved external child module; the exact
child index discharges it only when the declaration is public. `Error` tokens
and `Invalid` nodes still fail closed. Missing/private paths and ambiguous
declarations otherwise fail closed. This does not prove candidate typing,
role conformance, method selection, runtime execution or source/native
correspondence.

The caller-supplied index set remains an authority boundary. The playground
must build it from `resolve_implicit_stdlib()` and verify pinned blob identity.
The HIR carrier must retain that input identity and must not treat a spelling
or externally supplied ordinal as semantic authorization.

## Before/after evidence and falsifiers

Before: R291 resolves `Display`, `say` and `println` by public uses, but does
not verify public module ancestry and is not consumed by HIR. R149 reports
`SemanticImports::empty`, a local-only HIR namespace and unresolved imported
names; candidate definition-use indexes assume one HIR module's local ordinals.

After: tests demonstrate public module ancestry, exact imported source
identities through prelude re-exports, local shadowing, alias/glob behavior,
and fail-closed private/recovered/ambiguous paths. The unchanged 92-byte
Console input retains `println`'s import identity; its `say:` form still has an
unsupported local-source carrier, while a supported standalone `say` use
retains the same export identity. Any attempt to treat an imported source key as a local
`DefinitionRootId`/ordinal or to skip the declaration's type/scheme is a
falsifier for candidate integration.

## Exact leases and resources

- `crates/yu-hir/src/module/source_exports.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/lib.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tasks/agent-loop/current.json`
- this contract
- `notes/theory/2026-10-22-r292-hir-authenticated-import-identities.md`

Cap 900 seconds, no carryover, one Cargo process at a time. Focused HIR and
playground checks, the full playground library tests, `cargo check -p yu-hir`,
`python3 tools/agent_sprint.py check`, and `git diff --check`. The primary owns
all leased writes and Git. Solo work has no independent proof review; checkpoint
results as unreviewed and keep R149 open. Stop at the resource cap, or when the
next step requires a multi-HIR type/scheme owner not established by this
contract; record that exact owner seam and carry the parent goal forward.
