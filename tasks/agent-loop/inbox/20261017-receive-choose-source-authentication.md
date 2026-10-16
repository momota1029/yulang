# Frozen assignment handoff: receive/choose source authentication

- Sprint: `authentic-source-and-forward-handler-20261017`, contract revision 1, SHA-256 `fb5f4be5a15b6697a745abdb3a3620c5c28415b60c05447747ce2e6e319ac290`.
- Assignment/handoff ID: `assignment-receive-choose-source-authentication-20261017`, revision 1.
- Parent gate: `CHOOSE-SOURCE-2`, the original receive/choose mathematical graph. This handoff authenticates only a newly authored fixture spelling; historical source identity, phase-root `R_e`, source-Generalize/public-export, principality, theorem, and production gates remain OPEN.
- Baseline: `cba9d794d1f0498262b3668f9d5cc055c16749e9` (source baseline; no Git operation performed).
- Role/runtime: implementation/source owner; requested `gpt-6-luna` / `high`; observed worker ID, session, model, and effort are UNKNOWN in this runtime context. No runtime routing claim is inferred from the requested role.
- Exact leases and artifact hashes:
  - `tasks/agent-loop/fixtures/20261017-receive-choose.yu` — SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.
  - `crates/yu-solver/examples/research_source_registration.rs` — SHA-256 `2a58996b1085ca892dcb9a79465054fad9ac0ddfce4b02eb02c51aa9d464bfe1`.
  - `tasks/agent-loop/inbox/20261017-receive-choose-source-authentication.md` — this frozen handoff; its direct SHA-256 is returned to Luna with the submission.
- Direct dependency revalidation before the first write: all 27 entries in the frozen contract's `dependencies` map matched their declared SHA-256 pins. Contract bytes matched the assigned hash. No leased or unleased dependency was modified.

## Outcome and source-to-owner path

The fixture is explicitly new research input, not a recovered historical source. Its fixed spelling declares `ctrl.choose : () -> (() -> [ctrl] int)`, defines `f0 (u:()) = ctrl::choose ()`, and defines a receiver body that applies `f ()`, binds the returned `g`, then applies `g ()`. This renders the admitted `choose : Unit -> alpha+` shape from `notes/theory/2026-10-16-choose-source-declaration-initial-installation.md` §1 and the receive/choose call shape, without claiming a historical CST or source identity.

The example reads the exact fixture bytes via `include_str!` and checks them against the disk file before parsing. It uses the public `parse_file` and `ParsedFile::structural_recoveries` APIs, then `lower_module_with_local_source` with a source-root `ModuleIdentity`. The inventory reports parse revision, structural recoveries, module identity, HIR definition IDs/roots and source keys, the family/member declaration keys, the `f0` operation occurrence key and range, exact resolved declaration pointer identity, and the receive LocalSource expression inventory.

The solver path calls only `CandidateInference::solve(hir.clone())`. That entrypoint owns `candidate_source::preflight`, normal candidate source collection/constraint scheduling and candidate propagation through the solve session. On success the example exports only the fixture-owned `f0` `DefinitionRootId`, then reports the root node's public leaf/polarity/function-child observations and graph node count. `CandidateGraphNode` exposes no printable numeric root index, so the example reports the value returned by `CandidateGraphExport::root()` through its public observations instead of inventing an identifier. It never calls a detached collector, weakens preflight, fabricates a source key, or exports another root. The candidate graph root remains an implementation graph identity and is not identified with mathematical phase-root `R_e`.

The exact owner path inspected is:

`parse_file` / parse-branded `SourceNodeKey` → `lower_module_with_local_source` → `lower_module_with_counters` and source declaration/local-source formation → HIR-owned definition roots, occurrence source-key lookups, and LocalSource operation resolution → `CandidateInference::solve` preflight → `ConstraintBatch::collect_candidate_mode_scoped` / candidate session propagation and graph capture → `CandidateInference::export(f0_root)`.

Relevant prior source-owner history was reused as an owner map only: `tasks/agent-loop/inbox/20261017-authentic-root-export-cut.md` records the previously missing concrete CST/ModuleId/SourceNodeKey and distinguishes the candidate graph root from `R_e`; `notes/progress/2026-10-17-source-constructor-export-cut-review.md` records that no fixture or compiler code had been supplied. The choose source-instantiation note supplies the fixed mathematical shape and warns that it has no historical CST, module, or source key. None of those records authenticates this new fixture or supplies a pass result.

## Pass/refusal evidence and boundaries

No parser, HIR, candidate solve, export, test, build, or Cargo command was run by this assignment. The frozen implementation lane expressly forbids execution; the optional single primary-owned Cargo run is outside this lease and may only be considered after freeze. Therefore the actual parser/HIR/candidate outcome is **NOT RUN**, not pass and not refusal. The example is instrumented to print the observed structural recoveries and IDs, or to stop at the precise parser, lowering, operation-resolution, `CandidateInference::solve`, conflict, or `export(f0_root)` refusal stage when the primary elects to run it. It does not claim that a refusal occurred or that solve/export passed.

The outstanding source-owner TODO is: obtain an authorized execution receipt for this frozen example or, if it stops, preserve the exact first stage and error as emitted. Even a pass authenticates only these newly emitted fixture-owned CST/HIR/candidate identities. Historical source correspondence still needs the original immutable source artifact, original `ModuleId`/`SourceNodeKey`s, and an independently justified association of the selected mathematical phase root with the source/candidate/export operands. Do not infer `R_e` from `f0`'s definition root or this candidate graph root. No theorem, semantic adequacy, detached export law, ordinary runtime execution, or production claim follows.

## Checks, resources, and cessation

- Checks completed: contract SHA-256; all 27 direct contract dependency pins; source-owner/API read audit; output byte hashes. No tests, builds, Cargo commands, compiler execution, Git, network, scratch output, or generated artifact was used.
- Omitted verification: actual parse/lowering/solve/export outcome; reserved for Luna's optional post-freeze primary-owned run (one Cargo process, at most 120 seconds, isolated target directory, not a test).
- Budget: within the assignment's 7-stage / 600-active-second cap; exact active seconds were not instrumented. No budget transfer requested or used.
- New paths: exactly the three leased paths listed above. Disposable scratch: none.
- Worker state: **STOPPED** for this assignment; writes ended after freezing this handoff and hashing outputs. No descendants, active processes, generated paths, or unresolved descendant leases.
- Integration/review: pending Luna intake and fresh independent source/code review. No self-certification.

## Exact missing source-owner TODO

`CHOOSE-SOURCE-2-RUN-RECEIVE-CHOOSE-20261017`: on the unchanged frozen bytes, record the primary-owned parser/HIR/normal-solve/export outcome and the exact first refusal if any; source owner is Luna for the optional run. If the path passes, retain only the fixture-owned `f0` root/export association. Falsifiers are fixture-byte mismatch, structural recovery, missing/wrong declaration or use source key, non-resolved or mismatched `choose`, HIR ownership mismatch, CandidateInference preflight/solve refusal, conflicts, or export refusal. This TODO does not authorize edits, a new test, altered source domains, or `R_e` inference.
