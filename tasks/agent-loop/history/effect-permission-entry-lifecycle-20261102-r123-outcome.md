# R123 outcome — computation-entry lifecycle

Contract: `tasks/agent-loop/sprints/effect-permission-entry-lifecycle-20261102-r123.md`, SHA-256 `d715f6f26267c7ab14f2451ede516ddba8184b91f899ebf5005f9b5477104623`. Baseline: `852ab889cee2f4cfe04da3a1e8c9dd96f9758845`. Exact input pins are in the manifest and admission.

## Result

**PASS for bounded immutable-source lifecycle evidence only.** Every authenticated production `LocalSource` Lambda formation route excludes simultaneous `record_pattern` and outer annotation. Record-pattern routes require no annotation; annotated routes carry an identifier pattern with `record_pattern = None`. Root/local initializer, inline and member-formal routes preserve the distinction. The computation-entry constructor is byte-identical to the corrected R39 source audited in R122.

For the selected paths, the action order and local lifecycle are traced. A successful guard establishes the two absence conditions immediately before that invocation's publication. The selected `shadow_apply` caller owns and discards its private session on error. The evidence does **not** establish a universal one-time schedule or safe reuse law: the SCC partition owner, exhaustive Lambda traversal uniqueness, and the intrusion undo bridge are outside the authenticated inputs. Publication can precede a failing final resource sample; no general rollback follows from `Err`.

## R39 mapping and remaining gap

Existing R39 `Valid`/`prepare_exact` can consume the conditional guarded PRE-state fact, but a Rust source-to-Lean instantiation still needs the exact same graph state, registration/key membership, ordered collection projections, owner identities and publication state. The R121 consumer indexed-read interpretation is another separate open edge. The conditional guard result is not universal absence before every dispatched `Entry`, and neither is claimed.

## Frozen evidence and independent review

- Source handoff: `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-source.md`, SHA-256 `c2fe62592f85a8f6bbf3e5b1eecb29fdef26cb031a2894c0a417db1ab64c679a`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-proof.md`, SHA-256 `689588906f07efcf1908fca05d74e868eee5835b026582d79bf4cf8106b2ee90`.
- Fresh independent `compiler_referee`: **PASS**, no blocking/major/minor findings. Reviewer independently checked pinned Rust/Lean bodies before the handoffs, authenticated all eight source pins and both handoff hashes, and confirmed the limits above. Relevant tests were read, not run. Read-only reviewer wrote no file; this section is the primary review receipt.
- Source, proof and review workers are STOPPED: `/root/r123_entry_lifecycle_source`, `/root/r123_entry_lifecycle_proof`, `/root/r123_lifecycle_review`.

No source, Lean declaration or model was changed. No build, test, Lean, checker, compiler, source execution, storage/environment probe or dirty/quarantined source read occurred. `python3 tools/agent_sprint.py check` passed as static consistency evidence only; it is not proof or independent review evidence.

## Disposition

Close R123 conditionally. Keep SCC/traversal uniqueness, transaction/undo correspondence, concrete Rust-to-R39 projection, R121 consumer read, R111 verification resource, parent soundness, full effect hygiene and production OPEN. Rust solver/runtime source integration remains **NO_SAFE_CODE_SLICE** under current gates. The user's ongoing Rust/Lean goal remains active; next action is dispatcher selection of the next useful bounded path, without creating another conditional model for these same missing owners.

The exact R123 Git packet is limited to this outcome, the two frozen handoffs, and the primary-owned current-state record. No dirty solver files, quarantined runtime files, or unrelated untracked artifacts are included.
