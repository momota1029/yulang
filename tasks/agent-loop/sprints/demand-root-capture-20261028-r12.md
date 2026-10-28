# DEMAND-ROOT-CAPTURE-CORRESPONDENCE/r12

Status: ADMITTED BY LUNA. New packet after R11 `CLOSED_INCOMPLETE`; it continues the same original bounded source/native diagnostic goal and does not revise R11. Baseline `7b3ad7074`. R11 outcome SHA-256 `838204e0451b52eda3a7b23baa01710f65af587992008ada168e8c1c7eb756a9`; R11 review `0f55499d141b85e4b3abc74b2e362a1cf9ce0f75f7b663a6faa26d8421c8242a`. Input manifest `tasks/agent-loop/sprints/demand-root-capture-20261028-r12-inputs.json`, SHA-256 `996d23a3f86541608bc7967658ceee9e29b128a95153fe6a60c26a00ef2ee05b`; 104 entries, 104 unique paths at preparation. The R12 clone contains R11 Cargo-1 logs at its inherited `logs/cargo-1.*` paths; those are immutable inputs. The R9 original Cargo logs are separately pinned at their original paths.

## Fixed goal and bounded outcome

Resolve the R11 FreshUse coverage seam: when a retained captured bound contains `Some(ScopedDemand)`, establish whether its deferred demand root has a same-capture reconstruction node and an authentic source/use/bound antecedent. Trace this relation from latent demand-root discovery through capture `formal_domains`, `negative_formal_roots` construction and FreshUse lookup. Determine the responsible invariant/owner and whether an isolated candidate repair follows from existing source authority, or return the exact missing premise/owner. A passing test alone does not close a source theorem.

Keep the original `YulangClosure.SourceProblem.InferenceSoundness`, quantifiers, source domain, shared source witness, immutable-birth Value qualification and effect-hygiene policy fixed. Parent, full source/native correspondence, effect hygiene and production remain OPEN.

R11 established only this finite native observation: in invocation 1, `prepare_candidate_fresh_use` sees a bound `Some(ScopedDemand)`, but lookup of `demand.root` in `graph.negative_formal_roots` returns `None`; the same invocation's `session.execute` returns `Err(ReceiptMismatch)`. Capture `formal_domains` constructs the map; latent demand discovery interns roots separately. R11 did not record the graph, root, bound/relation, source occurrence/use or antecedent. The reason for the missing root remains unknown.

## Frozen inputs and leases

The 100-entry manifest inherits R11's 90-entry cone, remaps the immutable workspace snapshot into `isolated/demand-root-capture-r12/`, and pins R11 final Rust outputs, handoffs, review, outcome and exact Cargo trace. All three R11 Rust source files are immutable inputs. Only the R12 `candidate_scheme.rs` copy is writable; `candidate_context.rs`, `candidate_extrusion.rs`, and every dependency remain read-only.

## Lanes and resources

Fresh aggregate envelope **3,000 seconds**, no renewal: Luna implementation 900s, registered `lean_prover` Sol/high source/proof lane 900s, independent review 600s, Luna primary checks/integration 600s; Astra 0. Implementation and proof may proceed in parallel from exact immutable R11 inputs. Reviewer performs source-first review before checks and final log/result review after checks.

- Implementation writes only `isolated/demand-root-capture-r12/crates/yu-solver/src/candidate_scheme.rs` and `tasks/agent-loop/inbox/demand-root-capture-r12-rust.md`. Add test-only, same-invocation observations sufficient to join the failed demand root to source occurrence/owner, graph identity, root and polarity/scope, bound ordinal/relation, complete `ScopedDemand`, context use, captured/imported antecedent, reconstruction node/index and formal-map membership. Preserve fixture, assertions, error kind and ordinary control path. Record owner-returned indexes; do not infer or fabricate mappings from equal-looking identifiers. All log formatting/allocation stays dormant outside the exact trace scope. Do not modify `candidate_context.rs` or `candidate_extrusion.rs`.
- Proof/source writes only `tasks/agent-loop/inbox/demand-root-capture-r12-proof.md` and, only if a source-derived conditional theorem is available, `isolated/demand-root-capture-r12/notes/theory/lean/YulangClosure/DemandRootCaptureR12.lean`. Work from immutable R11/R10 sources. Establish the latent-demand discovery → capture → map construction → FreshUse correspondence and apply the actual trace to the original source occurrence, use and antecedent. If the required source law is missing, identify exact owner and premise. Do not assume the failure, narrow the theorem, or invent an axiom.
- A **provisional isolated semantic repair is pre-authorized only conditionally**: it may be made in the single leased R12 `candidate_scheme.rs` after the implementation lane supplies exact same-capture root/index evidence and the proof lane establishes the existing source authority/owner obligation. Preserve all fixture inputs, assertions and expected behavior. The repair must use authentic capture owner-produced root/index correspondence with matching use/scope/polarity; no blind insertion, synthesized index, or weakened guard. If either lane cannot establish these conditions, no repair is allowed and R12 records the unresolved premise. Any repair candidate is separately frozen and must receive fresh review before the second Cargo attempt.
- Reviewer is fresh `compiler_referee`, Sol/medium, maximum 600s, read-only. Authenticate all 100 pins before body reads, review source instrumentation and proof first, and issue initial ACCEPT/reject before checks. If a semantic repair is proposed, independently review its exact delta and authority before Cargo-2. After checks, authenticate all logs and outputs. Luna writes review receipt `tasks/agent-loop/inbox/demand-root-capture-r12-review.md`.
- Luna owns `tasks/agent-loop/current.json`, all check logs, outcome `tasks/agent-loop/history/demand-root-capture-20261028-r12-outcome.md`, review persistence, integration and Git. Reuse R9 Cargo cache only after current writer cessation and hashes are verified.

## Conditional checks

Only after fresh review accepts the exact frozen source/proof revision:

```text
CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target cargo test --manifest-path isolated/demand-root-capture-r12/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

At most two Cargo attempts, each at most **120s wall**, combined maximum **240s**, one CPU affinity 0, maximum **2 GiB sampled process-group RSS**. Cargo-1 is the diagnostic trace attempt. Cargo-2 is allowed only for a conditionally pre-authorized isolated repair reviewed on exact bytes. No third attempt or resource extension.

At most one Lean run, only if the proof lane produces a justified theorem artifact; max **60s**, one CPU, `-j1 -M1024`, pinned R11 Lean/Lake environment and R12 absolute artifact. No Lean execution otherwise.

Retain exact argv, complete stdout/stderr, tool versions, exit and resource JSON in:

```text
isolated/demand-root-capture-r12/logs/r12-cargo-1.argv
isolated/demand-root-capture-r12/logs/r12-cargo-1.stdout
isolated/demand-root-capture-r12/logs/r12-cargo-1.stderr
isolated/demand-root-capture-r12/logs/r12-cargo-1.resources.json
isolated/demand-root-capture-r12/logs/r12-cargo-2.argv
isolated/demand-root-capture-r12/logs/r12-cargo-2.stdout
isolated/demand-root-capture-r12/logs/r12-cargo-2.stderr
isolated/demand-root-capture-r12/logs/r12-cargo-2.resources.json
isolated/demand-root-capture-r12/logs/r12-lean-1.argv
isolated/demand-root-capture-r12/logs/r12-lean-1.stdout
isolated/demand-root-capture-r12/logs/r12-lean-1.stderr
isolated/demand-root-capture-r12/logs/r12-lean-1.resources.json
```

Absent attempt/Lean files are explicitly NOT_RUN in the outcome, never synthesized. Only exact output paths above and named lane paths are leased.

## Falsifiers and stop conditions

Reject evidence if it joins a different invocation/source occurrence/use, loses bound/root identity, mismatches polarity or scope, invents an antecedent, or records a node index not returned by the actual capture owner. A semantic repair that changes the expected fixture, assertion, or annotation permission is rejected. Stop on pin mismatch, missing source authority, source-domain weakening, changed R11 evidence, resource boundary, `sorryAx`/project axiom, missing complete theorem type/audit, or absent independent review. Preserve failures and open gates. No trace or passing finite test closes the original parent, source/native correspondence, effect hygiene or production.
