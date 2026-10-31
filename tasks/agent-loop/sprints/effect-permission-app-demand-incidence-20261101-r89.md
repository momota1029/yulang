# Sprint R89 — authenticate the source App-demand constructor

Status: candidate pending primary pinning, compact-state update, exact leases, and pushed admission.
Branch / baseline: yulang3 / e56d1b618c2025859f5ab912d7ba3168634aaaed.
Authority: continuing user goal for Rust and Lean soundness, with effect hygiene; original source-preservation theorem; immutable birth-level qualification; R88 reviewed bounded obstruction.
Contract revision: 1.

## Fixed outcome

Trace the actual producer chain behind R88's missing equation:

1. candidate_source creates ApplySourceInput and retains the recipe source-input index.
2. shadow_apply::admit_candidate_fact, Apply branch, joins formal-name registration to omitted_formals, constructs DirectionalIntroduction, and installs it.
3. candidate_call retains/authenticates input and introduction provenance.
4. candidate_context_seed slot 0 consumes introduction.demand to construct ScopedDemand.

For the actual constructor path, match each retained identity, operand, telescope, effect port and qualification field against one original App/Call witness, all original checks and the complete source effect obligations. Preserve absent-introduction cases, written annotations, value and effect ports, argument evaluation, application and result effects, provider/capture identity, publication incidence, and lawful-use allocation.

Return either a source/native incidence equation supported by the actual constructor, or the first absent original supplier with exact owner and dependent fields. Do not infer source meaning from symbolic IDs, a Boolean qualification, receiver residual publication, or native metadata alone.

In parallel, construct a repaired, clean Lean App inversion in a new artifact, preserving R88's four theorem statements and complete premises. Apply it only to the constructor evidence actually established by the source lane. No assumed bridge, weakened quantifier, arbitrary concrete Kernel, or source restriction.

Success is a kernel-checked App inversion with complete printed types and axiom audit plus a source-evidenced incidence up to the first real supplier; or an exact, independently reviewed missing-supplier result with the clean App inversion. Either result is bounded: original A/B, whole source/native joint lift, Rust implementation, and production remain OPEN unless separately proved.

## Exact lanes

Proof lane, registered lean_prover, writes only:
- notes/theory/lean/YulangClosure/SourceAppDemandIncidenceR89.lean
- tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-proof.md

Preserve all four R88 declaration statements and the one shared witness. Correct the dotted-identifier ambiguity and derive app_rule from the actual sourceRules builder instead of relying on the failed rfl. Audit all theorem types and complete #print axioms. No sorry, admit, project axiom, checker bypass, Lake/build/test, scratch, cache, or project output.

Source lane, read-only only:
- crates/yu-solver/src/candidate_source.rs
- crates/yu-solver/src/shadow_apply.rs
- crates/yu-solver/src/candidate_call.rs
- crates/yu-solver/src/candidate_context.rs

Writes only:
- tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-source.md

Trace producer through first consumer and report the first absent original supplier, if any. No Rust edits are authorized by this packet. Source bytes are manifest-pinned, including dirty working-tree versions; treat them as read-only. Do not inspect or alter unrelated dirty paths.

Fresh independent reviewer, not either author, returns a read-only verdict. Primary alone writes:
- tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-review.md

## Resources and environment

Total wall-clock envelope 3,600 seconds: proof 1,400; source 1,000; independent review 700; primary 500. Astra budget 0. Proof allowance is at most two direct Lean invocations, each at most 120 seconds, pinned Lean 4.35.0, -j1 -M1024, one thread. The primary verifies the executable and exact flattened stdin hash before each call. Freeze candidate bytes and have independent pre-execution review before invoking. Record full stdout/stderr, exact theorem types and all axiom reports. Do not exceed the call cap.

No new worktree, checkout, project copy, environment, scratch, build cache, target, or /tmp output. Preserve all unrelated dirty paths, unknown writer reservations and quarantined paths. Use existing checkout. No tests are authorized or needed.

## Inputs and review

The input manifest pins the four exact Rust source files, R88 candidate and handoffs/review, original syntax/generation, and governing original source and allocation laws. Any additional dependency needs a versioned primary amendment before use.

Reviewer independently checks the actual producer chain, source telescope, all value/effect obligations, absent-introduction branch, qualification, theorem statements/types/axioms, author separation, and any claimed first supplier. Reject semantic inference from IDs or metadata alone.

Only primary owns current-state synchronization, exact leases, adjudication, staging, commit and push. Commit coherent checkpoints promptly after verifying the exact outbound range. Next dispatcher boundary: a constructed source/native incidence, a counterexample, a missing-supplier result, or material authority/resource/dependency change.
