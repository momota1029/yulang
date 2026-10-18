# Sprint R38 — ordinary Call result owner and typed port

Status: CANDIDATE until Luna freezes hashes and issues the exact leases below.
Branch / baseline: `research/simple-sub-intrusion` / `887eed4370278cd9e789fb2b9b10ff58369da540`.
Authority: `notes/design/2026-10-08-call-source-interface-definition.md` §§3–4; `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §3.3; unchanged original full Yulang inference/executor theorem and Simple-sub A/B contract.
Revision: 1. Astra0.

## Original outcome and success evidence

Original parent remains the full inference/executor theorem, with unchanged source domain and quantifiers: recursive worlds, both frames, aliases, arbitrary W, complete Call/effects, F1/FK1, N-Transport, soundness, principality and termination. Do not narrow any claim. R37 ends `0→0`; its frozen, unexecuted test candidate and two BLOCKED review results are dependencies only.

R38 targets the first direct source/native edge at exact `q = loop y`: ordinary Call's result description. Determine whether existing adopted rules derive an owner-introduction plus `Desc(C,q,sort,sigma,Delta)` for the full ordered dependent telescope and a typed field correspondence to both `ApplySourceInput.result` and `NativeInterface.result`.

Success evidence is one of:

1. A checked derivation from existing rules with original owner, scope, sort, ordered dependencies, result-port distinction, and typed native correspondence; apply it to the unchanged parent obligation and identify the next missing premise.
2. If existing rules do not derive the record, a single explicit candidate formation rule with all operands/dependencies and an exact falsifier. This is a proposal only; it neither changes approved semantics nor counts as closing the parent condition.

Track parent condition count honestly. Tests cannot prove the source rule. Preserve distinction among source Call result, returned provider/world, receiver ports, invocation effect and native result. A `Term`, pending supplier list or candidate certificate is not the missing source typing.

## Two continuing lanes

**Proof — Sol/high, 1500s.** Construct the exact `q=loop y` result-description owner using complete Call and Generalize §3.3; inspect actual pending suppliers and source introduction. Work through related derivation stages, then apply to R's original dependency telescope. If underdetermined, draft one explicit candidate rule and show dependency order, consistency with complete Call alternatives, and a falsifier. Do not repeat conditional alias work or infer a binder from spelling/solved endpoint shape.

**Implementation — Luna/high, 900s.** In existing test modules only, establish source Apply → demand construction → `NativeInterface.result` with occurrence, source result endpoint and exact four-port projection. Keep the missing logical telescope explicitly unprovided. Add wrong-occurrence, invocation-effect, and provider/result substitution controls. If no useful owner correspondence can be encoded under existing owners, record `NO_SAFE_CODE_SLICE` with exact inspection of `candidate_call.rs` and `shadow_apply.rs`; do not manufacture a telescope. No production changes, approved expected-output changes, or bypass.

These lanes are independent through frozen artifacts. If implementation freezes first, proof continues. If proof yields a candidate rule, implementation cannot encode it as approved semantics absent a separate authority decision.

## Open premises, falsifiers, non-goals

First missing source evidence: actual ordinary Call result introduction and its source scope/complete ordered telescope. Falsifiers include missing/reordered dependency, inaccessible binder, conflation of body result and invocation result, wrong occurrence, wrong result port, or unsupported dependency inferred only from endpoint solving. If no rule owner supplies the record, retain the exact gap.

C/D CopyScope, typed publication, general source/native correspondence, both original frame joins, theorem soundness/principality and production promotion remain open. Do not alter existing Call meaning, source domain, A/B, expected outputs, theorem quantifiers or the accepted inference/executor behavior.

## Resources, leases and verification

Cap 4080s, Astra0: proof1500, implementation900, independent falsification300, proof review360, compiler review300, joint spec review300, conditional focused Cargo180, Luna integration240. Charge full assignment grants. Cargo is allowed only after all applicable fresh reviews are CLEAN and Luna records a separate launch receipt; it validates native correspondence only. At most one heavy verification process. No carryover from R37. No nested CLI, extra semantic authority, wildcard paths or worker-created descendants.

Exact proof leases: `notes/theory/2026-10-18-call-result-owner-r38.md`; `tasks/agent-loop/inbox/20261018-call-result-owner-r38.md`.
Exact implementation leases: test-only sections of `crates/yu-solver/src/candidate_call.rs` and `crates/yu-solver/src/shadow_apply.rs`; `notes/progress/2026-10-18-call-result-port-r38.md`; `tasks/agent-loop/inbox/20261018-call-result-port-r38.md`.
Reviewer receipts are returned read-only to Luna; no code, central state, or each other's output files.

Direct dependency hashes: `candidate_call.rs` e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479; `shadow_apply.rs` 5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb; Call source definition 20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c; Generalize proof e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240; R37 closeout 5c1aa3ea9f653a73d5f7466f61f9cbc32bc641fcc56ac5eeed6ff3da201f1d44.

## Frozen seam and integration

Freeze exact artifact/dependency hashes and writer-stop receipts before review. Proof reviewer must check dependent-context formation, telescope completeness/order and parent application. Compiler reviewer checks source event/port correspondence and all consumers. Joint spec reviewer checks consistency with the complete Call source contract and expected-output protection. The falsifier independently searches for counterexample or missing owner input. Any blocking finding stops Cargo. Luna integrates only exact reviewed paths, checks the entire outbound diff and records original conditions closed (if any), implementation behavior, remaining premise, checks, hashes, and Git result.

Current baseline HEAD: `887eed4370278cd9e789fb2b9b10ff58369da540`; source/spec changes require a new frozen contract revision. A candidate rule may be drafted without adoption; adopting it as language semantics is outside this contract and requires a separate authority decision.
