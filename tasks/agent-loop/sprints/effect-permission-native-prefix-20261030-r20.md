# Sprint EFFECT-PERMISSION-NATIVE-PREFIX/20261030-r20

Status: ADMITTED; conditional source/native evidence only  
Branch baseline: `871de7c6dca9c2645ad10bad231f05c46392b244`  
Authority: continuing Yulang Rust/Lean inference, executor soundness, effect correctness, principality and termination goal  
Decision: R20 selector proposal; admitted by Luna  

## Parent and unchanged scope

The original supported source domain, Simple-sub A/B claims, quantifiers, accepted semantics and full parent theorem stay unchanged. Inference/executor soundness, effect hygiene, principality, termination, native correspondence and production conformance remain OPEN until their separate obligations close. R19 proves only a conditional journal-presence projection. R20 does not promote that result or make a production change.

## R20 outcome

Authenticate one real source-to-native selected call on an ordinary candidate entry route, including the complete executed SCC graph-plan prefix, and connect the *same observed native tuple input* to R19's Lean `atCallInput`. The selected call is the positive scalar-tuple `intern_structure` route used by a source formal annotation without a top-level effect annotation.

A successful trace must identify one source module and occurrence, ordinary public candidate entry, generated SCC plan, every executed plan item and member/provider action before the selected action, the selected formal-annotation action, and the actual term-arena call. It must record both journal owners (session route journal and arena mutation journal), every begin/finish and intervening writer, transaction tokens and before/after presence, plus the actual selected `TupleInput` fields before mutation. Prefer a real earlier member/provider; report actual coverage if the chosen source has none. No unclassified intervening call or inferred event may be omitted.

The Lean lane must define an interpretation for the frozen observed trace, derive both journal projections from initialization and its event transitions, and prove field-by-field equality between the observed selected input and R19's `atCallInput` for that trace. Apply `selected_call_excludes_R18` only after this equality. Do not assume an empty caller frame, journal absence, matching source occurrence, or input equality. A model projection without authenticated equality fails the outcome.

Independent falsifiers: a missing/reordered plan event; unclassified member/provider call; mismatched or unclosed transaction token; source occurrence mismatch; unaccounted writer to either journal; or any mismatch in the native tuple input invalidates correspondence. On failure, report the first missing source edge and retain R19's relevant premise as OPEN.

## Rust lane and exact outputs

Use the detached worktree `isolated/ep-native-r20/project` at the branch baseline. Its five source files were initialized from and authenticated against the R19 frozen workspace snapshot. All Rust edits and execution stay in this worktree. Keep observation test-only or otherwise provisional and behavior-neutral; do not edit production semantics, expected output, the main worktree, or a quarantined path. Invoke one ordinary supported source module through the normal candidate entry. There is one serialized offline locked Cargo invocation, at most 180 seconds, one CPU, <=2 GiB RSS and only if available memory is >=4 GiB. Preserve exact argv, complete stdout/stderr/status/resource observations, and the machine-readable event trace.

Rust writer `/root/effect_permission_native_prefix_r20_rust` has these exact write leases:

- `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_effect.rs`
- `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/ep-native-r20/project/crates/yu-solver/src/candidate_source.rs`
- `isolated/ep-native-r20/project/crates/yu-solver/src/lib.rs`
- `isolated/ep-native-r20/project/crates/yu-solver/src/term.rs`
- `isolated/ep-native-r20/project/receipts/native-prefix-receipt.json` (complete trace, raw Cargo streams, status, argv and resource receipt in one authenticated JSON object)
- `tasks/agent-loop/inbox/effect-permission-native-prefix-r20-rust.md`

No directory-wide lease is granted. `Cargo.lock`, manifests and every other worktree file are read-only. No Git operations, descendants or changes outside these exact paths.

## Lean lane and exact outputs

Lean writer `/root/effect_permission_native_prefix_r20_lean` reuses R19 unchanged and writes only:

- `notes/theory/lean/YulangClosure/FormalPermissionNativePrefix.lean`
- `tasks/agent-loop/inbox/effect-permission-native-prefix-r20-proof.md`

Use Lean 4.35.0 in an isolated project. Build a trace transition model and theorem interface from the concrete owners in the pinned Rust sources; do not duplicate R19 or weaken its theorem. Coordinate only by reading frozen R20 source inputs and the Rust lane's frozen handoff/trace after it is complete. Do not treat the pending trace as an assumption. At most two serialized Lean audits total, each <=90 seconds and <=120 seconds combined, <=1 GiB RSS each. Capture exact theorem types and complete per-root axiom reports. Any changed inherited proof dependency needs a versioned successor and a fresh audit; do not edit R19 or its imported frozen closure.

## Review, boundary and resources

After both lanes freeze, a fresh nonauthor `compiler_referee` reviews source deltas, all raw receipts, event completeness, trace-to-source fidelity, theorem statements, axiom reports and the exact residual premise. Primary Luna authenticates hashes, adjudicates, updates current state, writes the outcome/evidence, and alone stages, commits and pushes coherent reviewed checkpoints. No production permission consumer slice is authorized by R20.

Total active envelope: 2,400 seconds (Rust 900, Lean 900, review 300, primary 300); zero Astra; at most two concurrent producers and one later reviewer. Cargo attempts: one. Lean audits: at most two. Stop on falsifier, exact budget, user STOP or session end. Unknown writers retain their quarantines. R20 can at most establish one source-qualified native call trace and its conditional Lean application; original parent and production remain OPEN.
