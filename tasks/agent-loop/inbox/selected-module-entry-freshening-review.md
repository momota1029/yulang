Baseline admission: **REJECT pending two findings**. This delta adds test instrumentation and rewrites tests; it does not repair the production freshening operation.

Authenticated contract SHA `1091467e92e7231bc416190eb9c0727d39fadfdcafcbc78a2c1dcd4b26e40fb2` and all three assigned Rust hashes, both at initial inspection and final recheck. Complete net diffs match +719/−41, +62/−4, +7/−0 against pinned HEAD. Session `/root/selected_module_baseline_review`: started with successful authentication; review now STOPPED. No builds, tests, edits, descendants, or quarantined-path inspection occurred. Primary materialized this receipt from the reviewer's final message because its runtime instructions prohibit file writes.

1. **BLOCKING — Original regression fixture was replaced by a different recursive program.**  
   `candidate_effect.rs:3225` changes the predecessor’s `my f(...) = pair` to `my f(...) = f pair`. The predecessor test `tuple_formal_permissions_keep_element_paths_and_transaction_ownership` disappears. The replacement consumer test at line 3212 nevertheless says it preserves the original fixture. Recursive self-use changes SCC, inference and capture behavior; passing that case cannot establish preservation of the original identity-returning program and its residual-effect consumer. This violates expected-fixture protection in `AGENTS.pre-sprint.md:270` and the contract’s unchanged-source/expected-output boundary.  
   **Minimum closure:** restore the original named regression with its original nonrecursive fixture and assertions. Keep the recursive transport probe separate. Supply feature-correct verification of both after the primary authorizes checks.

2. **MAJOR — Enabling tracing introduces panics on legitimate sibling annotation paths.**  
   `candidate_effect.rs:1533` and line 1555 require every symbolic annotation memo operation to execute inside `candidate_formal_annotation`’s constructor guard. That ownership assumption is false: `candidate_formal_entry_annotation` calls the same helper at line 1809 without installing that guard. Local annotation construction at line 1985 also reaches it through `candidate_signature_value` → `candidate_signature_effect` (line 2494), or root computation checking (line 2276). With the trace enabled and constructor ID absent, the lazy event closure executes and `.expect(...)` panics. With tracing disabled it remains dormant, so ordinary untraced tests would miss this defect.  
   **Minimum closure:** record memo events only when a formal constructor identity exists, or represent the actual entry/local owner explicitly. Verify traced symbolic formal-entry and local-annotation paths complete without changing solver results. This is an observer correctness requirement, not a demand for general rollback restoration.

Other inspected points:

- New state, graph field and event emission are gated by `cfg(test)`. Event payload closures are lazy; some instrumentation bookkeeping still occurs outside them.
- Both existing explicit `Graph` literals in `shadow_apply.rs`, lines 4981 and 5094, initialize `formal_capture_trace_id: None`. The capture constructor initializes its own field.
- `Endpoint` and `Node` are `Copy`, so the new event patterns do not themselves introduce a moved-value defect.
- Canonical interning now records original row → canonical endpoint → materialized graph row; export assertions compare the exact returned port index. These are useful bounded observations, not proof of the whole dependent-map image.
- Compilation and the unequal-transport assertion remain **UNVERIFIED**, not failed by this review.

Parent, native correspondence, effect-hygiene and production gates remain **OPEN**.
