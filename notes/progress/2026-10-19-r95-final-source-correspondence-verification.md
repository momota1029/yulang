# R95 closeout: method/role source-correspondence boundary

R95 completed its single authorized bounded source-correspondence test adjudication. The code change stayed within `crates/yu-hir/src/tests/shadow_method_role_source.rs`; production `shadow.rs` remained frozen at `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`.

A fresh spec review approved the constructor-derived range law before editing and confirmed the exact frozen delta afterward. The test now checks that the first receiver HIR range equals its IdentifierExpression node range; the second continuation range begins at the previous receiver start and ends at the preceding FieldTail source end; continuation child zero is pointer-identical to the first receiver; and the provenance key resolves through the same artifact to the retained preceding FieldTail position. Field order, occurrence, source-kind, role and impl identity checks remain.

The sole authorized command ran once and passed:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`

Result: exit 0; 3 passed, 0 failed, 130 filtered. One existing `dead_code` warning for `replace_admission_root` appeared. No retry.

A fresh compiler/source reviewer independently bound the R93 implementation and proof obligations to the exact frozen implementation, found no blocking/major/minor issue, and recorded limitations in `tasks/agent-loop/inbox/20261019-r95-compiler-review.md`. The R93 proof note itself remains a candidate source proof; R95 establishes only this bounded bridge prerequisite. It does not prove method typing, lookup, dispatch, role semantics, RoleId, evaluator behavior, original Simple-sub/A-B closure, R50 adoption, R85 adoption, or production promotion. Allocation reporting limitations and untested nested/error paths remain as recorded by the reviewer.

R92’s runnable effectful example remains separately verified at CLI exit 0 with stdout `23`. The six effect-hygiene fronts remain open and independent: ordered handler priority, §21 Value/Computation entry, wrong/sibling permission, unmatched outward request plus suffix, continuation capture/resumption, and static-to-runtime projection. This closeout changes no effect semantics or adoption gate. The next sprint should rotate to one bounded effect-hygiene evidence slice, avoiding a return to effect storage/fiber-only depth.

## Frozen hashes

- R95 contract: `05eb5a3148585358e33cb573076984f07d803e71ffbd69813e7c321cd850ea29`
- production source `shadow.rs`: `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`
- focused test: `6d5c3fec7b4ca0d4618f4ad378f0ad5e8e0689b4897d406ab90d175ba78e6135`
- independent spec review transcript: recorded at inbox path; hash synchronized in current state
- independent compiler/source review transcript: recorded at inbox path; hash synchronized in current state
