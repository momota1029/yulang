# Shadow join to frozen infer application provenance

Date: 2026-10-06
Status: regression-audited M1 shadow-only structural/provenance join
Yulang3 baseline: `060cc3f22ef004add6d083f800a1cd8443713795`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: explicit user authorization for shadow/differential work; no Oracle semantic authority

## Result

Captured one ordinary source application from a completed Frozen Oracle old-infer
run for the exact 38-byte, no-final-LF source
`my apply f = { my step x = f x; step }` (SHA-256
`09bdb9b3f976e40c70990336c3d7358909a3fe2cc3a1e7224425520bd21e8177`). The old
run reported no lowering errors and one source `ApplicationProvenance`: its
expression was an `App`, its callee was a direct `Var` resolving to local `f`,
and its whole/callee source spans were `47..50` and `47..48`. The old root
scheme display was `('a -> ['b] 'c) -> 'a -> ['b] 'c`; the test keeps that as
opaque historical metadata and never compares its meaning or shape with a
successor result.

The old source-text entry adds a 20-byte implicit prelude to these recorded
spans. After removing that known prefix, the whole application is `27..30` and
the callee is `27..28`. The new focused test joins these spans to the current
shadow `ApplicationSourceOccurrence`, resolved outer binder `f`, exact
`CapturedCallInput`, and `IncompleteDerivation::PendingCall`. The seven
application premises remain borrowed and byte-for-byte/identity-stable before
and after projection. Changed LF and trailing-space source bytes are rejected
after constructing each variant's own validated input.

This extends the prior frozen displayed-tree differential with provenance from
an actual completed old inference result. It compares source ownership and
retained identity only. The successor call remains pending: no scheme equality,
typed capture, profile, call-view judgment, semantic discharge, source
acceptance theorem, soundness, principality or source adequacy follows.

## Capture and verification

The capture used a scratch copy of the pinned Oracle checkout with a temporary
example invoking `yulang::source::build_poly_from_source_text_with_embedded_std`.
The original `/tmp/yulang2-oracle-rebuild` checkout remained clean at the pinned
commit. Captured outputs were `errors=[]`, `file_count=41`, one source
application at `ExprId(8396)`, `App(ExprId(8394), ExprId(8395))`, and callee
`Var(RefId(3452)) -> DefId(2286)` labeled `f`; old root scheme display is
recorded above. The helper ran in one Cargo process with two build jobs. The
capture inspected only the public old provenance/result surface and was not
used as a semantic oracle.

Regression auditor PASS on the test SHA-256
`5a94f4e3de6b208c116008b1342882e73943c16176a0a1f6a8c76841b857b0a4`, within
the structural source-range, identity, mutation, pending-premise and feature-
gate scope. A later comment-only edit added the exact source SHA-256; primary
inspection and scoped `git diff --check` cover that delta.

Focused check before that comment-only edit:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_legacy_application_provenance -- --test-threads=1
1 passed
rustfmt --edition 2024 --check --config skip_children=true crates/yu-core/tests/shadow_legacy_application_provenance.rs
passed
git diff --check -- crates/yu-core/tests/shadow_legacy_application_provenance.rs
passed
```

No current production HIR or infer code changed. No feature-off check, broad
suite, performance measurement, or inference parity experiment was run.

## Remaining work

The next experimental gate is a genuinely comparable successor judgment for
supported ordinary applications. The current production HIR still rejects the
selected nested closure source, and the experimental core builder supplies only
a structural `PendingCall`. Old scheme output remains opaque until successor
semantic judgments are independently defined and proven. Production cutover
remains gated by soundness, principality, source adequacy and the approved
production containment obligations.
