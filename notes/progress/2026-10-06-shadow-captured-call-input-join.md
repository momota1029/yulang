# Shadow captured-call input join

Date: 2026-10-06
Status: independently reviewed structural shadow slice; no blocking or major findings
Baseline: `b39ca45a0d1c88490fe6984db79e400123fab9f3`
Authority: user-approved experimental identity plumbing; no semantic or production authority

## Result

The opt-in HIR shadow now exposes `Skeleton::captured_call_input()` for the
exact represented shape selected by the nested-block addendum:

```text
root Lambda(parameter=f,
  Bind(binder=step,
    value=Lambda(parameter=x,
      Apply(Use(f), Use(x))),
    body=Use(step)))
```

The borrowed result joins the outer parameter, captured local-lambda identity,
local binding, final returned use, call expression, callee use, and capture
position. It checks full artifact-branded IDs, the exact one-element capture
list `[f]`, the direct argument use of `x`, and the final direct use of `step`.
Unsupported topology or a broken/foreign traversed edge returns `None`.

This makes the already retained lexical identities available as one structural
input record. It does not construct or assert `SourceViewInst`, formal-call
applicability, `beta`, a profile, scope/generalization identity, a typed path,
receipt, evidence root, owner/receiver, `Flow`, or a semantic judgment. The
seven pending premise rows are unchanged. Production `ResolvedExpr` and the
inference path are untouched.

## Review and verification

A pre-write spec audit required the direct `Apply.argument -> Use(x)` edge and
an exact capture list; both guards are implemented. A post-write regression
review found no blocking or major issue. It noted that tests do not mutate every
private occurrence-index invariant; those IDs cannot be forged through the
public API, and the projection uses checked lookups. The added tests cover the
approved shape, unrelated topology, pending-inventory preservation, foreign
references, wrong arguments, and missing/additional captures.

Focused check:

```text
RUSTC_WRAPPER= cargo test -p yu-hir shadow_captured_call_input -- --test-threads=1
```

Result: 3 passed, 80 filtered. `rustfmt` on the two changed Rust files and
`git diff --check` passed. Broad package/workspace checks, production behavior,
typed capture, source adequacy, principality, and theorem closure were not
tested or established.
