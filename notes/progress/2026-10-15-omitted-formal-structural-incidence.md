# Omitted-formal structural incidence checkpoint

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Implementation base: `90401ccad`
Status: bounded, inert source-construction certificate; no effect authority

## Result

The private candidate path now retains the identity of an omitted formal at its
owning Lambda and can inspect one authentic captured-Function route to an
Argument comparison. The inspected route requires the actual
`FunctionPort(Argument, Swap)` child, both comparison Replay bounds, a retained
`FreshUse` transport from the owning Function, and the exact original raw
Function domain child. For the tested local-use route it additionally requires
the source Name's Derived edge, handoff Replay with both inputs, and a matching
slot-0 `Action::Local` occurrence.

The Lambda's one owning context seed carries both the omitted-formal
construction and the existing inferred-entry evidence. The source record keeps
the definition owner, Lambda/formal identities, source position and lexical
scope. The checker reconciles an endpoint with the current representative only
after the retained incidence chain selects it; equal endpoints do not create
source incidence.

## Exact limits

This is structural evidence only. It adds no callback position, protection
profile, grant, receiver role, Receive/Observe event, residual eligibility or
consumer authority. The inspection helper has no production semantic consumer.
Earlier extrusion, additional derived routes, dynamic evidence, arbitrary
alias/return paths, H1/H2/U and production behavior remain OPEN. In particular,
the omitted-formal matrix for `A [Ein] -> [Eout] B` remains undecided, so no
protection implementation follows from this certificate. H3/P remains disabled.

## Evidence and review

Focused regression:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_structural_incidence_survives_source_capture_without_effect_authority -- --exact --test-threads=1
```

The exact test passed once. `git diff --check` passed. An independent M3 review
set covered source/design conformance, the changed incidence and seed/caller
dependency cone, and the added resource path; no blocking, major or minor
findings remain after the bounded repairs. No broad suite, build, benchmark or
performance measurement ran. Package-wide `cargo fmt --check -p yu-solver`
reported extensive formatting differences across pre-existing files, so it
was not used to rewrite this focused change.
