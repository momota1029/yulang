# Ordinary HIR recovery expectation rerun

After the fresh CLEAN delta review, Luna ran the single authorized HIR
integration command once:

```text
timeout 45s cargo test -p yu-hir --features shadow --test ordinary_application_admission
```

Exit 0 in 1.444s: **9 passed, 0 failed**. This includes
`unsupported_and_recovery_bodies_keep_the_whole_body_refusal`; the repaired
`broken` binding checks passed along with the retained no-Apply,
nonempty-cause, no-UnresolvedName, and unsupported-sibling assertions.

The compiler emitted three existing dead-code warnings for the payloads of
`AssociationProvenance::Token` and `Synthetic`, and `replace_admission_root`.
Compilation and execution succeeded; these warnings are not test failures.

This is candidate HIR regression evidence only. It closes no original theorem
condition and establishes no source/native correspondence, Call theorem,
F1/FK1, N-Transport, soundness, principality, termination, or production
promotion. The held solver vertical is authorized once after this PASS.
