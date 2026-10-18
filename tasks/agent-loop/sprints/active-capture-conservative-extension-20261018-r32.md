# Sprint R32 — active-capture conservative extension and native path

Status: ACTIVE. Branch `research/simple-sub-intrusion`; baseline
`eb01835c1c78ad3566dac054c285d2a5df4d3e7f`.

## Original outcome and success evidence

Parent goal remains: implement Yulang type inference and executor with proofs.
Preserve every original source, binder, provider, scope, occurrence, event and
event telescope; complete Call/effects; full residual clauses; aliases versus
independent uses; signed pairs/equalities; and all original quantifiers. R31
left original conditions `0 -> 0` and identified the first missing adopted
judgment: the source-owned active-capture demand record/telescope for `C/D` and
its equality incidences at nested helper publication. R30's `j0/a0` guard and
same-event world-action gate remains independent and OPEN.

Fixed outcome: construct one **research-only candidate** owner record for the
missing active-capture demand, then test whether it is a conservative
definitional extension of the complete existing Call relation: erase the added
record and recover exactly the original Call judgments, and lift every
original Call witness back to a candidate witness, jointly for two independent
helper uses. If this fails, freeze the first failed direction. If inequivalent
completions both satisfy conservativity, return the semantic choice to Luna.
Do not automatically adopt a candidate, change source admission, narrow the
theorem, or alter production allocation policy.

In parallel, exercise the existing accepted-source candidate path for an active
recursive `f`, a nested helper `g` that calls `f`, publication of `g`, and two
independent FreshUses. Add only a test-scope regression using existing
observers; do not change production code or claim source-theorem soundness.

Success is one of:

1. A reviewed conservative-extension proof, with exact erased/lifted judgments
   and unchanged parent application stated; or a concrete failure showing the
   new record is not conservative.
2. A reviewed source-to-native regression path that identifies the active-root
   Link, demand generation/equality incidence, helper publication and two
   distinct FreshUse maps, with its focused test result.

Neither candidate-rule work nor a green test alone discharges an original
parent condition. Original-condition discharge starts at `0` and changes only
on an independently reviewed application to the unchanged parent.

## Governing authority and dependencies

- User's standing authorization: research interpretations and candidate
  constructions may be tried and reverted; production semantic adoption remains
  a separate reviewed primary decision.
- Source Generalize definition `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- Local self-recursive binding `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895`.
- Nested active-root derivation `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9`.
- Intrusion event qualification `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`.
- Parent-copy SCC operation `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b`.
- Native source scheduling `candidate_source.rs` `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`.
- Native publication/FreshUse `candidate_scheme.rs` `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`.
- Local source identity/resolution `local_source.rs` `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
- Generalize construction proof `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Source contract authority `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
- Exact native regression owner `crates/yu-solver/tests/candidate_local_self_recursion.rs`
  `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a`.
- R31 reviewed derivation `9ea76796b7514f71541dea5dfd9a4d1326bfbfc849e07706cbd2cd09e1663ced`,
  falsifier `4c2ddeca7bdd4e5655af069a7cfbfeab93105d76616185758e673cc9caf50041`,
  and closeout at `notes/progress/2026-10-18-r31-active-root-allocation-closeout.md`.

## Lanes and exact leases

### Constructive candidate conservativity — Sol/high, cap 600 seconds

Writes only:

- `notes/theory/2026-10-18-active-capture-conservative-extension-r32.md`
- `tasks/agent-loop/inbox/20261018-active-capture-conservative-extension-r32.md`

Construct a minimum candidate active-capture owner record from the complete
Generalize construction telescope and source Call. Prove both exact directions:
erasure preserves and reflects the original complete Call relation, and every
original Call witness admits a candidate record. Preserve dependencies,
scopes, all signed incidences/equalities, effects and both helper-use frames.
Do not pick a placement from a successful type result. If a required premise is
absent, name the exact type/index/owner; if two inequivalent conservative
records survive, provide both and the irreducible choice. Apply the result to
the unchanged intrusion/principality/N-Transport parent without claiming that a
candidate record itself closes it.

### Native accepted-source path — Luna implementation lane, cap 300 seconds

Writes only:

- `crates/yu-solver/tests/candidate_local_self_recursion.rs`
- `notes/progress/2026-10-18-active-capture-native-path-r32.md`
- `tasks/agent-loop/inbox/20261018-active-capture-native-path-r32.md`

Use the existing candidate-mode source construction and observers. Extend the
nested-helper witness so `g` has two independent local uses while it references
the single active `f` root. Assert their `FreshUse` images are distinct and
trace relevant active Link/Call and demand/equality incidence using existing
observable records. Keep assertions limited to candidate/native behavior.
Allowed focused verification, one Cargo process owned by this lane:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test candidate_local_self_recursion nested_helper_uses_active_outer_root_without_freshening_it
```

No production Rust changes, allocation-policy changes, expected-output changes,
other tests/builds, or executable probes. If existing observation APIs cannot
identify demand/equality incidences, stop and record the precise missing
observer instead of adding instrumentation under this lease.

## Review, resources, and integration

After both lanes freeze, Luna assigns fresh independent compiler and spec
reviewers, 180 seconds each. The compiler reviewer checks the source/native path,
test validity and absence of production semantic changes. The spec reviewer
checks exact bidirectional conservativity, original scopes/quantifiers and
candidate-versus-adoption labeling. Luna integrates for 120 seconds. Total cap
1,380 seconds: proof 600 + native/test 300 + two reviews 360 + integration 120.
Astra budget is zero. One heavy Cargo process maximum, owned by the native lane;
no concurrent verification processes.

The primary grants leases only after the contract, state and dependency pins are
committed. Unknown writers retain their exact paths and reservations. A changed
dependency, new source-semantic selection, extra observer/code path, or budget
increase returns to Luna. A candidate's production adoption requires a later
versioned decision and review; no such adoption occurs in R32.

## Stop, parent application, and next trigger

Stop on either proof direction failing, a missing owner field, inequivalent
conservative completions, a source/native mismatch, focused-test failure that
cannot be repaired within the test-only lease, or resource bound. Keep R30
independent and OPEN. Report original conditions discharged, new tested behavior,
and the exact remaining premise. Next dispatcher boundary: reviewed conservative
completion ready for adjudication, inequivalent choices, a source-qualified
counterexample, or a material dependency/resource change.
