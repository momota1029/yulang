# Directional introduction playground slice

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Code baseline: `3683ed72dd862e1259e5b07f1d2e48e4f1c51704`

## Result

The private candidate now retains a source-authenticated, occurrence-specific
symbolic record for an omitted formal's original Apply upper demand. The record
joins the original omission and scope, formal registration, checking occurrence,
complete negative Function demand, designated `ResultEffect`, and raw invocation
row before `constrain_live_value`.

The scope is retained once in `FormalRegistrationInput`; observer validation
compares registration and omission scopes without traversing source bindings
(constant work with respect to binding count). The record is available through
`CandidateSourceCall::directional_introduction`
and the opt-in `yu-playground --intrusion` view. Repeated uses retain separate
checking occurrences. The captured, wrapped, composed, and known-provider
fixtures distinguish source formals from nearby endpoints and provider calls.

This is symbolic source evidence only. It does not add `ProtectedVarAt`, a
`ContextExpr::Protect` operation, a live filter/gamma consumer, Receive/Observe
events, or Catch residual activation. It does not prove all-path profile
transport, hygiene, H1/H2/U, complete Call, soundness, principality, generic
rigid opening, or production/F5 correspondence. H3/P remain disabled.

## Review and focused checks

M2 conformance review found no issues. The semantic review found one major
observation-cost issue: reconstructing scope with a full binding scan per call
made nested-use reports quadratic. The repair retains scope at its existing
source owner and rejects mismatched registration/omission scopes; focused delta
review confirmed constant work with respect to binding count and no replacement
calls-by-bindings traversal. No benchmark was needed to establish this static
complexity repair. No semantic reviewer finding remains open in this slice.

After that repair, the primary ran these bounded checks serially:

- `cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib directional_ -- --test-threads=1`: 2 passed.
- `cargo test -p yu-playground --test cli directional_introductions_show_exact_uses_and_provider_exclusion -- --exact --test-threads=1`: 1 passed.
- `cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib shadow_apply::tests::source_call_retains_registered_root_across_wrapped_and_captured_uses -- --exact --test-threads=1`: 1 passed.
- `cargo check -p yu-solver --features shadow-f5,shadow-apply-candidate`: passed.

All commands used `CARGO_BUILD_JOBS=2 timeout 300s`. No broad suite or timing
measurement ran. The implementation and this record are a reversible private
playground slice, not production cutover.

## Next gate

Establish whether and how this source record becomes live contextual protection
at the selected original upper `ResultEffect`, then connect its authenticated
position and lifecycle to the existing hygiene theorem's premises. The proof
and source audit must distinguish an exact occurrence certificate from an
executable protection consumer. Preserve the one-assignment scope and the
existing no-backflow rule; stop before residual activation if profile authority,
consumer correspondence, or transport is still missing. H1/H2/U remain OPEN.
