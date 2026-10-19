# R100 implementation assessment

Sprint `method-body-source-consumer-20261019-r100`, contract revision 4,
SHA-256 `f9dd7e0d6283770616993dcb93388fe2fc884665346ac8f632e1d6bbfb47034a`.
Assignment `R100-IMPLEMENTATION-ASSESSMENT`; handoff revision 1. Author:
`/root/r100_member_impl_audit`; current R100 session
`current-conversation-2026-10-19-r100-method-body-source-consumer`.
Requested model/effort: `gpt-6-luna`/high (per Luna's assignment). Observed
model/effort: UNKNOWN/UNKNOWN. Exact write lease: this handoff only. No code
authority.

## Outcome

**NO_SAFE_ROLE_CODE_SLICE.** R85 remains Draft and unadopted. The inspected
owners expose source evidence and ordinary consumer behavior, but they do not
provide a safe role-specific production slice: P2 authentic member body and
binder/environment materialization, P3 source-qualified receiver-first Apply
construction, and P4 complete candidate/runtime target admission depend on the
unresolved R85 adoption boundary and missing owner-local producers. No semantic
or runnable-role claim follows.

## Frozen inputs and prior evidence

Read-only SHA-256 revalidation matched all directly used pinned dependencies:

- R85 positive contract (Draft):
  `notes/design/2026-10-19-r85-role-call-positive-contract.md`,
  `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`.
- R95 source closeout:
  `notes/progress/2026-10-19-r95-final-source-correspondence-verification.md`,
  `dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1`.
- R93 associated-member source note:
  `notes/theory/2026-10-19-r93-associated-member-source.md`,
  `6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c`.
- `crates/yu-hir/src/shadow.rs`:
  `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`.
- `crates/yu-hir/src/module.rs`:
  `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`.
- `crates/yu-hir/src/module/local_source.rs`:
  `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786`.
- `crates/yu-solver/src/candidate_source.rs`:
  `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`.
- `tools/inference-playground/src/runtime/program.rs`:
  `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`.

Reused R93's paired-constructor and same-parse association result only for the
source inventory boundary. It establishes retained source occurrences and
borrowed associated pairs; it does not establish semantic member resolution or
consumer construction. Reused R95's focused source correspondence as bounded
evidence about syntax occurrence identities/ranges, not as method typing,
dispatch, or execution evidence. R84's source-to-runtime map was reused to
locate the open P1-P4 producer seams; its ordinary Apply/runtime behavior is
conditional on an authentic producer. No withdrawn Simple-sub bypass or
standalone same-spelled binding is used.

## Owner-by-owner comparison with R85

1. **`shadow.rs::with_associated_method_role_sources` (source occurrence
   bridge).** The complete method validates the retained FieldTail and
   RoleDeclaration/ImplDeclaration inventories against keys from the same
   `ParsedFile`, associates outermost operator roots, pairs HIR/provenance
   trees, and publishes borrowed source views only after all checks. It does
   not construct a semantic role/member/implementation identity, select an
   implementation, or materialize an executable member body/environment.
   This is useful source evidence for R85's P2 input, while P2 itself remains
   open. Safe next dependency: an adopted source judgment and a separately
   leased HIR member resolver/materializer with unique target, actual ordered
   binders, body root, lexical environment and original annotations.

2. **`module/local_source.rs::Formation::expression` and `LocalSourceForm`.**
   The enum has `Operation` and ordinary curried `Apply`, but no role-member
   form. For an operator chain, the first `PathTail` is treated as an
   operation tail; the branch reads `Family::member`, resolves it through the
   operation namespace, and stores `LocalSourceForm::Operation`. Remaining
   accepted call tails are folded into `Apply` nodes around that head. Thus
   this path can represent ordinary application of a resolved operation, but
   does not make the exact `SecondInt::second` member a selected executable
   callee or preserve a role-member target in the Apply chain. R85 P3 remains
   open. Safe next dependency: the adopted exact source judgment plus an
   authorized HIR/LocalSource producer that emits
   `Apply(Apply(C_member, E_receiver), E_argument)` with original operands,
   source provenance and caller environments.

3. **`candidate_source.rs::preflight` and `Plan::emit_candidate_source`.**
   Preflight accepts only resolved, monomorphic supported effect operations
   and rejects unresolved/ambiguous names and unsupported forms. The emission
   branch for a resolved `Operation` emits ordinary signature facts and an
   `Action::Operation`; the ordinary `Apply` branch emits the existing Apply
   recipe and its scoped admission work. Neither branch receives validated
   role/member target metadata, body root/environment ownership, or a complete
   role-target certificate. This owner cannot close P4 from the current
   LocalSource input. Safe next dependency: producer-owned target metadata,
   ordinary endpoint evidence and a leased candidate admission path that
   authenticates completeness before publication. Do not reuse the
   effect-declaration exemption.

4. **`runtime/program.rs::RuntimeProgram::from_hir`.** The consumer obtains
   each ordinary HIR-owned `LocalSource`, builds code from its existing forms,
   translates `Apply` to `Instruction::Apply`, and `Operation` to
   `Instruction::Operation`. It has no validated role-target table or
   selected member body/root metadata. This is an ordinary consumer only, not
   evidence that the exact role call reaches it. Safe next dependency: a
   separately authorized complete source/candidate projection and target
   validation before RuntimeProgram publication.

## Parent application, remaining premises, and falsifier

The implementation assessment supplies owner-local evidence that the exact
current path stops before R85 P2/P3/P4. R85 remains unadopted; original
Simple-sub/evaluator A/B, F1/FK1 and R50 remain unchanged and open. R92's
ordinary/effectful stdout `23` remains the prior runnable-surface baseline and
was not rerun or counted here.

The narrow missing premise is an adopted source judgment authorizing this
exact role-qualified member relation, followed by separately owned producers
for authentic member identity/body/environment and source-qualified receiver-
first Apply (P2/P3), complete candidate admission (P4), and matching runtime
publication. A falsifier for this assessment would be an existing path that
authentically lowers the exact `ImplDeclaration` member into the executable
binders/body environment, emits both receiver-first Apply edges from the exact
qualified occurrence, and admits its complete selected target into runtime;
the inspected owners contain no such route.

## Checks, budget, and stop

Allowed read-only inspection only: `cat`, `rg`, `sed`, and `sha256sum` against
the pinned contract, prior evidence and exact source owners listed above.
Dependency hashes matched. No tests, builds, CLI/runtime execution, compiler
commands, formatter, Git, source/test edits, scratch files or descendants.
R100 implementation-assessment cap: 360 seconds charged at grant; exact
elapsed resource use UNKNOWN. No test/check budget used.

New path: this leased handoff only. No generated or disposable scratch paths.
**STOP / writes stopped at frozen handoff.** This producer does not certify
its own work. Luna owns independent review and any subsequent authority/lease.
