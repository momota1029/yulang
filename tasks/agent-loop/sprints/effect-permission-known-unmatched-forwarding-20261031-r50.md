# Sprint EFFECT-PERMISSION-KNOWN-UNMATCHED-FORWARDING / R50

Status: ADMITTED for the narrow R49 review correction.  
Branch: `yulang3`; keep the existing checkout.  
Authority: the user's continuing Rust/Lean effect-hygiene goal and the R49
review finding. No source semantics, language scope, production authority, or
parent claim changes.

## Objective

Repair the R49 regression where a known source-selected Catch operation that
does not match the provider is rejected instead of forwarded. Preserve the
original endpoint and all existing expectations. Distinguish three cases from
authenticated retained source evidence:

- **Match:** exact resolved handler/provider identity agrees. Suppression still
  requires the full same R45 permission, R47 entry, R48 arrival, and selected
  arm evidence; a missing or ambiguous premise stays unavailable before any
  residual publication.
- **KnownUnmatched:** both identities are independently authenticated and
  differ. Disable suppression and forward the original endpoint unchanged.
- **Unavailable:** identity/source evidence is missing or ambiguous. Do not
  infer a mismatch or publish a partial result.

Names, families, and pointer inequality alone do not authenticate KnownUnmatched.
Keep the full decision plan before any `constrain_live_effect` mutation.

## Exact lanes

Rust author `/root/r49_rust`, at most 900 seconds, writes only:

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-rust.md`

Update the existing handoff to numbered revision 2, preserving revision 1 and
correcting its `candidate_source.rs` hash to
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.

Lean author `/root/r49_proof`, at most 900 seconds, writes only:

- `notes/theory/lean/YulangClosure/AuthenticatedResidualConsumerR49.lean`
- `tasks/agent-loop/inbox/effect-permission-authenticated-residual-r49-proof.md`

Mirror all three classifications, prove a constructive KnownUnmatched endpoint
survives the fold, and preserve the theorem that every suppression requires
complete authentication. Use installed Lean 4.35.0 read-only stdin audits,
one CPU, `-M1024`, at most 120 seconds per process. Record full types, per-root
axioms, commands, hashes, failures and resource receipts.

After both authors STOP and freeze, fresh independent reviewer `/root/r49_review`
gets at most 700 seconds and writes only
`tasks/agent-loop/inbox/effect-permission-authenticated-residual-r50-review.md`
or returns a complete report for primary placement. Review the five focused
cases: signal Catch/write provider forwards; same-spelling distinct resolved
operations remain unmatched; matching operation with absent auth is
unavailable; unknown identity is never treated as mismatch; authenticated
matching suppression remains supported. Also check same-family sibling
preservation, prepublication ordering, exact forwarding arguments and the full
Lean theorem/axiom census.

## Constraints and gate

No build, test, Cargo, Lake, formatter, cache, target, scratch file, environment,
worktree, service, or nested CLI. Do not modify tests or expectations. Reuse
only the current checkout and installed tools. Do not read/release any
quarantined path. Preserve all pending and UNKNOWN state. If a needed producer
outside these exact paths is missing, stop and report the boundary.

Primary time limit is 700 seconds; total R50 budget is 3,200 seconds. The
reviewed R49 failure remains OPEN until the repaired exact source and proof
bytes pass the fresh review. Original A/B, source extraction completeness,
runtime success, complete subtraction/hygiene, and production remain OPEN.

Luna owns exact leases, intake, adjudication, staging, commit and non-forced
push. The only follow-up boundary is the fresh review result or a material
blocker.
