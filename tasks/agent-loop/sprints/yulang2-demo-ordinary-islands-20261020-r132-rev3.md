# R132 rev3 — verification failure and closeout

Status: **CLOSED_FAILED_FIXED_OUTCOME**. This record supersedes neither the
frozen rev1 implementation contract nor the rev2 UI-repair contract; it records
the final outcome after both were executed. Original user goal remains broad
Yulang2 demo coverage with proof-backed implementation.

## Preserved review and command history

- R132 rev1 prospective spec review was CLEAN for its frozen contract.
- The rev1 final candidate had independent compiler/source and regression
  **BLOCKING** findings: selecting an old example retained `int_identity`.
- R132 rev2 repaired the example-change handler. Both independent delta reviews
  were CLEAN: new fixture → `int_identity`; previous examples/fallback →
  `main`; the input remains editable. The first BLOCKING receipts remain
  permanent history.
- First exact command, `timeout 240s npm --prefix web/playground run check`,
  exited 1 before compilation completed. `wasm-pack` attempted to install
  `wasm-bindgen` and failed to create a temp directory on the read-only
  filesystem (`os error 30`).
- Per the sandbox escalation rule, Luna requested approval to rerun that exact
  command through `require_escalated`, disclosing the conflict with rev2's
  no-retry clause. The user approved that command. This is a user-approved
  exception; no installation command or alternate check was run.
- The approved escalated command compiled the release WASM and built the Vite
  bundle, then exited 1 in `smoke-test.mjs` with a source diagnostic at bytes
  301..330. The exact copied countdown source
  `if flag { 8 } else { countdown true }` is rejected with a missing `IfArm`
  and a structural error. No identity output was established because the
  combined module failed preparation. This is a source-shape incompatibility,
  not a passing or failing evaluator result.
- No command retry remains authorized in R132. Browser/WASM success for the
  four-result fixture is **NOT_ESTABLISHED**. The entire 19-result demo is not
  supported. R65, R64, all theorem, adoption, source/native and production
  gates remain OPEN.

The syntax reference and `crates/yu-syntax/src/expression/if_expr.rs` make the
failure expected under current authority: expression `if` uses colon-introduced
arm bodies; braced arms are deferred to a separately reviewed language slice.
R132 does not authorize that grammar change or translation of the Yulang2
source.

## Resource reconciliation

Preserve the full 360-second R132 implementation reservation because its exact
elapsed time is UNKNOWN. Preserve 240 seconds for rev1 final review, charge the
48 seconds reported for rev2 delta review, charge the 60-second repair cap,
retain the initial 240-second check allocation, and charge the full 240-second
escalated run because its process runtime cannot be separated reliably from
approval wait. The environment exception and approval receipt consume a further
60 seconds. Inventory 120, prospective review 120, proof 279, and source audit
184 seconds remain charged. Closeout remains 60 seconds.

The documented R132 extended ceiling is 2,100 seconds: 2,011 charged or
reserved, 89 unused. No part of R114's independent unreconciled 360 seconds is
available. No R132 work may be resumed or its check repeated.

## Next boundary

The exact identity block remains a ready narrower source island with three
named values; it does not rely on braced conditionals. It requires a new sprint
contract because R132's fixed four-result outcome and verification allowance
are exhausted. Keep the failed combined fixture and its hash as evidence.

Braced `if` support is a separate syntax-design and authority proposal. The
current colon-only rule must not be silently broadened as a “small parser fix.”
