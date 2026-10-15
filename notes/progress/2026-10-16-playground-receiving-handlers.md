# Playground receiving views and primitive operation handlers

Date: 2026-10-16
Branch: research/simple-sub-intrusion
Baseline: d40452204; independent native research checkpoint f75299ea4
Status: local receiving/primitive discard-selection implementation and proof
complete; raw Resume and whole-language parents remain OPEN.

## Authority and implemented scope

Existing receiver-relative protection/permission decisions, typed-boundary §6
and the shallow-handler charter govern this slice. No new language decision is
introduced. The [receiving theorem](../theory/2026-10-15-runtime-receiving-view-construction.md)
derives the original local positive Grant and its corrected actual source bridge.

Original Lambda/formal annotations supply ground Int Computation schemas. Entry
creates a fresh original receiving boundary; immutable views retain known
ancestry and unknown inherited coverage. Direct formal-Name delays preserve
their proved root dependency. Entries/reads create authentic receipts; execution
creates event observations before unwind. Value, view, receipt, receiver,
execution and Catch-installation identities remain distinct.

Observe and Receive join on the exact same view independently of the observing
read's owner. Original receiver activity and written permission are checked at
the reached Catch. A known local Grant permits selection despite unknown older
coverage; absence of that certificate never proves nonprotection.

Ordered exact-operation selection checks primitive Value payloads
(Unit/Int/Bool/Str), total binder/wildcard payloads or empty-call wildcard, and a
wildcard continuation. Empty-call does not impose Unit matching; discarding the
continuation imposes no Int-response restriction. Selection drops the selected
shallow handler and captured suffix before executing its arm. Abandonment clears
only captured pending GlobalRead/Root cache-write owners, preserving live outer
initializers and never caching the arm result as the abandoned global. This
cache theorem explicitly excludes Resume.

## Review and repairs

M3 covers the material receiving-authority and repeated ancestry-query risks.
Reviewers: `runtime_semantic_review` (compiler/proof), `runtime_contract_review`
(specification/public contract), `receiving_cost` (resources).

Accepted majors were repaired at their owners: unchecked primitive payloads;
stale cache markers after suffix abandonment; Unit-operation/empty-call coverage;
repeated ancestry-query work; and the observing-receipt-only join. The last
counterexample executes an outer received view through a helper: its observation
must join the live outer receiver's existing receipt. The exact positive case
and the nested-helper-own-Catch negative both pass. Final code, proof, contract
and resource deltas are clean; producer notes alone did not certify closure.

## Cost and verification

Binary target lookup, one permission check, bounded receipt lookups and shared
ancestry visitation give expected O(log B + P + V + U) query work, plus aggregate
formal-key hashing/equality when identity size is not bounded. Temporary space
is O(U). Receipt indexing adds expected amortized constant insertion per
fixed-size key and O(K) persistent storage for distinct owner/view/formal keys.
Production queries never scan historical receipts. Structural fixtures measure
image visits only; source loops bound other work. Timing samples/processes: 0/0.

- Final `CARGO_BUILD_JOBS=2 timeout 300s cargo test -p yu-playground -- --test-threads=2`:
  72 passed, no failures/warnings, including 15 receiving integration controls.
- Earlier focused 14 receiving cases and full 71 tests passed; superseded by
  the final repaired 72-test run.
- `CARGO_BUILD_JOBS=2 timeout 300s cargo check --workspace`: passed without
  warnings before the final private receipt-index repair. Final package tests
  rebuilt that repair; no repeat workspace check after local/record edits.
- Exact touched-file rustfmt and `git diff --check` passed.
- README relay stdin example through candidate inference and `--run main -`:
  exit 0, output exactly `7`.

One primary serialized Cargo with two jobs. Logs:
`/tmp/yulang-playground-receipt-final.log` and
`/tmp/yulang-workspace-receiving-final.log`. No broad workspace test suite ran.

Final hashes: machine `bac47d83a5f928bb30cb73df830048f9f57d9041fbc2cac2bc965dde10a7cdc8`,
receiving `dcd40e9ff0eae587339825d5e434d627269b6f56e2aa61990230fd5dd7af0fe1`,
tests `d2b2172154598a4e76ca6777f2042c19e4e85be4ced00eea63c1801b75da5732`,
program `984efecac3257976b87c24c851f2f3d1e5a5a762bfcaaa92b572ac75000591ea`,
mod `72b8963d42e6bb6c92914f13f5b96d2e33ecfd865a17836b2f046534303c053c`.

## Remaining gates and records

Raw Resume, nonprimitive/Computation payload selection, general negative/inherited
profile completeness, Function/B, native joint result interpretation, full
hygiene/soundness/principality and F5 cutover remain OPEN. Missing evidence is
tool unavailability, not source rejection. Reusable templates proceed under
existing rules; cache-bearing Resume alone awaits the separate pending
definition-materialization decision. The no-Resume cache theorem is not extended.

README, tasks/current.md, tasks/research-lab.md and notes/design/INDEX.md are
synchronized. Pending question files are excluded from this commit.
