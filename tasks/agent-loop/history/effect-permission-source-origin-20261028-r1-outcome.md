# Outcome: EFFECT-PERMISSION-SOURCE-ORIGIN-20261028/r1

Disposition: **CLOSED_INCOMPLETE**. The broad Yulang inference/executor
soundness goal remains active. No parent theorem, effect-hygiene, A/B,
principality, termination, native, or production gate closed.

## Evidence and changes

- Corrected the internal capture fixture to use the constructor's checked
  `parameter_live_base + parameter` row and assert the exact negative domain
  term appears in the returned graph.
- Added an ordinary `CandidateInference::solve` path through source preflight,
  actual definition export, and `formal_effect_permissions`. The assertion
  checks that the same constructor term is published as a captured root and
  that the expected permissions are exported.
- Made test recorder endpoint formatting lazy when observation is disabled.
  No solver decision, source behavior, API, recovery, expected output, or
  runtime behavior changed.
- One released focused Cargo run was reported by the worker as exit 0,
  62.17 seconds, 1,652,924 KiB RSS, one CPU, three tests passed and 814
  filtered. The corrected trace named `Term { brand: TermArenaBrand(1),
  index: 286 }`, node 3, and one negative formal root. The ordinary source
  solve/capture/export assertions passed. The exact worker receipt is in the
  frozen Rust handoff, SHA-256
  `da1d12525f568a63dbc22f634a824493d571eecc71803a65f14a004423cbdd5a`.
  No raw Cargo transcript was retained; the independent reviewer therefore
  classified runtime figures as worker-reported, not raw-log authenticated.
- The proof artifact `FormalPermissionSourceOrigin.lean`, SHA-256
  `3e8ae8ba21cdaf47e1172a40d69f37a29247d2987a323e0c0746e7770ac58231`, did
  not pass its final pinned check. It failed at line 163 after 7.23 seconds,
  peak RSS 781,032 KiB, before theorem-type or axiom audits. All 12 declarations
  remain NOT_AUDITED. The frozen proof handoff SHA-256 is
  `7d4ef479f68a8865a1c3563867494dce53a4ddfe6d7f321f36850937b343e321`.
- Fresh compiler_referee review found no semantic regression in the Rust
  changes and accepted the corrected Rust observation as provisional. It also
  found a minor risk that module-wide trace events can conflate separate
  captures; owner-specific graph export assertions independently strengthen
  the finite result. Actual successful-constructor realization, row/bound/
  evidence/context recurrence, canonical transport, completed node writes,
  endpoint arrival, and universal native correspondence remain OPEN.
- The frozen sprint contract contains a one-character manifest hash typo:
  `…e68e314…`; the authenticated manifest hash is
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
  No dependency mutation was found. The prior contract remains immutable; the
  corrected pin is used in the next contract.

## Frozen inputs and review

- Contract SHA-256:
  `4158140fa23108a9be8377527854df831044de1dc4d8a06ed063cfbf44ef7130`.
- Rust sources: `candidate_effect.rs`
  `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`;
  `candidate_scheme.rs`
  `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`.
- Fresh review verdict: provisional finite Rust evidence; Lean unchecked;
  native bridge open. Reviewer additionally noted missing raw Cargo transcript
  and the manifest pin typo. Review was read-only and ran no tools that mutate
  repository or compiler state.
- `python3 tools/agent_sprint.py check` passed after primary state updates.
  `git diff --check` passed for the leased Rust source files and compact state.

All source and handoff writes are frozen. The Rust target scratch remains
primary-owned at
`/tmp/yulang-effect-permission-source-origin-20261028-r1/rust-target/`.
Unknown runtime writer paths remain quarantined and untouched.
