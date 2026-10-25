# Sprint PAPER-BIND-PROJECTION-SCHEMA-20261026/r38 — let input projection

Status: READY; Luna source construction, then fresh bounded independent review.
Branch: `research/simple-sub-intrusion`
Baseline: `8e255b775` (R37 source/control result frozen; full-state projection remains OPEN)

## Fixed outcome

Construct one candidate projection schema for the ordinary bind/let first-child
case. Map the manuscript's full-state evidence to R36's `PaperCoreControl.State`
for `let x ← M in N` with `M` as the active computation. The schema must state:

1. how full-state graph, active code label, and active/saved let frames determine
   R36 `head` and innermost-first `stack`;
2. conditions under which the same typed derivation graph `G`, joint assignment
   `η`, and port table `U` are retained;
3. the actual parent-interface to child-`M`-interface restriction/transport;
4. the generated bind edge(s) and Horn-closure derivation establishing child
   concrete diagram membership from parent membership; and
5. a finite discriminator showing the schema does not derive membership when a
   required edge is absent, or the exact missing source rule if no such edge is
   authorized by the governing source.

Do not include child membership as an assumed relation field or cite it as
proved by the schema. Do not use R36 erasure equality as a substitute for a port
proof. Do not change a language rule or infer an unprinted transport.

## Authority and frozen inputs

- Manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`;
  active-child/reduction `:305–334`, frame inversion `:1014–1026`, bind graph
  row `:1520–1559`, full current evidence and parent `:1845–1907`.
- R37 boundary report, SHA-256
  `fed049b8a67f7c2a3919533ea4acf97ef3826d44715ccf2df5aaf3c6a1753b38`.
- R36/r2 `PaperCoreControl.lean`, SHA-256
  `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- R36/r2 contract SHA-256
  `84c679419e1fd4cb75f4d16e2c2b9c537f0f10e5b29ac6d5fe885e697079bfe2`.
- `PaperExecutionSyntax.lean`, SHA-256
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- R35 `PaperCoreStep.lean`, SHA-256
  `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.

## Exact leases, review and budget

Luna alone owns and writes this contract, `tasks/agent-loop/current.json`, and
`tasks/agent-loop/inbox/paper-bind-projection-schema-r38.md`. Inputs are
read-only. After Luna stops and freezes the candidate, one fresh non-author
`spec_auditor` receives a separate review report path and reviews only the schema,
source correspondence, and falsifier. No checker/cache/Git access for reviewer.
No other worker, descendant, Lean/Lake/checker, tests, Rust, implementation,
fixtures, diagnostics, expected-output or semantic changes.

New R38 grant: at most 600 active seconds total: Luna primary at most 450 seconds
and fresh independent review at most 150 seconds. Checker/native invocations: 0;
other workers: 0; Astra: 0. R37's exact active duration is UNKNOWN and its full
600-second grant is charged; R36 remaining resources are not transferred. Stop
if the 450-second primary bound or 150-second review bound cannot be established.

Falsifier: a finite candidate schema with parent membership and closure but
without a required child-connection edge still derives child membership. That
would show the proposed schema omits a real dependency; it is a discriminator for
the candidate schema, not a counterexample to the manuscript.

Before: R36 proves only finite-let syntax typing/stuttering; R37 identified no
full-state projection or child-port proof. After: one source-grounded bind
projection schema either derives child membership from an authorized generated
edge plus `F_G(U) ⊆ U`, or names the exact missing rule and owner without
asserting the parent theorem. Full state preservation, other frames,
source/native, inference A/B and production remain OPEN. `NO_SAFE_CODE_SLICE`.
