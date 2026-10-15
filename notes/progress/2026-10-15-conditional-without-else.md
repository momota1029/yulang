# Omitted-else conditionals for the Callback Hygiene source

Date: 2026-10-15
Status: private source construction implemented, independently reviewed and verified;
the exact Callback Hygiene program and native execution remain OPEN.
Baseline: `58b0d3760e1dde103474179ed52b1792770c9585`.

## Contract and implementation

The user's current target is the actual Yulang2 web playground **Callback
Hygiene** example, including `if i == 0: return i`. Its omitted-else form was
outside the native candidate carrier. The original language behavior is pinned
by Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`crates/infer/src/lowering/control.rs:35–48,63–68,127–136`: evaluate each taken
branch and discard its value; a normally completing conditional yields Unit.
Keep all condition/body inference constraints and effects, including branches
with constant conditions. An explicit else retains the existing value join.

Pre-write `spec_auditor` approved removing only the obsolete private-carrier
omitted-else rejection. Both interpolation rejection assertions remain.
Authority is the user's source target and frozen Oracle compatibility policy,
alongside inference top-level principles §1.1 and conditional-reference Choice A.
The earlier explicit-else envelope was not a language rejection.

HIR now stores an optional else child without synthesizing source occurrences.
Candidate construction checks every condition and body; only the no-else
body-to-result value links are omitted. Its authentic conditional occurrence
contributes Unit at slot 0. Every actual child's effect still reaches the
conditional result at child slot 51, with condition demands at child slot 50.
The Value graph retains all actual condition/body references and its existing
wrapper boundaries. No incoming Expression edge is added.

New work/storage is linear in actual children; there is one Unit fact and no
implicit child allocation. Explicit-else generation is unchanged. Independent
`compiler_referee` found no findings in the construction, slot ownership,
counters, reference correspondence or tests. This closes the local discard
construction review, not the previous universal or runtime proof obligations.

## Verification and budget

Mode M2: one implementer, pre-write spec review, one semantic closure reviewer;
convergence requires no accepted blocking/major finding and focused checks.
Cargo commands used `CARGO_BUILD_JOBS=2`, `timeout 300s`, and one test thread.
No performance experiment or benchmark was run.

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-hir --features shadow --test conditional_local_source -- --test-threads=1` | 8 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --test candidate_conditionals -- --test-threads=1` | 13 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --lib conditional_ -- --test-threads=1` | 9 passed, 685 filtered out |
| `check -q --workspace` | passed, no warnings |

`rustfmt --edition 2024 --check` on the two integration-test files and
`git diff --check` passed. Checks ran before a formatting-only test update;
no semantic bytes changed afterward. Logs are retained under
`/tmp/yulang-callback-exact-20261015/`. Broad tests, runtime tests, and global
soundness/principality certification were not run. The three previously
recorded unrelated Effect fixture failures were not rerun or changed.

## Remaining exact-source gate

The original sample additionally needs standard-module/syntax imports, loop and
range lowering with captured `h`, operation/method resolution, receiver-owned
hygiene and selective Catch handling, plus native evaluation. Those remain
separate dependencies. This slice does not claim the original program runs.
The next hygiene construction must relate the protected original `h` demand
to its receiving boundary; releasing the outer application's argument scope
does not establish that relation.
