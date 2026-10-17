# Sprint `npair-operation-rule-completion-and-accepted-replay-20261018`

Status: CANDIDATE until Luna records live author receipts. Branch
`research/simple-sub-intrusion`; baseline `059bbab6e`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` stays OPEN with original
quantifiers, source domain and fixed-c requirement. Astra0; no rollover.

## Fixed outcome and evidence

Advance two connected but independently finishable outcomes:

1. Turn the exact missing judgment `?e_Op` in
   `notes/theory/2026-10-18-original-c-complete-output-elimination.md` into a
   concrete, falsifiable Operation fixed-c specialization candidate, using the
   existing formation proposal. State what is derivable, what is new semantics,
   all binders/licenses and complete `A_decl` output behavior, every R/W/Z and
   changed-domain action, consumer law, consistency obligations, language impact,
   and a source-qualified counterexample/falsifier. Apply it to the unchanged
   parent without counting a proposed rule as proof of the old semantics.
2. Diagnose the previous focused test's actual HIR failure and create a
   materially corrected existing-semantics fixture. From one accepted parse/HIR,
   show omitted-formal introduction -> exact Apply/native demand -> retained
   Replay -> ordinary propagated result. The matching demand row is keyed to
   the `invoke` Apply, not the outer `received` Apply. Preserve old negative
   comparator. Add one regression and one example.

Success: independent review accepts a complete candidate and states the exact
remaining adoption/parent burden; parent closure count remains 0 unless the
original fixed-c theorem itself is derived. Runtime success requires focused
test and example each exit 0 and the captured typed Replay row matches the
authenticated `invoke` call index, native demand root and ordered endpoints.
No semantic/compiler/source-admission change is authorized in this sprint.

## Pinned authorities and dependencies

| Input | SHA-256 |
|---|---|
| preceding sprint closeout contract | `2fb8ee59a8d21f96d7a418ff7ea0d6a52cadceeaa5e0220e674d2721b5256bcb` |
| preceding failure metadata | `a87c4ee1bd52123a7c2ced4e2ab2e5ea1214e9c5d088f5e65fb4bcf597f401e7` |
| original fixed-c audit | `0ab3061c26b1b5b081dcf931fb8b616d77b2d17a34ec7fe48f277b740f101b67` |
| Operation formation candidate | `7d966d665fc4a87806c4ba989bb11c8ec1fbde34a39432a31e190cf207ec1236` |
| Operation adoption decision | `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783` |
| candidate graph test baseline | `21c555b57a8684c9f8971e9180ac0ee732dc7a82834db606241653869987f55b` |
| candidate source | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| candidate call | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| candidate context | `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f` |
| shadow apply | `51d1d1534d86181dce6caf0638f5c55e7c3bad6d764c3da5c4c9af10421335ac` |
| yu-solver manifest | `7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c` |

## Lanes and exact leases

**Proof — Sol/high, cap 600s:** write only
`notes/design/2026-10-18-operation-fixed-c-specialization-candidate.md` and
`tasks/agent-loop/inbox/20261018-operation-fixed-c-specialization.md`. Build
from the missing `?e_Op` and existing formation proposal; do not repeat the
already-reviewed rule-absence inventory. Continue derivation and compatibility
analysis until the full candidate and falsifiers are concrete. Original fixed-c
identity, original dependent licenses, complete output and all alternatives
must remain explicit. No parent closure from candidate adoption.

**Implementation — Luna/high, cap 720s (includes runtime):** write only
`crates/yu-solver/examples/research_scoped_formal_replay.rs`,
`crates/yu-solver/src/tests/candidate_graph_call.rs`,
`notes/progress/2026-10-18-accepted-scoped-formal-replay.md`, and
`tasks/agent-loop/inbox/20261018-accepted-scoped-formal-replay.md`. First
diagnose the prior `hir.errors()` failure from pinned logs and actual HIR
producers. Do not merely suppress the assertion or guess a parser fix. Use the
existing HIR helper and accepted fixture idioms; report actual diagnostics in
any failing assertion. No edits to compiler implementation, expected outputs,
source admission or solver semantics. Show real constraint/propagation consumer
results in the same HIR and tie Replay demand to `invoke`.

Primary-owned receipts:
`tasks/agent-loop/runtime/20261018-accepted-scoped-formal-replay.meta.json`,
`.test.stdout.log`, `.test.stderr.log`, `.example.stdout.log`,
`.example.stderr.log` in the same directory. After frozen independent CLEAN
review and a fresh >=120s capacity check, run each exact command once,
sequentially, timeout <=120s:

```sh
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib
timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay
```

Any command failure means stop and preserve full output; no retry.

**Review — fresh independent proof review 180s and compiler/regression review
180s.** Review frozen authored artifacts and exact dependencies. Proof review
must challenge same-c identity, binder/license dependence, complete-output
action, every original alternative, and actual consumer compatibility. Compiler
review must check HIR diagnostics/source owner authenticity, actual consumer
propagation, runtime row identity and noninterference. Neither review closes
parent theorem.

Global cap 1920s: proof600 + implementation720 + reviews360 + Luna primary120
+ reserve120. Reserve 240 seconds of implementation allocation for the two
runtime commands. Astra0. No rollover. Stop authoring when less than 600s global
capacity remains; prioritize review/runtime/closeout. STOP on a true source
admission/semantic boundary, dependency mismatch, failed command, writer
cessation uncertainty or budget boundary. Other lane continues when safe.

## Parent and closeout

Keep F1, FK1, P3/P4/P5/P6, N-Transport, complete Call, soundness, principality,
termination and production/cutover separately OPEN. A candidate, local fixture,
conditional lemma, static review, or green test does not prove the original
claim. Apply any derivable original-rule result directly to the unchanged parent.
At the next material boundary consult `next_action_selector`; closeout reports
only original conditions genuinely closed, newly working implementation/test
behavior, and the next exact open premise.
