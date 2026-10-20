# R148 candidate rev6 — authentic raw-bound history to consumer

Status: **CANDIDATE; no worker, code, execution or resource authority is active.** Rev1 was rejected with three MAJOR findings. Rev2 was rejected because its output file limit also constrained build artifacts and its CPU/address-space claims were not aggregate limits. Rev3 was rejected because it omitted the 1 GiB memory scheduling profile, exact scratch-output ownership/disposition, and reliable process-group cleanup after child exit or supervisor exceptions. The rev2 pathname drifted during review; its recorded review target SHA-256 was `04aaab41a6a55d01b7ba76c894aec7f1646048e231b0c59ceaee5a7c864dcb25`, and the drifted bytes are not that target. Rev4 was rejected because the supervisor hash did not match its pin, the 120-second loop could continue indefinitely after KILL, and a second signal could interrupt cleanup. Rev5 was rejected because cleanup waits could exceed the observation deadline, Cargo build output had no exact path/disposition, and syntax/HIR source owners outside the partial pin set remained mutable. This rev6 is a new frozen candidate and needs fresh review.
Branch: `research/simple-sub-intrusion`; baseline commit
`4c9d549eab9f2ba38a2b319d4329599dd5272430`, tree
`a93b3c4d2eefdc80eb419b50d8605868d53976ea`. Luna is the primary and sole Git
integrator. This candidate continues the original proof-backed inference and
evaluator goal; it does not replace the independent unchanged-Web-sample
breadth objective. R147's braced-if choice remains pending and is outside this
packet.

## Parent and fixed outcome

Preserve the original inference/evaluator and Simple-sub A/B claims, their
quantifiers and accepted source domain. `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`,
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, source/native correspondence, and
production remain OPEN. The immediate source-evidence target is
`R146-AUTHENTIC-RAW-BOUND-HISTORY-1`: from the unchanged accepted source
`tools/inference-playground/examples/nested-recursion.yu`, obtain one authentic
production-reachable raw `Work::Bound` history, its selected physical source
slot and all relevant raw preimages, the mutation/canonicalization order, and
the actual relation-local consumer that uses the transported lineage.

The outcome is either (a) a frozen, replayable finite history whose source
constructors, solver events and consumer obligations agree, or (b) an exact
source-route obstruction showing which required event/consumer is absent. A
finite history does not close the universal R70/R71 or Simple-sub obligations.
The observation is explicitly provisional, test-only and noninterfering. No
production inference semantics, runtime behavior, expected output, schema, or
accepted input is changed. No hand-built graph or direct test-only helper call
may stand in for the source-driven execution.

## Lanes, exact outputs and authority

- Luna owns this contract, `tasks/agent-loop/current.json`, the separate
  observation receipt `notes/progress/2026-10-20-r148-observation.txt`, final
  adjudication, closeout and all Git.
- The implementation worker owns only `crates/yu-solver/src/candidate_intrusion.rs`,
  `crates/yu-solver/src/candidate_extrusion.rs`,
  `crates/yu-solver/src/candidate_effect.rs`,
  `crates/yu-solver/src/candidate_context_tests.rs`, `crates/yu-solver/src/candidate_context.rs` (test-only observer hooks and consumer capture; no production-path changes), and the exact handoff
  `tasks/agent-loop/inbox/20261020-r148-implementation.md`. Changes must remain
  under `#[cfg(test)]`; any needed production-path semantic change stops and
  returns to Luna. Its source-driven observer records completeness explicitly,
  selected raw slot/preimages, merge and canonicalization events, transported
  relation/evidence, and the eventual actual consumer. A missing or truncated
  log is inconclusive, never a pass.
- The constructive proof worker owns only
  `notes/theory/2026-10-20-r148-raw-bound-history.md` and
  `tasks/agent-loop/inbox/20261020-r148-proof.md`. It independently reconstructs
  the frozen event history from source constructors through raw-bound
  selection, transport and consumer; it records unsupported steps and applies
  any useful result to the original parent without narrowing it.
- Luna runs the one exact contracted observer against the unchanged source
  only after prospective reviews are CLEAN, implementation bytes are frozen,
  and source/dependency pins are revalidated. `CARGO_TARGET_DIR` is set to the
  exact scratch output path above; the observation receipt hashes the retained
  stdout, stderr and supervisor metadata, while the Cargo target tree is removed
  after those bounded receipts are saved. The supervisor uses one CPU
  (selected from the current allowed affinity and inherited by Cargo),
  `CARGO_BUILD_JOBS=1`, a 1 GiB aggregate process-group RSS scheduling ceiling
  sampled from `/proc` every 0.1 seconds (stop immediately above it), and a
  109-second TERM / 114-second KILL wall bound and one absolute 120-second
  deadline shared by every exception, signal and reaping path. No cleanup wait
  resets that deadline; if reaping or cessation is unconfirmed at the deadline,
  the result is inconclusive and Luna quarantines the scratch outputs. These are
  scheduling and monitoring limits, not kernel-enforced memory guarantees. It retains no more
  than exactly 65,536 bytes per stdout and stderr stream, continues draining
  after overflow, and returns inconclusive on overflow. Cargo build artifacts
  are written only under `target/r148-4c9d549-observer/cargo-target/`, owned by Luna
  as a generated scratch output and removed after the bounded logs are copied to
  the observation receipt. The command uses `--locked --offline`, disables
  incremental compilation, and clears compiler wrappers; `CARGO_HOME` is fixed to `/home/momota1029/.cargo` as a read-only cache input;
  the offline, locked invocation must not fetch or update dependencies. It requires Python 3.11 or newer and the exact pinned Rust
  toolchain binaries listed below.
- The supervisor puts Cargo in its own process group. On ordinary completion it
  checks that the group has ceased; if processes remain after Cargo exits, it
  sends TERM then KILL and reports inconclusive. SIGINT, SIGTERM, SIGHUP and
  Python exceptions enter cleanup, terminate the process group, wait/reap Cargo,
  and record whether group cessation was confirmed. If the supervisor is hard
  killed, no cessation receipt exists: Luna records UNKNOWN, quarantines the
  output lease, and does not claim cleanup.
- Luna owns the exact scratch directory `target/r148-4c9d549-observer/`, containing
  two capture files capped at 64 KiB each and a fixed-field metadata file. On a
  completed or conclusively stopped run, Luna copies all retained files and
  their hashes into `notes/progress/2026-10-20-r148-observation.txt`, then
  removes the scratch directory. If cessation is unconfirmed, scratch remains
  quarantined until safe cleanup is established. Luna owns provisional
  instrumentation cleanup: retain the observer/supervisor only if final review
  finds them useful; otherwise remove them in a separately reviewed cleanup
  diff. On obstruction or confirmed STOP, preserve the bounded receipt and
  remove provisional hooks in a separately reviewed cleanup diff.
- Fresh independent final compiler/source and spec/authority reviewers inspect
  the frozen contract, observer, proof, observation and handoffs. A reviewer
  may not have authored either lane. Findings return to Luna; no worker edits a
  frozen review target.

No broader paths, test expectations, fixtures, source meaning or production
code are leased. No new sprint team is started by a child. The implementation
lane is observation tooling only and is separate from R147's unauthorized
braced-if changes.

The sole observer is a `#[cfg(test)]` unit test inside the existing solver
source-test module, reading the pinned playground fixture with `include_str!`.
The authorized command is:

```sh
python3 tools/r148_bounded_observer.py
```

No second command, retry, build-only invocation or alternate fixture is
authorized. A command failure, source mismatch, timeout, incomplete event log
or ambiguous result ends the observation lane without repair. This invocation
is evidence for the one finite observer only, not proof of the parent theorem.

## Required evidence and falsifiers

The event record must distinguish the selected raw `BoundKey` from each
canonical representative, retain every raw preimage relevant to the selected
fiber, preserve ordering across merge/compression/rollback, and identify the
relation-local provider/context/evidence at the actual consumer. The proof must
derive every recorded transition from the pinned source owners and show that
test instrumentation does not change production builds or solver decisions.

Falsifiers include a missing selected `Work::Bound`, wrong extrusion or
restoration arm, unaccounted raw preimage, log incompleteness, mismatch between
event replay and live forest state, dropped/forged relation lineage, or no
actual consumer on the fixed source route. Any falsifier or ambiguity returns
an exact OPEN obstruction; it does not authorize a repair or semantic change.

Do not claim R70/R71 closure, a general source/native correspondence, soundness,
principality, termination, F5 replacement, or production readiness from this
finite result.

## Baseline and direct dependency pins

Before activation, Luna must recheck the baseline tree and every listed hash.
The complete tracked and untracked `crates/` and `tools/inference-playground/`
trees must exactly match baseline at activation;
any required unlisted dependency requires a sequential candidate revision and
fresh prospective review.

The expected baseline tree objects are `73ffdc35651b3ff73303077f74edc0493651311a` for `crates/` and `995f7ce2b066a856f26451b22791cab2cb177b92` for `tools/inference-playground/`. Luna compares the actual working-tree inputs with baseline commit `4c9d549eab9f2ba38a2b319d4329599dd5272430`, including tracked diffs and untracked files under both trees. Any mismatch requires a new contract revision.

```text
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
45465871d4eec1dea86bb7fa652a253b82e293ce91512608df6c06ab248eec95  crates/yu-solver/src/candidate_context_tests.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0  crates/yu-solver/src/candidate_value_graph.rs
620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3  crates/yu-solver/src/candidate_receiver.rs
a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473  tools/inference-playground/src/lib.rs
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100  tools/inference-playground/src/main.rs
51aac3016d9000a1cc0e34e2050ca73f4aa44112f461ec6237195b0d65d89906  tools/inference-playground/examples/nested-recursion.yu
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
bb191d590b47dff547202427de67c771a1c47014abc19b32609d3bca3c860f0c  notes/progress/2026-10-20-r144-closeout.md
f576ad08d386509eebda0eaf65da73ed90a0f2f4a668d1f63391bed16b32feee  notes/progress/2026-10-20-r146-closeout.md
7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c  crates/yu-solver/Cargo.toml
04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1  crates/yu-solver/tests/candidate_intrusion_observation.rs
5970e63ed7eafe720ff0737483d5f22d96b3b3787a465b225c38a757facf199a  tools/r148_bounded_observer.py
18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93  crates/yu-syntax/src/lib.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
1a68331e5d16d46471545e673226541dc848123d1c3e286260359cecf41adcd2  crates/yu-syntax/src/sequence.rs
c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626  crates/yu-syntax/src/root_statement.rs
cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad  crates/yu-syntax/src/header.rs
3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973  crates/yu-syntax/src/syntax_environment.rs
8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8  crates/yu-hir/src/lib.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654  crates/yu-hir/src/shadow.rs
567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3  crates/yu-syntax/Cargo.toml
a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1  crates/yu-hir/Cargo.toml
2be9f92dbb92013436311b696b4020d10bc99a965a82a25181d8957fc5e1b08d  crates/yu-core/Cargo.toml
1fae5cab6325fc575ff586f665460592c3c66d9fb03310d060d5d018cb251a9c  crates/yu-types/Cargo.toml
a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a  Cargo.toml
de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5  Cargo.lock
c185a2b859850d94af015a9672c1568e1ef73b12612d820f596ef967b835f637  .cargo/config.toml
f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142  crates/yu-syntax/src/cursor.rs
81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669  crates/yu-syntax/src/expression/operator_chain.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  crates/yu-hir/src/module.rs
841072d1d92f9e841d9ba5b0814182a0adf064acf4527cd120967b7bc49dcb66  /home/momota1029/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo
bff349e72704ff70bc08a234a3847338e797065bbedde5e556808bc87b7bf7c6  /home/momota1029/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc
```

 The implementation worker may not edit `lib.rs`, source fixtures, package manifests, `Cargo.toml`, `Cargo.lock`, or `.cargo/` under this revision. The test-only context observer hooks are explicitly leased above. If a missing event owner lies outside these paths, stop for a new reviewed revision.

## Resource and stop conditions

Proposed hard cap: **3,120 active seconds, Astra 0, no carryover**: preparation
and pin validation 180; rev1 and rev2 prospective review reservations 360;
rev3 and rev4 prospective review reservations 360; rev5 and rev6 prospective
review reservations 360; implementation/observer 600; proof 600; Luna
observation 120; final reviews 360; closeout 180. Charge each completed prospective review
reservation in full; no prior reservation is refunded. Charge full
reservations when actual runtime is unknown. Keep the existing three legacy
UNKNOWN assignments, board quarantine and R104 HELD lease unchanged.

No worker starts before CLEAN prospective compiler/source and spec/authority
reviews, exact pin validation, Luna's explicit activation and runtime receipts.
Stop on source/dependency drift, unlisted ownership, any production-semantic
change, incomplete/nonreplayable events, unconfirmed process cessation (UNKNOWN/quarantine), a disproving source trace, exhausted
budget, or user STOP. Only Luna may activate, adjudicate, update current state, stage explicit paths, commit and push. Routine commits and pushes are already authorized by the user goal.
