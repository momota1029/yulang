# Sprint R146 candidate — bounded admission observation for the fixed source

Status: **CANDIDATE; no process, worker, lease, or resource is authorized yet.**
Revision 3. Sequentially revises rev2 after one major spec finding. Rev1 and rev2 remain frozen. This revision pins its predecessor and places graceful termination wholly inside the strict 120-second process-group deadline without changing the source or parent claim. Branch `research/simple-sub-intrusion`; baseline
`f6e59e42bcfcfb3c13a0c511c63bcf9d0390005d`, repository tree
`38f79bf7203e9766ac26b5876d7569fc84dbc842`. Luna is primary, authority owner
and sole Git integrator.

## Parent and fixed outcome

Preserve the original inference/evaluator and unchanged Yulang2 sample
execution objective. `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, R71, Simple-sub
A/B, source/native correspondence and production remain OPEN with their
original domains and quantifiers. R146 is a finite admission/entrance probe for
the exact tracked input `tools/inference-playground/examples/nested-recursion.yu`.
It does not prove a theorem, source/native correspondence, Yulang2 compatibility
or a compiler defect.

The fixed question is whether the existing documented `yu-playground` inference
path observes this exact input as syntax-admitted and candidate-prepared, or
which exact caller stage reports a failure. If preparation succeeds, use its
bounded `--intrusion` output only to identify the next statically reviewable
source entrance. No claim about a production raw slot or consumer follows from
CLI output. The prior R145 result remains accurate: before observation, the
source derivation was stopped at the unpinned syntax-admission owners.

## One allowed observation and outcome classes

After activation and a fresh pin check, Luna may make **one** invocation of the
existing documented Cargo command, using the exact unchanged input. Preserve
this exact Cargo argv:

```text
cargo run -q -p yu-playground -- --intrusion tools/inference-playground/examples/nested-recursion.yu
```

Use one inline Python supervisor (no file or scratch artifact) with this fixed
procedure. Before starting Cargo, record `cargo --version`, `rustc --version`,
UTC start time, baseline/tree and live commit. Spawn the argv above via
`subprocess.Popen` with `start_new_session=True`, `stdout=PIPE`, `stderr=PIPE`,
`bufsize=0`. Prefix the Cargo argv with `taskset -c 0 prlimit --cpu=125:125
--as=4294967296:4294967296 --`; CPU 0 is in this environment's allowed affinity
set. The one-CPU affinity is inherited by Cargo and every child, so their
aggregate CPU cannot exceed the 120-second monotonic wall interval. `RLIMIT_CPU`
is a per-process 125-second backstop, not the aggregate cap. `RLIMIT_AS` is a
per-process 4-GiB virtual-address-space limit, not an RSS limit.

Set only `CARGO_BUILD_JOBS=1` in the child environment to avoid simultaneous
Cargo compiler jobs; inherit every other environment value without
modification. Failure to set the single build job is inconclusive.

Use `selectors` to drain both pipes concurrently and retain no more than
1,048,576 combined bytes. Hash/count bytes as read. At the first byte beyond the capture cap, send SIGTERM to
`os.killpg(proc.pid, ...)` and allow at most five seconds for shutdown while
continuing to drain, but never past the fixed deadline `start + 120s`. At 115s,
send SIGTERM if the group is still running; at exactly 120s send SIGKILL to the
same process group if any member remains. If capture overflow starts after
115s, the remaining grace is only the time until the 120s deadline; if the
wall deadline itself triggers first, send SIGKILL immediately. Reap the Cargo supervisor with `wait`; reaping time is outside the child
process CPU/wall allowance. Record the initiating limit. An exception or
failure to establish affinity, limits, capture, group termination or reaping is
**inconclusive** and must stop the packet. The process group owns only this
invocation; do not launch another process. Store only a bounded excerpt and
per-stream byte counts/hashes in the authorized observation record.

Record the exact Cargo argv, baseline/tree and live commit, tool versions,
start/stop timestamps, exit code, signal/timeout/resource status, and
stdout/stderr counts and SHA-256. No input rewrite, stdin substitution, retry,
other environment mutation beyond the one fixed `CARGO_BUILD_JOBS=1` setting,
feature flag, manual graph, or alternative fixture. Build failure, unavailable
toolchain/dependency, timeout or resource
exhaustion is **inconclusive infrastructure evidence**, not a source admission
result.

Only these outcomes are allowed:

1. **Observed prepared:** exit success and output reaches the existing finite
   intrusion report. This establishes that this invocation passed its current
   syntax, HIR and candidate preparation path; it does not prove the internal
   constructors or any universal invariant.
2. **Observed source failure:** successful tool build, then the CLI reports a
   syntax diagnostic, HIR/candidate lowering error, or candidate conflict.
   Preserve exact category and bounded diagnostic evidence; do not label it a
   defect or refutation of R70/R71.
3. **Inconclusive:** all build/process/toolchain/resource failures or output
   classification ambiguity. Stop with no retry.

The exact input bytes, existing caller and actual syntax/HIR constructors must
be statically audited under the manifest. The observation and source audit are
separate evidence: CLI success cannot replace constructor reasoning. If
candidate preparation succeeds, the proof lane may continue only through
manifested owners toward a later source/merge/raw-slot locator, and must stop at
the first missing owner or unmet consumer premise. Do not reuse the R145
unfinished path as a theorem or claim a selected `Work::Bound` slot without
source evidence.

## Source scope and stop conditions

This is read-only source research plus the one existing-tool CLI invocation.
No source edits, tests, runtime evaluation (`--run`), instrumentation, observer
implementation, fixture changes, expected-output edits, semantic decision or
production promotion. Stop on pin drift, unmanifested constructor/dependency,
resource exhaustion, ambiguous output, need for additional execution, or user
STOP. Any second observation or broader sample needs a new reviewed contract.

The implementation result is **NO_SAFE_CODE_SLICE**. The proposed activity
uses the existing tool and has no authorized code repair.

## Exact outputs, lanes, reviews and resources (not granted)

- Contract: `tasks/agent-loop/sprints/source-admission-observation-20261020-r146-rev3.md`.
- Proof: `notes/theory/2026-10-20-r146-source-admission.md`.
- Frozen handoff: `tasks/agent-loop/inbox/20261020-r146-proof.md`.
- Luna observation record: `notes/progress/2026-10-20-r146-admission-observation.txt`.
- Luna closeout: `notes/progress/2026-10-20-r146-closeout.md`.

Proof owner: one registered `prover` owns only theory and handoff. Luna alone
owns the one CLI observation record, contract, current state and closeout. No
overlapping writers. Get prospective spec/authority and compiler/source CLEAN
reviews for this exact contract and every pin before activation. After freeze,
a fresh compiler/source reviewer independently checks the outcome and source
classification. Reviewers do no execution, write or Git.

Proposed cap: **1,800 active seconds; Astra 0; no carryover or renewal**:
preparation/pin validation 180; prospective reviews 360 (including the sequential rev2 and rev3 review rounds
after findings); proof/static audit 600; Luna's single observation 120; final review 240; closeout 180; remaining
120 is unallocated headroom and may not be reallocated to another process.
Unknown elapsed worker time is charged at its full lane reservation. The
supervised process group has a strict 120-second aggregate CPU and wall cap.
Preserve three UNKNOWN historical
assignments, board quarantine and R104 HELD; do not reclaim unknown capacity or
overlap any frozen R145 path.

## Frozen baseline pins (baseline/live SHA-256 required before activation)

The baseline commit and complete Git tree ID above pin the tracked code
snapshot. At activation, `Cargo.toml`, `Cargo.lock`, `crates/`, and
`tools/inference-playground/` must be byte-identical to that baseline
(`git diff --exit-code <baseline> -- Cargo.toml Cargo.lock crates
tools/inference-playground`), the direct pins below must match baseline/live,
and the worktree must be clean apart from this packet's own recorded artifacts.
The following direct reasoning and process-control sources make the critical
owners explicit. Any source or command change requires sequential revision and
fresh prospective review.

```text
a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a  Cargo.toml
de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5  Cargo.lock
87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56  tools/inference-playground/Cargo.toml
681af715b51d236cabd2aaf481eea43abd36f114a841d49d3bcd520ef2c85f8c  tools/inference-playground/README.md
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100  tools/inference-playground/src/main.rs
a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473  tools/inference-playground/src/lib.rs
51aac3016d9000a1cc0e34e2050ca73f4aa44112f461ec6237195b0d65d89906  tools/inference-playground/examples/nested-recursion.yu
567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3  crates/yu-syntax/Cargo.toml
18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93  crates/yu-syntax/src/lib.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1  crates/yu-hir/Cargo.toml
ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654  crates/yu-hir/src/shadow.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  crates/yu-hir/src/module.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c  crates/yu-solver/Cargo.toml
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
```

Frozen predecessors: rev1 `tasks/agent-loop/sprints/source-admission-observation-20261020-r146-rev1.md`, SHA-256 `a7848b9138898a04213a071172f41d4b351233a1ae82e713232a1dbd320273da`; rev2 `tasks/agent-loop/sprints/source-admission-observation-20261020-r146-rev2.md`, SHA-256 `5a59eb8a01b6c8c9e09acf78f10142e45c900d3ae0ec2105b46ab55a7d6d7cca`. Rev2 closed rev1's supervision gap, but its five-second SIGTERM grace could extend the strict 120-second budget. Rev3 fixes the grace schedule: graceful termination begins no later than 115s and SIGKILL occurs at 120s. No activation, lease, build or CLI execution follows from this candidate.
