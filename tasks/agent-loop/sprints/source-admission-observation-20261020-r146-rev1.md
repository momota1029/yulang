# Sprint R146 candidate — bounded admission observation for the fixed source

Status: **CANDIDATE; no process, worker, lease, or resource is authorized yet.**
Revision 1. Branch `research/simple-sub-intrusion`; baseline
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
existing documented command, using the exact unchanged input:

```sh
cargo run -q -p yu-playground -- --intrusion tools/inference-playground/examples/nested-recursion.yu
```

Record the exact command, baseline/tree and live commit, `cargo --version`,
`rustc --version`, start/stop timestamps, exit code, timeout/resource status,
stdout/stderr byte counts and SHA-256, and a bounded redacted-free excerpt or
classification. No input rewrite, stdin substitution, retry, environment
mutation, feature flag, manual graph, or alternative fixture. The CLI already
caps input/output; run under a hard 120-second wall/CPU envelope and a 4-GiB
process memory limit. Terminate the entire process group on the first limit.
Build failure, unavailable toolchain/dependency, timeout or resource exhaustion
is **inconclusive infrastructure evidence**, not a source admission result.

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

- Contract: `tasks/agent-loop/sprints/source-admission-observation-20261020-r146-rev1.md`.
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
preparation/pin validation 180; prospective reviews 120; proof/static audit
840; Luna's single observation 120; final review 240; closeout 180; remaining
120 is unallocated headroom and may not be reallocated to another process.
Unknown elapsed worker time is charged at its full lane reservation. The CLI
process itself has a strict 120-second cap. Preserve three UNKNOWN historical
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

No activation, lease, build or CLI execution follows from this candidate.
