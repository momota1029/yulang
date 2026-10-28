# Rust handoff: EFFECT-PERMISSION-SOURCE-ORIGIN-20261028/r1

Assignment: `EFFECT-PERMISSION-SOURCE-ORIGIN-20261028/r1/rust`
Handoff revision: 2
Prior frozen revision 1 SHA-256:
`277f9dd4469dbd942f2d0713faa315f04702de49048f948d9658f1da75a46ffc`
Contract SHA-256: `4158140fa23108a9be8377527854df831044de1dc4d8a06ed063cfbf44ef7130`
Baseline: `d2814e4d1`

## Parent and claim scope

Parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3,
5, with the original whole-language obligations unchanged and OPEN. This is
provisional source-native evidence for the constructor-to-capture connection;
it is not a theorem, a semantic change, cutover approval, or production closure.

## Prior evidence and amended fixture scope

The previous `formal_live_capture_source_observation_trace` fixture directly
selected an `Action::FormalAnnotation` and called
`candidate_formal_annotation`. It deliberately bypassed source preflight and
passed `parameter as u32` to `capture_candidate_graph`, even though construction
stores the domain at `parameter_live_base + parameter`. Its empty-root result is
withdrawn as evidence of non-arrival. The prior review and outcome remain
immutable historical evidence.

The amended internal fixture computes the checked parameter row with the same
mapping as `candidate_formal_annotation`, then asserts that the graph contains
the exact negative domain term constructed for that parameter. The constructor
trace now records this parameter row alongside the negative term.

A separate observation was added to the existing tuple-formal source fixture.
It starts the recorder before ordinary `CandidateInference::solve`, performs
the actual definition `export`, and calls `formal_effect_permissions`. The test
checks that the constructor's domain term is the same term published as a
captured negative formal root and that capture returned. This route uses the
ordinary source preflight and does not inject an `Action` or bypass a gate. Its
source is the already exercised tuple fixture containing two distinct
permission paths; the captured fixture additionally checks public effect
permission export and the neighboring returned-computation behavior. It passed:
ordinary solve returned without candidate conflicts, and export yielded both
formal permissions.

## Implementation and exact diff

Leased source files:

- `crates/yu-solver/src/candidate_effect.rs` SHA-256
  `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256
  `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`

The `Capture::intern` test recorder no longer eagerly formats the canonical
endpoint. Event text is constructed only if the recorder is enabled. No
solver-choice, recovery, API, source semantics, or runtime behavior was changed.

Dependency pins checked before editing:

- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- `crates/yu-solver/src/shadow_apply.rs`: `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- prior checked live-capture Lean model:
  `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`

## Check plan and resources

`git diff --check -- crates/yu-solver/src/candidate_effect.rs crates/yu-solver/src/candidate_scheme.rs`
passed before execution. Luna released exactly one focused invocation after
checking that the Lean heavy check completed, no competing heavy process was
running, both source hashes still matched, and available memory was
23,873,077,248 bytes (>4 GiB):

```text
timeout 180s taskset -c 0 env CARGO_TARGET_DIR=/tmp/yulang-effect-permission-source-origin-20261028-r1/rust-target CARGO_BUILD_JOBS=1 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_permission -- --nocapture
```

The command exited **0**. `/usr/bin/time -v` reported 62.17 seconds elapsed,
55.63 seconds user time, 4.27 seconds system time, 96% CPU and maximum RSS
1,652,924 KiB (under the 2 GiB cap); 0 swaps. Three tests passed and 814 were
filtered out:

- `candidate_effect::tests::formal_permission_live_capture_source_observation_trace`
- `candidate_effect::tests::negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back`
- `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership`

The corrected trace constructed domain term
`Term { brand: TermArenaBrand(1), index: 286 }` at parameter row 3, then
published that exact term at capture node 3. Capture returned graph root 0,
live root 3, 36 nodes, 11 rows and one negative formal root. The ordinary source
test's assertions also confirmed the same-term root publication and public
permission export. Test output contained existing compiler warnings but no
errors. No retry was made.

The single runtime transcript is frozen here; no separate raw output log was
created. `CARGO_TARGET_DIR` is the leased scratch locator. The exact argv,
individual test names, exit status and measured resources are recorded above.

## Remaining evidence and TODOs

- `lean_prover`: derive the permission origin and allocated-row witness from
  the successful recursive constructor, then connect the exact parameter
  domain/root identity to capture under the live LIFO and canonical endpoint
  transport. Preserve endpoint-arrival and export-membership premises explicitly.
- Independent reviewer: verify the corrected offset, exact-domain identity,
  ordinary preflight route, event allocation boundary, actual capture/export
  correspondence, and the frozen Lean theorem/axiom evidence.

No source-preflight refusal was observed: the ordinary source tuple fixture
completed solve, capture and export through the public path. This is finite
source evidence, not a universal theorem or production approval.

## Worker and hygiene receipt

Requested role/model/effort: `implementer`, Luna/high. Actual runtime metadata:
UNKNOWN in this handoff. No model change is claimed. No Git operation was run.
Writes are frozen in the two leased source paths and this handoff only. The
leased scratch target
`/tmp/yulang-effect-permission-source-origin-20261028-r1/rust-target/` was
created by the sole Cargo invocation and remains disposable for primary-only
hygiene. No other new or disposable path was created. Worker state: STOPPED;
the Cargo process exited and all writes have stopped.
