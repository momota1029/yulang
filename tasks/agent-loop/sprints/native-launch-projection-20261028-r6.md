# NATIVE-LAUNCH-PROJECTION/r6

Status: ADMITTED by Luna after R5 closeout and fresh live-roster synchronization.
This is a new packet after R5 rejection; R5 is not reopened, revised, waived or
treated as accepted evidence.

## Fixed outcome and original parent

The user's continuing goal remains a sound Rust/Lean account of Yulang
inference, with annotation-effect hygiene and native correspondence as open
obligations. The unchanged original parent is `SourceProblem.InferenceSoundness`
in `notes/theory/lean/YulangClosure/Contracts.lean`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.NativeCorrespondence` remains a separate obligation. This
packet does not instantiate either definition, narrow accepted source forms,
change the shared witness, or promote a theorem or production behavior.

Within that fixed parent, the bounded outcome is a source-grounded projection
bridge for the successful `ReplayChildWait::Idle` + `Some(item)` path, from
`candidate_context_step_replay_child` through `candidate_prepare_replay_wait`
and `start_typed_drain` to the final `replay_destination` and `Running` writes.
The Lean lane must account for every write in that path to the chosen evidence
projection: prove a write preserves the projection, changes it as specified,
or is an exact error prefix. It must not assume resource callbacks are pure.
The successful branch must compose through seeding, enqueue and passive receipt
attribution, or identify the exact first remaining owner without claiming
launch closure.

In parallel, the Rust lane builds a bounded test-only completed-restoration
observer on the ordinary source-driven fixture. It must bind the restoration
begin/return to one invocation, authenticate the actual current physical bound
vector slot on completion, and retain the FreshUse source-to-destination
relation and actual emission readback. Same-ID raw transformer mutation stays a
separate falsifier. Restore the exact raw row before asserting rejection.

## Baseline and immutable inputs

Use clean source baseline commit `7b3ad7074`. The primary created
`isolated/native-launch-projection-r6` from that commit with `git archive`; it is
a complete pinned source snapshot. Mutate only the exact R6 output files below.
Do not read mutable root working-tree Rust paths for assigned source bodies:
other unrelated edits and quarantined work exist there. The source snapshot is
not a Git repository and must not receive Git metadata or refs.

### Rust source read set and initial hashes

All paths below are relative to
`isolated/native-launch-projection-r6/`.

```text
crates/yu-solver/src/candidate_scheme.rs
  35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1
crates/yu-solver/src/candidate_extrusion.rs
  80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61
crates/yu-solver/src/candidate_context.rs
  57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e
crates/yu-solver/src/candidate_scope.rs
  9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a
crates/yu-solver/src/candidate_intrusion.rs
  475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
crates/yu-solver/src/candidate_effect.rs
  7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b
crates/yu-solver/src/candidate_source.rs
  96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
crates/yu-solver/src/lib.rs
  ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
crates/yu-solver/Cargo.toml
  aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed
Cargo.toml
  a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a
Cargo.lock
  de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5
.cargo/config.toml
  c185a2b859850d94af015a9672c1568e1ef73b12612d820f596ef967b835f637
```

### Lean/proof read set and initial hashes

Paths are relative to the main repository unless the snapshot prefix is shown.
The Lean lane may inspect exact source bodies only in this list and the Rust
read set above.

```text
isolated/native-launch-projection-r6/notes/theory/lean/lean-toolchain
  ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
isolated/native-launch-projection-r6/notes/theory/lean/lakefile.toml
  212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4
isolated/native-launch-projection-r6/notes/theory/lean/lake-manifest.json
  058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3
isolated/native-launch-projection-r6/notes/theory/lean/YulangClosure/NativeDrainOwnership.lean
  d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18
notes/theory/lean/YulangClosure/Contracts.lean
  2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
docs/yulang-whole-proof-closure-ja.md
  17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5
notes/theory/lean/README.md
  8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3
notes/design/2026-10-24-birth-level-scc-intrusion.md
  ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae
notes/design/2026-10-10-annotation-effect-hygiene-integration.md
  a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
notes/progress/2026-10-26-inference-soundness.md
  fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1
notes/theory/lean/YulangClosure/NativeIdleChildLaunchR5.lean
  282e0f68922d3176e0d98aab04e535426cf2558403f2648ee4916ec5bb1644f4
tasks/agent-loop/inbox/native-idle-child-launch-r5-proof.md
  1757aed4b4a6bf0657596f3a826845a0fd550078573073ed128c670d3b8620a8
tasks/agent-loop/inbox/native-idle-child-launch-r5-review.md
  9d4e79216181a452c026c89523ca2ad0d37803c318671c3e315f32a9c4adc5c1
tasks/agent-loop/history/native-idle-child-launch-20261028-r5-outcome.md
  7bdd262d603569d5e3e1552c83322db94caefeedf483d3b05df35f1d7460d2fb
```

R5 artifacts are failure/falsifier references only. Do not import the R5 Lean
candidate, use any R5 unchecked declaration as an assumption, or silently reuse
its rejected Rust output.

## Exact assignments, outputs and resources

- Constructive proof lane: registered `lean_prover`, Sol/high, 1,000 seconds.
- Rust implementation lane: registered `implementer`, Luna/high, 1,100 seconds.
- Bounded core lane: registered `astra_prover`, Astra/medium, 300 seconds total,
  at most three substantive stages. Named risk: whether resource/capacity
  observers can be erased as projection-preserving stutters while preserving
  error prefixes. The deliverable is an independently checkable argument or a
  concrete counterexample, not approval of Rust or self-review.
- Fresh independent reviewer: `compiler_referee`, Sol/medium, 600 seconds.
- Luna primary: 600 seconds for admission, integration, allowed checks,
  adjudication, record synchronization and checkpointing.
- Total grant: 3,600 seconds; Astra total 300 seconds. No renewal, no carryover.
  Count the full grant when issued. All workers report observed model/effort
  independently; UNKNOWN remains UNKNOWN.

Exact writes:

```text
Rust lane:
  isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_scheme.rs
  isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_context.rs
  isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_extrusion.rs
  tasks/agent-loop/inbox/native-launch-projection-r6-rust.md
Proof lane:
  isolated/native-launch-projection-r6/notes/theory/lean/YulangClosure/NativeLaunchProjectionR6.lean
  tasks/agent-loop/inbox/native-launch-projection-r6-proof.md
Astra lane:
  tasks/agent-loop/inbox/native-launch-projection-r6-core.md
Reviewer:
  tasks/agent-loop/inbox/native-launch-projection-r6-review.md
Primary:
  tasks/agent-loop/current.json
  tasks/agent-loop/history/native-launch-projection-20261028-r6-outcome.md
```

Leases do not overlap. Workers do not edit contracts, current state, other
outputs, baseline inputs, repository sources outside the isolated snapshot, or
expected output. Workers do not run Git, tests, Cargo, Lean/Lake, build,
formatter, or descendants. They freeze output hashes, state first remaining
owner and stop writing.

## Required implementation and proof evidence

Rust source output remains `#[cfg(test)]` and provisional. Instrument the actual
restoration begin and successful return on the ordinary source-driven fixture;
tie one invocation identity and handle through its exact source admission,
emission, mapped destination relation and successful readback. The completed
predicate must independently reread the current physical bound vector slot
(including the applicable row and atom/effect lane), not only stored readbacks.
Resolve raw transformer contents by ID. Make falsifiers for sibling invocation
reassociation, wrong source/destination relation, physical vector replacement
and removal, and same-ID transformer mutation. Capture mutation result, restore
the exact prior value, then assert rejection and restored acceptance. Avoid
ownership moves of non-Clone values. The ordinary fixture must reach the actual
recorder; a disconnected test wrapper is insufficient. No production behavior,
public API, diagnostics, fixtures, expected output or language domain changes.

Lean source must model the actual bounded branch writes with explicit concrete
constructors. Define a projection containing exactly the launch evidence used
by the bounded conclusion. Audit `candidate_prepare_replay_wait` and its helper
including undo append, resource observation and error prefixes; then account
for `begin_typed_drain`, processing-state save/clear, diagnostic clear, seed,
enqueue, passive receipt attachment, final destination and `Running`. Prove
each relevant write preserves or updates the projection as source dictates.
Separate failed prefixes from the successful path. The final theorem must
compose the source-local steps into the bounded Idle/Some-to-Running fact or
name the exact first unmodeled owner; it may not assume a desired lookup,
successful call, pure callback, seed preservation, enqueue, or driver outcome.
Print every theorem type and perform complete transitive axiom audits if Lean
execution is authorized after review. Reconcile all useful calculations with
the unchanged original parent; local calculations alone do not close it.

The core lane probes the named projection risk independently, checks
capacity/resource writes and failure prefixes against the exact source, and
returns a counterexample or a bounded sufficient invariant with its proof
obligations. It does not certify either producer.

## Success predicate, review and checks

Fresh source-first review compares the frozen Rust output and proof module to
the exact baseline source bodies, original parent, accepted birth-level
correction, effect-hygiene policy, R5 outcome, exact leases and this contract.
The reviewer returns `ACCEPT_FOR_BOUNDED_CHECKS` or `REJECT` and runs no checks.
Reject if the observer is unreachable or stale, invocation handle is unused,
current physical vector is not reread, mutation restoration ordering is wrong,
non-Clone ownership fails statically, projection assumes a source write away,
error prefixes are omitted, theorem is only a proposition definition, or an
R5 declaration/result is treated as accepted evidence.

Only after acceptance, Luna may run at most two focused Cargo attempts in the
isolated snapshot (aggregate 120 seconds, 2 GiB RSS, 1 CPU) and one Lean 4.35.0
check (`-j1 -M1024`, aggregate 180 seconds), one heavy process at a time. These
are included in Luna's 600-second grant. The same reviewer performs sequential
final evidence review. A failed invocation or incomplete audits closes the
packet incomplete. If review rejects, no source/Lean checks or revisions run
under this contract. Any worker deviation is recorded without retrospective
waiver.

## Non-goals and stop conditions

This packet does not prove whole-language source/native correspondence,
inference soundness, effect hygiene, principality, termination, later
Transport/Context/Dispatch completion, every FreshUse route, prepared-root
preservation, or production correctness. It does not alter original A/B claims,
quantifiers, source domain or immutable-birth qualification. No production
promotion follows from bounded source tests or a local Lean lemma.

Stop on missing authority/hash, source snapshot mismatch, overlapping writer,
unavailable live resource, expiry, source path outside the pin set, omitted
first writer, counterexample, or the grant boundary. Preserve all unknown
workers and quarantined paths. At close, record exact hashes, runtime receipts,
deviations, first remaining native owner, review/check outcome and parent gates
in a unique history outcome. Run only `python3 tools/agent_sprint.py check` for
static record validation at admission/close; no unit test of the sprint tool is
authorized here.
