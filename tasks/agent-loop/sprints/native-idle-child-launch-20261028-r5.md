# Sprint NATIVE-IDLE-CHILD-LAUNCH/r5

Status: CANDIDATE until Luna admits this contract and exact leases in
`tasks/agent-loop/current.json`.

## Goal and fixed parent

Construct and source-review one bounded launch bridge for
`ReplayChildWait::Idle` with `Some(item)`: the real successful call to
`start_typed_drain` creates its typed-drain frame, updates the source replay
operation to `Running { ack, drain_index }`, and records the exact replay
destination. In parallel, add a test-only observer reached by the existing
source-driven restoration path and authenticate one FreshUse source-to-
destination relation, its actual emission/readback, and raw transformer
contents under same-ID mutation.

This packet does **not** prove later Transport/Context/Dispatch child
completion, restoration completion, prepared-root preservation, all FreshUse
routes, source/native correspondence for the language, the original
`SourceProblem.InferenceSoundness`, effect hygiene, principality, termination,
or production correctness. Keep every one OPEN. Preserve the parent theorem's
quantifiers, source domain, lawful-history contract, shared witnesses and
effect policy.

## Baseline and pinned inputs

Use clean source baseline commit `418bde889`; the primary's record-only commit
`0abc0569a` does not change these pinned source blobs. Prepare the isolated
workspace from the baseline commit, never from the dirty root working tree or
R4 rejected Rust bytes. Remove the copied R4 isolated Rust artifact subtree
before worker access. R4's Lean candidate is permitted only as an explicitly
unchecked reference.

Pinned source blobs at baseline `418bde889`:

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

Pinned proof/toolchain and governing documents:

```text
notes/theory/lean/lean-toolchain
  ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
notes/theory/lean/lakefile.toml
  212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4
notes/theory/lean/lake-manifest.json
  058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3
notes/theory/lean/YulangClosure.lean
  3c38da4bb2e017249fa973e0ee28f243d44ba6d52b6f173ac617b605f1fce9e8
notes/theory/lean/YulangClosure/NativeDrainOwnership.lean
  d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18
notes/theory/lean/YulangClosure/NativeRestorationFrameR4.lean
  b2c185413cf537b22a91c04c97bdd5c30ce0f44afe83c91cbbc2eff1e32708f0
tasks/agent-loop/history/native-restoration-frame-20261028-r4-outcome.md
  84be4d221ef3277d95cb139cc1ee4ec1f773690a27f462fef8ed87823c9b1206
tasks/agent-loop/inbox/native-restoration-frame-r4-proof.md
  a33d0cccf7bff422e5f8ad050f30e0243f6d86ebf7eeba642e1b2be0bf9b7334
notes/design/2026-10-10-annotation-effect-hygiene-integration.md
  a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
notes/progress/2026-10-26-inference-soundness.md
  fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1
```

The entire bodies of the enumerated Rust source files form the source-read set;
use focused reads. Other source bodies require a Luna-authored amendment before
inspection. R4's unchecked candidate may not be imported as a theorem, assumed
as a transition law, or cited as verified evidence.

## Required source-to-Lean bridge

Audit these pinned owners and represent every successful write on the selected
launch path explicitly:

1. `candidate_context_step_replay_child`, Idle/Some branch: check queue and
   worklist preconditions, prepare replay wait, select the child and create its
   acknowledgement, then call `start_typed_drain`.
2. `start_typed_drain`: append a `TypedDrainFrame` with its actual initial task,
   occurrence, cause, previous processing/relation, empty current, Transport
   stage and zeroed counters; clear processing and diagnostics; seed/choose the
   relation; enqueue the child item; attach passive source-drain attribution
   only after enqueue succeeds.
3. Return to the caller: write `replay_destination = Some(ack)` and change the
   saved replay operation to `Running { ack, drain_index }`; return `More`.

Model success and fallible/error prefixes separately. Do not claim rollback or
later child completion. State exactly which frame fields are preserved and
which are initialized. The launch theorem must derive its post-state from
explicit transitions, not a premise named `StartTypedDrain`, `DriverReturns`,
or an assumed desired lookup. If the authenticated source inventory reveals
another successful write on this path, include it or stop at its first boundary.

## Rust observer and falsifiers

Instrumentation is `cfg(test)` and may change no production/API/semantic or
expected-output behavior. It must be reached by the ordinary source-driven
route through `candidate_begin_bound_restoration` and the actual driver return;
a test-only wrapper that source execution never calls is not evidence. Record
independent invocation identity, source witness, restoration handle and the
exact successful returned emission. After execution, recompute the completed
predicate from current state, including admission, mapped/admitted relation,
flow root, raw transformer contents and physical vector slot.

For FreshUse, distinguish source and destination bounds. Validate the mapped
relation against the destination and authenticate the actual source-to-
destination transport witness. Preserve root zero as logical identity distinct
from physical slot indices. The raw transformer witness must be captured from
the actual row contents, not just an ID; a same-ID content replacement must
make the same complete predicate reject, then restore the original value
before asserting rejection. Include invocation reassociation, duplicate
ownership, relation/flow/slot changes and all existing required field
mutations. Ensure the recorder is nonempty on the actual source fixture.

The `candidate_context.rs` one-element raw-transformer replacement helper is
authorized only as `#[cfg(test)]`, returning the original value. It must not
perform interning, solver continuation, or resource-accounting work. The
sequence and mutation proof remains finite evidence; no whole-language claim.

## Assignments and resources

- Proof, registered `lean_prover` Sol/high: 1,000 seconds.
- Implementation, registered `implementer` Luna/high: 900 seconds.
- Fresh independent `compiler_referee` Sol/medium: 600 seconds.
- Luna primary: 500 seconds. Total 3,000 seconds; Astra 0; no renewal.
- ACK the exact contract SHA, all source hashes and the amendment before body
  reads or writes. Unknown serving model/effort remains `UNKNOWN`.
- Workers do not run Cargo, Lean/Lake, builds, tests, formatters, Git or
  descendants. Freeze each handoff with byte hashes and stopped-writing receipt.
- Reviewer performs source-first Rust and proof comparison, returns
  `ACCEPT_FOR_BOUNDED_CHECKS` or `REJECT`, and runs no checks. A rejection
  closes this sprint incomplete; no revision/check is authorized under this
  packet.
- Only after acceptance, Luna may run at most two focused Cargo attempts
  (aggregate 120 seconds, 2 GiB RSS, 1 CPU) and one Lean 4.35.0 `-j1 -M1024`
  check (aggregate 180 seconds), one heavy process at a time. The same reviewer
  performs a sequential final evidence review. A failed check closes incomplete.

No source/production promotion follows from this packet. At completion record
all exact hashes, checker results, review, runtime/resource receipts and the
first remaining native branch in a unique history outcome. Preserve unknown
workers/quarantines and all R4 rejection history.
