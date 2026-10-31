# NATIVE-READBACK-AND-CALLBACK/r7 Rust handoff

Sprint-ID / contract revision and SHA-256:
`native-readback-and-callback-20261028-r7`, revision 1;
`35b3b0b23eeeb842acddc47ce4685bb8bd1ad6152825c9d1cbba4ba6bce0840a`.

Assignment-ID / handoff revision:
`native-readback-and-callback-r7-rust`, revision 1.

Parent gate / original theorem and scope locator:
`YulangClosure.SourceProblem.InferenceSoundness` at
`notes/theory/lean/YulangClosure/Contracts.lean`, with the separate
`SourceProblem.NativeCorrespondence` obligation. The unchanged full source
domain, original quantifiers, shared source witness, immutable-birth Value
qualification, and annotation-effect hygiene policy remain open and unpromoted.

Baseline / direct dependency hashes:
All 12 Rust pins in the sprint contract were independently hashed before any
Rust source body read and matched exactly. The exact ACK, including a corrected
transcription typo for `candidate_source.rs`, was sent to Luna. Pins:

```text
candidate_scheme.rs     c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context.rs    19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion.rs  e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af
candidate_scope.rs      9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a
candidate_intrusion.rs  475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
candidate_effect.rs     7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b
candidate_source.rs     96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
lib.rs                  ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
yu-solver/Cargo.toml    aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed
Cargo.toml              a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a
Cargo.lock              de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5
.cargo/config.toml      c185a2b859850d94af015a9672c1568e1ef73b12612d820f596ef967b835f637
```

Role / actual worker ID / current session / launch or resume receipt:
Registered `implementer`; actual worker ID is this task path,
`/root/native_readback_callback_r7_rust`. Current-session active-work ACK:
2026-10-28 09:52:52 UTC. Runtime launch/spawn time was not exposed (UNKNOWN).

Requested model and effort / observed model and effort:
Luna/high / UNKNOWN (runtime model metadata unavailable to this worker).

Exact leased paths / all authors and contributing descendants:
Only these four exact paths were written; no descendants:

```text
isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_scheme.rs
isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_context.rs
isolated/native-readback-and-callback-r7/crates/yu-solver/src/candidate_extrusion.rs
tasks/agent-loop/inbox/native-readback-and-callback-r7-rust.md
```

This worker authored the changes. `candidate_scheme.rs` and
`candidate_context.rs` remain byte-identical to their pins. No mutable root
Rust source was read. One read-only `git diff` command was run while inspecting
the leased extrusion file; no Git write or other Git operation was performed.

Outcome class:
`provisional` / test-only implementation repair. Not production behavior,
source/native theorem evidence, or parent closure.

Parent application:
The test-gated physical-bound replace helper now removes the endpoint wrapper
per lane before writing the concrete vector element, then reconstructs the
complete `ExtrusionEndpoint` around the displaced element. The remove helper
likewise wraps each actual removed `u32`, `ValueEndpointKey`, or
`EffectEndpointKey` as the proper Value/Effect endpoint. The eight lanes are
covered: value/effect lower/upper rows and value/effect lower/upper atoms.
Row-vs-atom guards and polarity checks remain. This repairs the two R6 static
type errors in the leased test helpers.

The R6 observer path was preserved: the completion projection still rereads
the currently addressed physical row/lane and compares it with the retained
readback. Invocation/handle linkage, the FreshUse source-to-destination
relation, raw transformer content authentication, ordinary fixture text, and
existing falsifiers were not edited. In the fixture, the removed item is
reinserted before asserting rejection; the replaced item is restored before
asserting rejection. This is source inspection only; the fixture was not run.

Source constructors -> generated constraints -> propagation -> consumer/native path:
This Rust packet changes only test-gated instrumentation used to mutate and
restore a physically addressed bound vector element. It does not alter
constraint construction, propagation, source execution, or native behavior.
The ordinary fixture is the intended consumer path, pending the conditional
focused Cargo attempt by Luna after independent review acceptance.

Prior evidence reused / rejected:
Reused the R6 rejected review's precise source observations that the physical
slot reread, invocation/handle association, FreshUse relation, raw transformer
content comparison, and restore-before-assert behavior address earlier
observer gaps. Rejected R6's replace/remove helpers as ill-typed, and retained
the R6 package as provisional failure reference only. R6 review receipt SHA-256:
`4323f806ad9767f9da111dfca187b3866bb9bc54a203d6825ad85ea96007ebe3`.
No R6 unchecked source or proof claim is promoted.

Artifact locators and byte hashes / frozen review snapshot:

```text
candidate_scheme.rs     c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context.rs    19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion.rs  2fa4cdf965785fc43ff9792af36c1dd86a01d50cf863229de2ddb721878d2477
```

The Rust artifact is frozen at these hashes for independent review. The
handoff content hash is recorded by the sender after this file is written.

Checks, coverage, omitted cases and resource budget spent/remaining:
No compiler, Cargo, test, Lean/Lake, build, formatter, or executable check ran,
as required for this worker. No test lane was newly added. Static source edits
cover all eight helper arms by inspection but are not independently verified.
Active elapsed time, CPU, and RSS are UNKNOWN. The assignment grant is 900 s;
actual remaining runtime is UNKNOWN. No scratch or generated outputs exist.

Provisional boundary, falsifier, cleanup owner:
This is reversible `#[cfg(test)]` observer instrumentation only. It is
falsified if fresh review or the authorized focused check finds an ill-typed
lane, a non-exact restore round trip, changed observer reachability or
authentication, a missing mutation/restoration, or an assertion preceding
restoration. Luna owns any cleanup or new authority decision after adjudication;
this worker's lease does not authorize production cutover.

Next related step inside the existing envelope, or exact boundary needing Luna:
Worker work is complete and stopped. Fresh independent review decides whether
the exact frozen artifact qualifies for the one contract-authorized focused
Cargo attempt. Luna owns that check and the source/native adjudication. This
artifact does not close the R6/R7 proof gap: the callback/resource correspondence
lane and full original parent remain open. The R6 proof's first unmodeled launch
owner remains `clear_diagnostic_scratch` (`lib.rs:15934`, called from `14196`),
with exact resource realization open earlier.

Mutual TODOs:
No Rust-to-proof file handoff is needed or authorized. Request independent
source-first review of the frozen four-lane conversion behavior and its
preserved observer/falsifier path. Original parent remains
`YulangClosure.SourceProblem.InferenceSoundness`; no semantic change requested.

Worker state / writes stopped receipt / unresolved descendant leases:
STOPPED after freezing this handoff; no descendants or unresolved descendant
leases. No parent/source/native correspondence claim is certified by this
worker.

Commit-ready milestone or explicit pending review/integration:
Pending fresh independent review. Luna owns integration and Git.
