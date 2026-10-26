# Direct-return recursive source: native rejection and its proof boundary

Date: 2026-10-26. Branch: `yulang3`. Native build base:
`99f18bdc54df8057f5a6d5d4bec5dc449336c234`; verified source-identical at
`11b0bf084a66119b83c75f26a75badfa5ff5316b`. The later observation-only
reproduction below uses the same native inputs at `e593657727fc019ee540cca3a098f7989bc919f0`.

**Status: reproduced native type rejection; original source-qualified
counterexample NOT yet established.** This is a reproducible observation of
the current private candidate route, not a proof of the approved abstract
intrusion rule's failure, whole-language unsoundness, or nontermination.

## Exact source and results

The [rejection fixture](fixtures/2026-10-26-direct-return-rejection.yu) is:

```yu
my top h = {
    my f x y = { h x; f {a: y}; y }
    my i: int = f {a: 0} 0
    my b: bool = f {a: true} true
    (i, b)
}
my ignore x = 0
my main = top ignore
```

The two intermediate expressions are expression statements. They are not
new `my ignored` declarations, which would change the source-origin ownership.
The recursive reference is to the one local `f` in its own initializer;
no forward local mutual-recursion or polymorphic-recursion assumption is used.
The native lowering accepts this source and inference produces one
`IncompatibleValue { lower: Int, upper: Bool }` conflict at the final `true`
on line 4 (bytes 105 through 109). `--run main` exits 1 before evaluation.
This is not an unsupported-source diagnostic, renderer failure or timeout.

| Fixture | Unchanged CLI outcome | Time in this run |
| --- | --- | --- |
| `2026-10-26-direct-return-rejection.yu` | exit 1; Int/Bool inference conflict | 1.329 s |
| [scalar control](fixtures/2026-10-26-scalar-return-control.yu) | exit 0; `(0, true)` | 1.323 s |
| [same body without result annotations](fixtures/2026-10-26-direct-return-unannotated.yu) | exit 0; `(0, true)` | 1.326 s |

The scalar control replaces `{a:y}`, `{a:0}`, `{a:true}` by `y`, `0`, `true`
respectively. The unannotated source removes only `: int` and `: bool` from
the local result bindings. These are separate programs and are not silently
identified with the rejection fixture. In particular, a terminating execution
of the unannotated program does not supply an original typing derivation for
the annotated one.

## Reproduction

From the repository root, using the checked-in `Cargo.lock`:

```sh
cargo build --locked -p yu-playground --bin yu-playground -j1
target/debug/yu-playground --run main --steps 5000 notes/theory/fixtures/2026-10-26-direct-return-rejection.yu
target/debug/yu-playground --run main --steps 5000 notes/theory/fixtures/2026-10-26-scalar-return-control.yu
target/debug/yu-playground --run main --steps 5000 notes/theory/fixtures/2026-10-26-direct-return-unannotated.yu
```

The actual run used task-local `CARGO_HOME`/`CARGO_TARGET_DIR` and the matching
absolute executable. Cargo 1.99.1 (`5f94df478`, 2026-08-27) and rustc 1.99.1
(`58cf8f9c3`, 2026-10-13) built the unmodified CLI with `--locked`, one build
job and no development debug info. Each source process had a 20-second wall
limit. `--steps 5000` bounds provisional source-machine evaluation only; it
is not a proof or bound for type inference. The original build exited 0 in
58.955 seconds. All 409 snapshotted native source/configuration inputs still
matched before this rerun. No compiler source, expected output, algorithm,
Cargo manifest, dependency lock or source semantic rule was changed.

`--intrusion` adds an observation to this same algorithm; it is not a switch
between two inference algorithms. After a conflict, the public
`CandidateInference::intrusion_observation` intentionally returns
`ArtifactMismatch` (`crates/yu-solver/src/shadow_apply.rs`). That guard remains
unchanged. The public API supplies no rejecting intrusion export; the later
isolated streaming observer below is a different, explicitly identified
instrument and does not weaken that guard.

## What the public observations do establish

A separate task-local client used the existing public APIs, the same pinned
stdlib syntax environment and the unchanged source lowering/solver. On the
rejection fixture it observed the same HIR, one conflict and seven authentic
source Calls. Their ordinal pairs are: `h x` at 6, `f {a:y}` at 9, the first
partial/full use at 15/14, the second at 21/20, and `top ignore` at 35.
The conflict is at ordinal 20, local constraint slot 40. Both inner calls
retain source level 2. Public Call observations remain available after this
conflict; successful graph and intrusion exports do not.

For the **unannotated** variant, the public retained-state observation shows
one consumed pending intrusion. Its activated group 1 contains the positive
Value pair parent raw 38 / copy raw 42, canonical representative raw 38,
target level 1, occurrence 9. The source support contains event 2 (local
`f` to parameter `h`, different SCCs) and event 3 (local `f` to itself, the
same SCC). Reuse records later attach each support separately. These are
retained associations, not a chronological trace or a proof that the
occurrence's original signed receiving Value is whichever support qualifies.
They cannot be substituted for the rejecting source's native history merely
because the function bodies are equal. The following separate observation
uses the exact rejecting input itself.

## Exact rejecting-input observation

The checked-in [observer patch](fixtures/2026-10-26-native-observer.patch)
changes only a private copy of four solver source files. It enables the
existing test-only streaming events, adds read-only dispatch snapshots and
an explicit observation limit. It changes no solver field, decision,
constraint, expected output or error-export guard. Formatting allocates and
adds execution cost; this is observation evidence, not a formal
instrumentation-equivalence theorem or a timing measurement of the CLI.

The [client](fixtures/2026-10-26-native-observer.rs) uses the same pinned
stdlib syntax bytes, resolved local-source HIR and CandidateInference route.
It reads the existing public conflicts after inference, without requesting
the prohibited successful intrusion/graph export. Its exit 0 means the
observer finished; the observed candidate still has one type conflict.
The unchanged CLI's outcome remains exit 1.

On the exact rejection fixture, the observer completed 1,404 events, with
one conflict at ordinal 20 / local slot 40 and all seven source Calls. It
did not reach its 12,000-event cutoff or its 20-second wall limit. The first
run took 0.837 s. The repository-relative client reproduced the identical
trace, and a newly prepared isolated solver copy reproduced it again in
0.439 s. The SHA-256 of all three traces is
`3d8e9aab2c3339efd6ab22059284919e6863bfc057a0201fa0a9e44175df744d`.

The retained finite chain is:

| Event | Observed native fact |
| ---: | --- |
| 48 | Value row 38 is at current level 2; the comparison is row38 ≤ row8. |
| 127 | The single observed merge identifies copy 42 with parent 38, at PositiveFunction term 304 ≤ ValueRow 4, parent index 4. |
| 432, 439 | Int reaches row38, now at level 1, and then row8. |
| 552–553 | FreshUse transport copies Int lower-bound witnesses from row8 to the second-use row56, preserving parent relations 189/186. |
| 755–758 | row56 ≤ row6 replays those actual Int witnesses into row6. |
| 808 | row6, already carrying Int lower witnesses, is compared with Bool. |
| 815–817 | The resulting Int ≤ Bool comparisons are dispatched; the public conflict reports the second full call. |

This authenticates the displayed merge and constraint propagation for the
rejecting input. It is stronger than borrowing a trace from the unannotated
control. It does not establish that the merge's retained source support is
the original signed receiving incidence, that it satisfies the approved
abstract SCC criterion, or that the full original source judgment holds.
The regular-graph atom-separation theorem in
[OriginalPrincipalClosure](lean/YulangClosure/OriginalPrincipalClosure.lean)
can reject such a pair of ground constraints once its graph and constraint
correspondence is supplied. A trace printout is not that correspondence.

### Reproducing the private observer

The [preparation script](fixtures/2026-10-26-prepare-native-observer.py)
requires a new destination outside the repository. It checks the four exact
base hashes and clean native inputs, copies the tracked solver bytes, applies
the observation patch only in the new directory, and points unchanged
dependencies back to the source checkout. Its generated Cargo lock starts
from the repository lock; the 22 registry packages in the reproduced client
retain exactly the original versions/checksums. The script itself neither
builds nor runs inference.

From the repository root, with the matching installed Rust toolchain and
dependencies available:

```sh
proof_dir="$(mktemp -d)"
python3 notes/theory/fixtures/2026-10-26-prepare-native-observer.py "$proof_dir/observer"
CARGO_TARGET_DIR="$proof_dir/target" CARGO_PROFILE_DEV_DEBUG=0 cargo build --offline --manifest-path "$proof_dir/observer/Cargo.toml" -j1
YULANG_PROOF_TRACE_LIMIT=12000 timeout 20s "$proof_dir/target/debug/yulang-finite-prefix-observer" notes/theory/fixtures/2026-10-26-direct-return-rejection.yu > "$proof_dir/result.txt" 2> "$proof_dir/trace.txt"
```

The recorded runs additionally used a 1 GiB process address-space bound.
`PROOF_TRACE_PREFIX_LIMIT` explicitly means that an observation stopped;
neither this sentinel nor a wall timeout proves solver termination or
divergence. No cutoff occurred on this fixture.

The fresh preparation/build check exposed one duplicate Cargo workspace
declaration; it was removed from the private preparation recipe. The final
isolated build then exited 0 in 22.065 s, followed by the identical trace.
The initial layout failure is retained in the scratch receipt and is not
reported as an inference result. No raw logs or build artifacts are in Git.

## Explicit Name-callee variant

The [aliased fixture](fixtures/2026-10-26-direct-return-aliased.yu) binds
`gi = f {a:0}` and `gb = f {a:true}`, then uses `gi 0` and `gb true` at the
same written Int/Bool boundaries. Its seven Apps all have Name callees.
The unchanged CLI also rejects it: exit 1 in 1.626 s, Int/Bool conflict at
`gb true`, line 6:21, bytes 135..139. This is a separately observed exact
source, not a claim that inserting aliases preserves inference history or
an ANF equivalence theorem. The original nested-App source remains primary.

## Decisive original proof obligations

A proposed closed source witness uses `S = Int ∨ Bool`, a record with an
actual evaluated Value field `a:S`, one fixed `h` contract accepting that record, and the same captured
`f` whose returned closure has both complete checked Int and Bool views. The
actual `y` inlet and formal description must stay fixed at `S`; the two
checked views refine that one inlet with their own return evidence. They
must not choose different shared/OneShot fields after seeing a challenge.

The proposed body evaluates `h x`, partially applies `f` to the actual record,
discards the resulting closure and returns the same `y`. This is a candidate
construction, not an already supplied full membership theorem. The required
original witness must still construct all four value/world/trace/carrier
postfixed components, actual closure formation/profile, complete Strict and
ReadInvoke phases, all independently admitted carrier/response/future cases,
actual current worlds and shared witnesses. Raw return correlation or a
scalar Int/Bool valuation does not discharge those requirements. The earlier
[fixed two-view construction](2026-10-24-active-capture-field-graph.md) gives
conditional publication laws, not these missing complete memberships.

The later [source-constructor manuscript](2026-10-26-original-principal-closure.md)
constructs the fixed descriptor, Shared and four-sort phase family and gives
the exact remaining seven Call-certificate obligations. Its checked Lean
module preserves the source census and proves the separate algebraic
obstruction. This observation note does not promote that conditional source
construction to a completed original typing judgment.

If that source witness is constructed, this reproduced rejection is evidence
against current compiler source completeness. To refute the **approved
abstract occurrence rule**, its exact source origin/receiver and produced
pairs must additionally be authenticated against that rule; the current
any-support consumer cannot silently stand in for that correspondence.
Inference soundness and algorithmic termination are different obligations.

## Frozen evidence

Raw logs and build products remain outside the repository. The checked-in
fixtures and reproduction commands are the deliverable; the hashes below
identify this run without committing console output.

| Evidence | SHA-256 |
| --- | --- |
| `2026-10-26-direct-return-rejection.yu` | `1f1e498263f807cf180c5ea36837aef966647c58831f7d8490599dddf0bcb9f4` |
| `2026-10-26-scalar-return-control.yu` | `011360063aead952506f948a60bbf39ac0e0137c4865e7497a64f106b1c7e784` |
| `2026-10-26-direct-return-unannotated.yu` | `81489a794a998e3ca1b8676a5c9b432c8d04f2a6bf9f31ff06c0462815248b80` |
| `Locked build output` | `e2856fb8a9a2bc01299f3c83ea2d3a2d99104b10aeab2d3a5089f0205bee00b9` |
| `409-input manifest` | `d766fbe003f6723d30a1fb7b43a176d0f5848f5d7fd47f86c3e458a3b00de239` |
| `Rejecting CLI stderr` | `a3c34a935345b07832eb23a59d4fef0622019492479c525588f4b6dc314deb1b` |
| `Each successful CLI stdout` | `35b43fd4f5be490acf71a2958e4b28bf64f7e6a7ce672cbfba1a7d7cd1cb16ef` |
| `Rejected-source public Call observations` | `7d6046f171fd7cad4310cdf4bd099fd999718b3920cf4b9ca15177b81649a874` |
| `Unannotated retained-state observation` | `8a1fb6cf2f1581a5a6b83324bb60bc15c0a3268a9831fb4266fb473967394919` |
| `2026-10-26-direct-return-aliased.yu` | `74cc1412fd1d5fc44713567756190439cbbd7168023d8f85d14899059d73b617` |
| `Observation-only patch` | `99c3a3f402381581820c706cb1748b7216d67cb3d50ebf9193959a68e1216fb3` |
| `Exact rejecting-input trace` | `3d8e9aab2c3339efd6ab22059284919e6863bfc057a0201fa0a9e44175df744d` |
| `Fresh private observer build` | `603d090241b2d8483296cd24215b21ffc6f711de2505335bcac12911f6769254` |

Scratch evidence: `/workspace/scratch/e3678bef96db/native-principal-r3`.
The additional observation/build receipts are in
`/workspace/scratch/e3678bef96db/native-termination-trace-r3` and
`/workspace/scratch/e3678bef96db/native-observer-repro-r3`.

## Pre-merge association evidence

The separately reviewed [association extension](fixtures/2026-10-26-native-association-observer.patch)
adds immutable readouts immediately after trace event 127 and before that
merge's representative checks, journal writes, bound copying or row mutation.
It does not bypass the public conflict-export guard. The readout is deliberately
limited to parent records 0--4, relations 0--67 and their selected retained
evidence, together with the complete `Graph` Debug value at that point. It is
not an exhaustive-context census and introduces no inference-state writes.

Apply this extension after the existing preparation command and before the
build command above, using the same new external directory:

```sh
patch --batch --forward -d "$proof_dir/observer/source/crates/yu-solver" -p1 < notes/theory/fixtures/2026-10-26-native-association-observer.patch
```

The unchanged observer client then emits `ASSOCIATION_` lines alongside the
original `PROOF_TRACE` stream. This is observation code, not a production
patch. Formatting and output allocate and take time; the readout does not
establish a formal equivalence theorem between instrumented and native runs.

One exact-fixture run completed in 0.372 s with observer exit 0, one Int/Bool
conflict and seven source Calls. No timeout or prefix cutoff occurred. Removing
the association lines leaves all 1,404 original trace lines byte-for-byte
unchanged, with SHA-256
`3d8e9aab2c3339efd6ab22059284919e6863bfc057a0201fa0a9e44175df744d`.
The successful incremental build exited 0 in 8.877 s. An earlier failed build
(exit 101, 4.796 s) used the nonexistent `self.candidate_source` path; the final
extension correctly reads `self.batch.candidate_source`. That failure is a
build observation, not an inference outcome.

The 337 association lines contain five parents, one Graph, 68 relations,
105 dependencies, 33 origins, 63 admissions and 62 emissions. Every printed
`RelationId` resolves inside the selected relation prefix; every printed
emission's admission also occurs in the readout. The four FunctionPort records
of the relevant cut and the producer links into the receiving boundary are
present. Their original signed interpretation is a separate proof obligation;
the source-set union does not itself select one original receiving Value.

| Frozen evidence | SHA-256 |
| --- | --- |
| Association extension patch | `890fdc94090809ae33c0af93b4bccd7f0cd22447aad2752dea1c02c975a0231c` |
| Extended private `candidate_context.rs` | `0c7eb06e357fbb57e2e10ce3d308ed6dace5c07a0c4bd1b534f2e34fea57517a` |
| Extended private `candidate_intrusion.rs` | `3cecc6455588e79873fbc2b613eacdbfe38c5c8119441b2bfbcd539ceb45a868` |
| Selected association readout | `cdceaf656e6100e3361d344bf9f927bf43925099c2077b3e3c654ac585765d36` |
| Combined stderr | `8a52c0817b0201b4f5262aad61631c0a8b717c2f8b6a0dfe4986f8cc5222cf29` |
| Successful build log | `a4226663135b05e178c9a27810b77d0be2deeaec679e940407e962910a332126` |

The association hash identifies this frozen readout; Debug iteration order for
HashMaps is not a portable textual ordering guarantee. Receipts and raw output
are retained outside Git at
`/workspace/scratch/e3678bef96db/native-association-observer-r3`.
