# Direct-return recursive source: native rejection and its proof boundary

Date: 2026-10-26. Branch: `yulang3`. Native build base:
`99f18bdc54df8057f5a6d5d4bec5dc449336c234`; verified source-identical at
`11b0bf084a66119b83c75f26a75badfa5ff5316b`.

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
`ArtifactMismatch` (`crates/yu-solver/src/shadow_apply.rs`). That guard was
preserved, so the exact rejecting candidate's intrusion state is not claimed
as an observed trace.

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
They cannot be substituted for the rejecting source's unobserved native
history merely because the function bodies are equal.

## Decisive original proof obligations

A proposed closed source witness uses `S = Int ∨ Bool`, a record with a pure
`a:S` field, one fixed `h` contract accepting that record, and the same captured
`f` whose returned closure has both complete checked Int and Bool views. The
actual `y` inlet and formal description must stay fixed at `S`; the two
checked views refine that one inlet with their own return evidence. They
must not choose different shared/OneShot fields after seeing a challenge.

The proposed body evaluates `h x`, partially applies `f` to the pure record,
discards the resulting closure and returns the same `y`. This is a candidate
construction, not an already supplied full membership theorem. The required
original witness must still construct all four value/world/trace/carrier
postfixed components, actual closure formation/profile, complete Strict and
ReadInvoke phases, all independently admitted carrier/response/future cases,
actual current worlds and shared witnesses. Raw return correlation or a
scalar Int/Bool valuation does not discharge those requirements. The earlier
[fixed two-view construction](2026-10-24-active-capture-field-graph.md) gives
conditional publication laws, not these missing complete memberships.

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

Scratch evidence: `/workspace/scratch/e3678bef96db/native-principal-r3`.
