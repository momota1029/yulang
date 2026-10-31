# R105 source-contract adjudication and logical-owner bridge

Status: **ADMITTED** under the standing user-authorized Rust/Lean goal.
Parent goal remains Yulang inference/source soundness; no language semantics,
accepted source behavior, production authority, or parent quantifier changes.
Baseline Git commit: `d19315503f911c615d4d3a9ab9329146f757acbf`.
R104 outcome: `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`.

## Fixed question and evidence

R104's bounded Lean gate passed and its final Rust source-promotion gate failed.
The reviewed Cargo evidence retains four failing assertions and establishes:

- the shared-tail `Int ≤ Function` diagnostic already exists after root
  execution; late `E` adds no error;
- the unequal-transport fixture produces only identity representatives and no
  `ParentWrite` event;
- a separate pair-returning provider creates Support, while the original
  recursive consumer returns no effect forms;
- both fresh-use templates lack captured Support, so no remapping loss has been
  demonstrated.

The shared-tail test source is
`my left (f:int -> ['e] int): (int -> ['e] int) -> (int -> ['e] int) =
{ my pure x = 1; pure }`. `candidate_source.rs` applies a named header result
annotation to the terminal body and retains the outer Lambda. This makes a
fixture-shape mismatch a concrete hypothesis for independent adjudication; it
is not an established explanation. The authoritative annotation policy remains
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1,
4–5. No behavior change is proposed or authorized here.

## Rust lane: source contract and one valid path

Owner: `/root/r104_source_causality`, resumed only after this admission.
The owner has exactly one mutable Rust path:

- `crates/yu-solver/src/candidate_effect.rs`, **test code only**.
- Handoff: `tasks/agent-loop/inbox/effect-permission-source-contract-r105-source.md`.

Frozen baseline hashes:

| Path | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `shadow_apply.rs` | `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f` |
| `candidate_receiver.rs` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

First classify all four protected failures against the actual source annotation
target, generated endpoint, effect polarity and consumer/capture path. In
particular establish whether the shared-tail source is admitted by the ordinary
source preflight, and whether the annotation target matches the terminal
body's source type. Read `candidate_source.rs`, `candidate_effect.rs`, and
`candidate_scheme.rs`; do not write production owners. If no public/source
admission route can validate a type-correct replacement fixture, stop before
editing and return that exact blocker.

If the mismatch hypothesis survives that check, add one separately named,
correctly typed test path through source admission, named result annotation,
returned function, capture, fresh use and the actual consumer. Preserve every
R104 fixture and assertion. The result must discriminate source-fixture error
from an owner-local solver omission without fabricating constraints. Otherwise
return the disproving evidence and make no Rust edit.

One fresh `compiler_referee` must review the frozen handoff and candidate before
Cargo. At most one Cargo invocation is authorized, and only for a reviewed new
test candidate. Exact command:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests::r105_ -- --test-threads=1 --show-output
```

Run with CPU affinity 0, `timeout -k 5s 180s`, peak RSS ≤2 GiB, no more than one
Cargo process, and exactly
`CARGO_TARGET_DIR=/dev/shm/yulang-effect-source-contract-20261101-r105-target`.
The target must stay below 6 GiB and be fully removed after execution. Do not
run another Rust command, retry, create another target, or use a persistent
workspace/cache in R105. A missing type-correct path or rejected review spends
no Cargo call. Any source-semantic change requires a separate user decision.

## Proof lane: connect route encodings without closing the parent

Owner: registered `lean_prover`; one exact handoff path:
`tasks/agent-loop/inbox/effect-permission-logical-owner-r105-proof.md`.
The only mutable Lean path is
`notes/theory/lean/YulangClosure/SourceLogicalOwnerBridgeR105.lean`.

Inputs are frozen: R104 module SHA-256
`0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39`, R104
handoff SHA-256
`5f9440ec72b2dbd058b2e3975040ec10ecf1778ceb9e116d9b7ab724c3efdef7`, source
syntax SHA-256
`3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`, and
generation SHA-256
`126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
The original event owner source is `OriginalSourceEvents.lean`, SHA-256
`cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`.
Read its `sourceOwners`, `Owner`, `ActualKey` and `binderOwner`, plus the
selected Source-Generalize claim. Construct the route bridge for R104's App
and Lambda logical occurrences against those original owner routes. This is
not a pointwise Bool-to-Nat map: forest-head steps consume no route tag,
siblings use `1`, and choice-right uses `3`; binder telescopes retain their
owner routes. Preserve the original source scope and all constructors.

`binderOwner` catalogs actual events, retained Shared and EventProof while
omitting ViewLogic. Keep ViewLogic in a separate logical catalogue; do not
claim it belongs to executable runtime `sourceOwners` or invent a runtime
owner. The first remaining semantic bridge is deriving original-source logical
admission and decoded formal contract readout for these exact generated
occurrences. An arbitrary `base.logical` premise is insufficient. Preserve the
selected descriptor/interface and Shared owner at the actual Name consumer in
both entry modes; the parent still needs one lawful joint strategy under the
original scopes.

The leaf may deliver a checked syntactic correspondence or an exact obstruction;
it may not assume semantic admission, source typing, local laws, or the parent
theorem. No sorry, project axiom, checker bypass, or source restriction. Freeze
the file and handoff for fresh independent review before the primary runs at most
one pinned flattened Lean stdin invocation. The primary records actual theorem
types, complete axiom audits and full output; no Lake cache, project build, or
persistent scratch. This bridge does not close the original source-parent, A/B,
effect hygiene, source/native or production gates.

## Shared envelope, review and integration

Luna owns integration and Git. Total sprint active-work envelope is 2,400
seconds; Astra assignments: 0. Keep at most four known active/reserved
assignments and reserve independent review/integration capacity. Rust and proof
authors work on disjoint exact leases. Fresh Rust and Lean reviewers do not
review their own lane. Executions are serialized and require frozen input
hashes plus passing pre-execution review. No worktree, persistent build target,
new dependency, or global environment change.

Successful bounded checks establish only their named fixture and syntactic
bridge. Preserve the four R104 failures unless separately rerun under a future
admission. Integration requires review of the complete outbound range. Push only
coherent reviewed evidence/code; never stage unrelated dirty paths or any
quarantined path. Stop at the earlier of the exact resource envelope, an
outside-owner/semantic blocker, or completion of both bounded outcomes.
