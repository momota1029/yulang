# Sprint R92 — admit indented binding bodies through the existing Block path

Status: APPROVED FOR RESEARCH; one owner-local semantics-preserving candidate.  
Baseline: `44a23937f99c55dea03714e82581e4a5a409576d`.  
Parent: original effect-hygiene/source-native obligation; original inference/evaluator claims and quantifiers unchanged.

## R91 evidence and exact outcome

R91 is closed as unmet in
[`notes/progress/2026-10-19-r91-closeout.md`](../../../notes/progress/2026-10-19-r91-closeout.md).
The exact fixture remains
`tools/inference-playground/examples/original-suffix-outer-receiver.yu`,
SHA-256 `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`.
Its sole R91 `--run` attempt exited 1 with
`candidate lowering unavailable: StructuralProjection`.

Independent source review established the concrete mismatch. The pinned syntax
constructor `binding.rs::binding_body_normalized` emits an
`IndentedStatementBlock` for the fixture's indented `relay` and `receive`
bodies. `yu-hir::module::local_source::body` extracts the `BindingBody` child
and rejects it unless it is `OperatorChain`. That happens before the already
existing `Builder::expression` branch for `IndentedStatementBlock`, so the
existing `block()` consumer cannot currently run for those definitions.

The outcome is to make only the `local_source.rs` BindingBody adapter preserve
and forward an admitted `IndentedStatementBlock` to the existing expression / 
Block consumer, while retaining the existing `OperatorChain` path and
validation. The byte-identical fixture must then pass public candidate lowering
and execution with exit 0/stdout `23`. No source rewrite, semantic bypass,
diagnostic suppression or broader compiler fix is in scope.

## Falsifiers and source correspondence

Use a forward simulation from the exact CST child to the existing
`LocalSourceForm::Block`: preserve the child SyntaxNode and its key/range; let
the existing `Builder::expression` route select `block()`; preserve binding
source key, Local ID, initializer slot, lexical restore and final expression
slot; verify the one local `first` is published before the final expression
resolves it. The later runtime claim remains conditional on these real source
objects.

Falsifiers: flattening/rebuilding a node and losing source identity, dropping or
reordering a Statement, changing an ordinary `OperatorChain` body's behavior,
accepting a block without `block()`'s structural checks, any other lowering
failure, or a result other than 23. Stop if the implementation needs another
source owner, solver/runtime change or semantic decision; return that exact
dependency to Luna before expanding the lease.

## Sequential lanes and exact leases

The lanes are sequential because the proof must inspect the final frozen bytes
of the one file changed by implementation, and only six active/reserved/unknown
assignments are allowed.

1. Implementation, `implementer` requested Luna/high, 900 seconds charged:
   write only `crates/yu-hir/src/module/local_source.rs`. Extend `body()` only
   to retain and return the supported `IndentedStatementBlock` child as well as
   the existing `OperatorChain`, allowing the existing expression consumer to
   perform its own validation. Do not change other files, source syntax,
   expected outputs, tests or semantics. Freeze the exact diff, new file hash,
   and writer-stop receipt. No tests, builds, CLI, probes or Git in this lane.
2. Proof/source lane, `prover` requested Sol/high, 600 seconds charged, begins
   only after implementation writes stop. Write only
   `notes/theory/2026-10-19-r92-indented-binding-body-correspondence.md` and
   `tasks/agent-loop/inbox/20261019-r92-proof.md`. Read the frozen implementation
   diff and final `local_source.rs` hash plus the exact R91 inputs and direct
   owners below. Establish the source correspondence for the unchanged fixture
   using actual node/key/range, local binder, initializer, final-expression,
   work-stack and lexical-scope constructors. Prove no constructor or consumer
   changed after the recorded freeze. No tests/builds/CLI/probes/Git.
3. Luna owns exactly one public command after both lanes freeze:

   ```sh
   CARGO_BUILD_JOBS=2 timeout 120s cargo run -q -p yu-playground -- --run main --steps 100000 tools/inference-playground/examples/original-suffix-outer-receiver.yu
   ```

4. After authors stop and the execution receipt freezes, obtain one fresh
   compiler/source review (300 seconds) and one fresh spec review (300 seconds),
   sequentially. Luna integration/adjudication: 300 seconds. Verification
   allowance: one exact CLI process, at most 240 seconds. Aggregate R92 cap:
   2640 seconds. Astra 0. Existing R91 charges are immutable and not refunded.

No test is added or run by this contract. The one CLI command is the observable
source-surface check. Static `python3 tools/agent_sprint.py check` may verify
scheduling records only and establishes no compiler behavior.

## Authority and direct dependencies

Authority is existing accepted syntax, LocalSource projection, candidate
inference and evaluator behavior. No new method/role semantics or production
promotion. R85 remains AWAITING_USER_ADOPTION. Keep proof-backed method/role
surface work in the next-action queue and continue bounded rotation across all
six effect-hygiene fronts; R92 advances only the unmatched-request/original-
suffix plus source-to-runtime bridge. A/B remains OPEN 0→0; R50 NOT_ADOPTED;
R67, F1/FK1, source/native correspondence, joint K,D and residual obligations
remain separately OPEN.

At baseline, direct hashes required by the writer/proof/review component are:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` (implementation write target; proof pins the final frozen hash) |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `notes/theory/2026-10-19-r91-original-suffix-outer-receiver-rev2.md` | `f7605fbf7b4ec14d1fc916488d9757e7df4380856259db2bb9819033960cc729` (candidate only; superseded at the LocalSource admission premise) |
| `notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md` | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| `notes/theory/2026-10-19-r78-receiving-selection-certificate.md` | `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` |
| `tools/inference-playground/examples/original-suffix-outer-receiver.yu` | `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7` (read-only exact input) |

Every read-only dependency hash must match before use. The writer records the
new `local_source.rs` hash; Luna then supplies it as the exact proof/review
target. Do not treat the R91 rejected bridge as independent proof of R92. Only
Luna may stage explicit intended paths or commit/push after reviewing the full
outbound range.
