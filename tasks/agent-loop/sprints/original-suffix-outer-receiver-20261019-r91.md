# Sprint R91 — resumed suffix reaches a distinct outer receiver

Status: APPROVED FOR RESEARCH; candidate semantics only.  
Branch / baseline: `research/simple-sub-intrusion` at `44a23937f99c55dea03714e82581e4a5a409576d`.  
Primary: Luna. Exact runtime owners and inputs are pinned below.  
Parent: original effect-hygiene/source-native obligation; original Simple-sub and evaluator claims and quantifiers remain unchanged.

## Outcome and falsifier

Construct a source-to-runtime evidence slice in which `signal::ping` is handled
by an inner Catch, its captured continuation resumes the original suffix, the
suffix emits `write::ping`, and an outer receiver handles that different
effect-family declaration. Both declarations intentionally use the spelling
`ping`; source family/member identity, request identity, receiver provenance,
and resumed suffix must remain distinct. The fixture's expected `--run` result
is `23`.

Success requires an occurrence-indexed construction from the exact raw source
through parser, LocalSource, RuntimeProgram, request capture/resumption and
outer local Grant, plus one authorized public CLI run with exit 0/stdout `23`.
The executable result is evidence for this fixture only. It cannot replace the
source/runtime derivation, establish general hygiene, prove native residual or
joint K,D correspondence, or close A/B/F1/FK1.

Falsifiers include parser recovery or a source-owner mismatch, merging the two
effect identities, resuming a newly constructed expression instead of the
captured original suffix, outer selection without its live receiver's positive
Grant, a different CLI result, or a new semantic premise. Stop at the first
unsupported constructor or consumer; return the exact missing owner.

## Exact source fixture

Implementation lane creates only
`tools/inference-playground/examples/original-suffix-outer-receiver.yu` with
these UTF-8 bytes and no final newline:

```yu
act signal:
    our ping: () -> int
act write:
    our ping: int -> int
my relay (thunk:[signal] int) =
    catch thunk { signal::ping(), k -> k 11 }
my receive (pending:[write] int) =
    catch pending { write::ping(p), _ -> 23 }
my main = receive (relay {
    my first = signal::ping()
    write::ping first
})
```

The proof lane proves the two member declarations have distinct resolved
identities despite equal spelling; `relay` receives the `[signal]` computation,
handles the first Unit request with `11`, and invokes the captured continuation
on the exact post-request suffix `write::ping first`; that suffix request is
then received by `receive` under its `[write]` permission and returns `23`.
Preserve all actual source and dynamic event identities; do not infer them from
textual names.

## Lanes and leases

1. Proof: one `prover` assignment, requested Sol/high, 600 seconds charged at
   grant. Write only
   `notes/theory/2026-10-19-r91-original-suffix-outer-receiver.md` and
   `tasks/agent-loop/inbox/20261019-r91-proof.md`. Read the pins below and the
   exact R78/R88 evidence; no tests, build, runtime probe or Git.
2. Implementation: after the proof writer stops, one `implementer` assignment,
   requested Luna/high, 300 seconds charged at grant. Write only the exact
   fixture path above. Do not alter parser/compiler/runtime behavior or expected
   outputs. Stop if current source syntax rejects the fixture.
3. Luna owns exactly one CLI command after both artifacts freeze:

   ```sh
   CARGO_BUILD_JOBS=2 timeout 120s cargo run -q -p yu-playground -- --run main --steps 100000 tools/inference-playground/examples/original-suffix-outer-receiver.yu
   ```

No tests or other compiler/build/probe commands are authorized by this sprint.
Proof and implementation run sequentially because three inherited assignments
and one legacy slot reservation remain UNKNOWN/reserved under the six-slot cap.
Fresh read-only compiler/source review (240 seconds) and spec review (240
seconds) run sequentially after authors stop and the CLI receipt is frozen.
Luna integration: 300 seconds. Aggregate stage-1 cap: 1800 seconds; Astra 0.

## Authority, pins and limits

Authority is existing approved syntax, LocalSource construction, candidate
inference and evaluator behavior only. No new semantics, production promotion,
or role/method adoption. R85 remains `AWAITING_USER_ADOPTION`. Keep method/role
syntax and its proof-backed positive path in the next-action queue; the R89
dotted-target/`with:` boundary remains deferred pending semantic clarification.
All six hygiene fronts remain open except for any precisely reviewed finite
premise this evidence actually narrows. A/B remain OPEN 0→0, R50
`NOT_ADOPTED`, R67 remains OPEN, and source/native, F1/FK1, joint K,D and
residual obligations remain separate.

Direct dependency SHA-256 values at freeze:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-syntax/src/cursor.rs` | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| `crates/yu-syntax/src/declaration/act_decl.rs` | `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/expression/case_like.rs` | `6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `notes/theory/2026-10-19-r78-receiving-selection-certificate.md` | `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` |
| `notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md` | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Recheck every pin at producer freeze and review. Preserve unknown leases; never
claim a worker stopped without a runtime receipt. Reviewers must not be authors
or contributors to the frozen artifacts. Only Luna stages explicit paths,
reviews the whole outbound range and commits/pushes.
