# R101: nested handler priority and shallow arm requests

Status: PRE_EDIT_REVIEW, revision 1. Primary: Luna `/root`.
Sprint selector: `/root/r99_front_selector`, sprint-end consultation after R100.

## Fixed finite outcome

Advance the ordered-handler-priority front through one exact source-to-runtime fixture with an inner Catch, an outer Catch, and a fresh request emitted by the selected inner arm. Preserve the existing language/runtime meaning and make no production semantic changes.

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::tick 7))
```

Freeze three cells before implementation edits:

1. Exact source: completes with integer `11`.
2. Swap only the two inner arms: completes with integer `23`.
3. Starting from exact source, change only the outer arm's operation pattern from `io::tick(p)` to `io::other(p)`: the inner first arm emits a new outward `tick` request with integer payload `11`; its SourceSite must identify the `io::tick 11` request in the inner arm, not the initial `io::tick 7` request.

These are predictions, not observed outcomes. If the exact source, grammar, receiver evidence, operation identity, or provenance does not support a cell, stop and record the precise obstruction; do not weaken the fixture or expected result.

## Source and runtime proof obligation

Constructively trace the exact three source strings through parser/CST, authentic operation declarations, `LocalSource` Catch arm order, candidate/runtime admission, `RuntimeProgram`, and machine frame/handler selection. Reuse R88 only for its proven single-Catch ordered-arm/source bridge. Derive the nested transition from the pinned machine constructors: distinguish the original `tick 7` request from the selected inner arm's new `tick 11` request; show which handler is active for each; show that selecting the inner arm removes that shallow handler before executing its body; and show the outer Catch's matching or operation-mismatch result.

Do not infer source/runtime correspondence from a test alone. Do not claim native residual, arbitrary continuation, source-wide soundness, or parent Simple-sub/evaluator closure. R100-ENTRY/P2/P3/P4 and R85 adoption remain unrelated and open.

Falsifiers include: parser lowering changes arm order; either request resolves to a different declaration identity; selection consults a non-innermost/incorrect handler; the selected inner arm executes while its own Catch remains active; swapped arms do not swap results; mismatch consumes the `tick` request; or the outward SourceSite points at the initial request rather than the inner arm.

## Implementation slice and one authorized command

Implementation lane owns only:

- `tools/inference-playground/tests/runtime_handler_priority.rs`
- `tasks/agent-loop/inbox/20261019-r101-implementation.md`

Add one focused integration test named `nested_handler_priority_and_shallow_arm_requests` with the exact three cells and exact expectations above. Use public parse/lower/candidate/runtime preparation APIs. No production source changes, fixture relaxation, unrelated test edits, or helper changes outside the leased test file.

After the test and proof freeze and CLEAN review, Luna may run exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_handler_priority nested_handler_priority_and_shallow_arm_requests -- --exact --nocapture
```

No retry, alternate command, build-only command, formatter or CLI is authorized. A preparation/compile failure consumes the single attempt if the command begins. A runtime mismatch ends R101 without repair.

## Proof outputs

- `notes/theory/2026-10-19-r101-nested-handler-priority.md`
- `tasks/agent-loop/inbox/20261019-r101-proof.md`

Proof lane owns only those two files and may not run commands. It must retain the three exact source cells, their byte-local delta, source operation/binder identities, ordered Catch construction, active-handler transitions, exact source-site lineage, and the remaining source/native limits.

## Frozen dependencies

| Input | SHA-256 |
|---|---|
| Charter `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| Ordinary computation package `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| R88 proof `notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md` | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| R88 closeout `notes/progress/2026-10-19-r88-closeout.md` | `e190f71dc28010b59a8ccd973d42c7f146622b15cb59df87b96394a6de081bd9` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| Existing receiving tests `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |

These dependencies are exact, frozen text/source inputs. Any drift stops the packet before dependent work; no unpinned owner may be added without a versioned contract and CLEAN delta review.

## Resources, reviews and stop

- Proof lane: Sol/high, cap 600 seconds.
- Implementation lane: Luna/high, cap 360 seconds.
- Fresh pre-edit and post-output spec review: 180 seconds total.
- One Luna-owned command: 120 seconds max.
- Independent compiler/source review: 240 seconds.
- Luna integration and closeout: 300 seconds.
- Total cap: 1,800 seconds; Astra 0.

Preserve three inherited UNKNOWN identities, board quarantine, and the reserved legacy implementation slot; admit at most two producers concurrently. Fresh independent review must validate frozen source correspondence, fixture deltas, and expected-output protection before the one command. Producers stop on handoff freeze. Luna owns current state, command, review adjudication, Git and closeout.

Stop without repair on source or dependency mismatch, review blocker/major, preparation failure, command failure, any outcome mismatch, provenance mismatch, or budget exhaustion. The six effect-hygiene fronts remain OPEN as broad research obligations; this one finite nested-priority slice does not close the ordered-handler front generally.
