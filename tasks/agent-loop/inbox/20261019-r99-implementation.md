# R99 implementation handoff

## Frozen outcome and implementation

Implemented the single fixed two-cell candidate integration test named
`unmatched_request_preserves_original_suffix_across_outer_handling` in
`tools/inference-playground/tests/runtime_unmatched.rs`.

The positive cell uses the contract fixture byte-for-byte (259 UTF-8 bytes;
SHA-256 `2c5f001cb1131882c78b90d4f1ed83810d0a31cd39291df352569aa20844ba2f`).
Its expected candidate result remains integer `23`. The negative cell is
created by changing only the outer operation pattern from
`io::tick(p), k -> k 23` to `io::other(p), k -> k 23` (260 bytes; SHA-256
`58fec23165d3f8ae1d2e318b4777b0d3e3e12711b8dc89b315d84e957441ee5b`). Its
fixed candidate prediction remains an outward declaration-owned `io::tick`
request with integer payload `7` and a retained continuation.

## Preparation and correspondence

The test independently parses the source with `parse_file`, lowers it with
`lower_module_with_local_source`, prepares `CandidateInference::solve` and
asserts no candidate conflicts, then constructs `RuntimeProgram::from_hir`
with `RuntimeEvidence::default()`, selects `main`, obtains execution roots,
starts the public `Machine`, and calls `run`.

The negative assertion compares the runtime operation ID with the `tick`
`SourceOperationId` collected from the source effect declaration. It also
checks payload `7` and positive continuation depth. The positive assertion
checks completed integer `23`. These source-constructor associations are
assertions in the test; no runtime behavior has yet been observed. The paired
outcomes remain candidate predictions until Luna's one authorized command.
This handoff claims no general source/native theorem or production authority.

## Evidence and checks

- Evidence class: candidate source/runtime integration test; runtime result
  unobserved.
- Checks not run: test, build, CLI, formatter, and Git commands.
- The proof lane separately reported a static possible `HandlerEvidence`
  obstruction on the resumed receiver. This is not a confirmed preparation
  mismatch or runtime observation; the fixed expected outcomes were not
  changed. Luna decides whether the one authorized execution proceeds after
  review.

## Pins and artifacts

All contract source pins were rechecked and match revision 2:

| Input | SHA-256 |
|---|---|
| `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |

| New artifact | Bytes | SHA-256 |
|---|---:|---|
| `tools/inference-playground/tests/runtime_unmatched.rs` | 3679 | `480229b78a1203c5c23fc4d7de78f9c7c257a1d8024661c3a24f9cd3fbbf1208` |

## Runtime and writer stop

Requested execution lane: Luna/high. Observed model and effort are not exposed
to this worker's runtime interface. The assignment cap was 360 seconds; work
completed within that cap (exact launch timestamp is not exposed here).

Writer stopped after these two leased paths only:

- `tools/inference-playground/tests/runtime_unmatched.rs`
- `tasks/agent-loop/inbox/20261019-r99-implementation.md`

No scratch or disposable paths were created. No test or execution was started.
