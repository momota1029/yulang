# R114 rev2 source identity continuation: frozen dependency obstruction

Status: **FROZEN CANDIDATE / INPUT MISMATCH / STOPPED**. Revision 1.
Author: `/root/r114_source_identity_proof`, sole author, no descendants or
coauthors. Requested model/effort: configured Sol/high. Observed model/effort:
UNKNOWN/UNKNOWN; no worker-visible runtime metadata establishes either.
This is an obstruction receipt, not a completed proof, independent review,
source/native certification, or production authority.

## Parent and exact result

Luna assigned R114 rev2 under
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev2.md`,
SHA-256 `ad2bf83a1e0769745cb8901cceb182aa75f5c7f7f85bba1ed3d20bb23dd9fc49`.
The unchanged rev1 contract is
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md`,
SHA-256 `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
Its complete frozen input table remains binding. Rev2 explicitly requires a
stop on any mismatch, without repair, retry, or pin expansion.

**Actual result:** startup SHA-256 revalidation found seven mismatching rev1
direct inputs. This triggers the stop condition before a proof can be completed
or applied. P-ID is **OPEN**. No new conditional theorem is substituted for it.
The rev1 finite conditional source/runtime argument remains unchanged and
unpromoted; this packet discharges none of its premises.

The exact source remains 195 UTF-8 bytes without final LF, SHA-256
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`:

```yu
act signal:
    our ping: bool -> bool
act other:
    our unrelated: int -> int
my receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }
my main = receive (signal::ping true)
```

The original finite claim, conditional on ordinary successful preparation,
requires authentic distinct family identities, retention of the original
`[other]` formal through runtime projection, exclusion of the closed-primitive
bypass, direct Machine `Unavailable(HandlerEvidence(original_handler_site))`,
and public stdin CLI failure with empty stdout and a diagnostic derived from
that original Machine site. Missing positive evidence is neither language
rejection nor proof of forwarding. All original quantifiers, premises,
falsifiers, accepted source domain, and exclusions are retained.

## Exact revalidation evidence

Read-only Python standard-library SHA-256 calculations checked both contract
hashes, all 19 rev1 table inputs, all 11 rev2 table inputs, and the exact source
literal. Both contracts and the source matched. Twelve rev1 inputs and all
11 rev2 inputs matched; seven rev1 inputs did not:

| Input | Frozen expected SHA-256 | Observed SHA-256 |
|---|---|---|
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` | `da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |

These are byte mismatches, with no assertion about their semantic cause,
author, approval, or compatibility. No changed input is silently accepted.
Web input hashes matched at this startup check; subsequent independent writes
are not represented by that observation.

The relevant matching continuation inputs are:

| Input | SHA-256 |
|---|---|
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| Rev1 proof, authored by `/root/r114_proof` | `447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92` |
| Rev1 proof handoff | `1e557c2adbcf53861701fa0a11679124fde1ebf87606a35624c923be6eba3f18` |
| Frozen rev1 CLI test | `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13` |
| Frozen rev1 implementation handoff | `6eecb772e7ee30d7582c1f5d89b47e9310273f18a393c550f464f67960cf609e` |

## Source/native evidence and parent application boundary

The startup read also exposed the two newly authorized identity owners:
`source_identity.rs::{source_keys,try_source_keys}` walk parse-owned
`SourceNode`s, inserting `(node.syntax().clone(), node.key())`;
`full_parse.rs::SourceNode::key` retains parse brand, green allocation and start;
`SourceNodeKey::eq` compares all three. This is an inspected constructor/equality
observation only. No completed exact-source derivation, inequality theorem, or
handoff into changed HIR/runtime owners is claimed under a failed frozen input
check. The same tool orchestration returned these source reads after its hash
check; no additional theorem investigation followed the mismatch result.

P-ID remains: the exact successfully formed parse's `signal` and `other`
ActDeclaration nodes receive authentic unequal keys, and the owning
`source_annotation::declarations` construction therefore produces unequal
`SourceEffectId`s. The corresponding consumer owners remain
`source_annotation::declarations` / operation lookup,
`local_source::Builder::resolve_operation` and parameter annotation formation,
`program.rs` formal projection, `RootCompSchema::from_parameter`, and
`Receiving::local_grant`, followed by Machine and public execute/CLI boundaries.
The changed module, LocalSource, candidate, projection, bypass, and machine
inputs prevent claiming the frozen rev1 bridge applies to the current workspace.

The frozen rev1 proof is reused solely to identify its exact P-ID and retained
finite conditional calculation. Its prior boundary is not retrospectively
rewritten. Historical runtime assertions and the unverified CLI test are not
current execution evidence or source constructor proof. No historical failure
or success is generalized beyond its actual premises.

## Resources, mutual TODOs, and cessation

Cap: 240 seconds; zero Astra; no children, heavy processes, tests, builds,
compiler/CLI invocations, formatter, or Git. Only read/hash operations and the
two explicitly leased research outputs were used. The first worker-visible
clock observation was `2026-10-19 15:16:02 UTC`; time before that observation
was not independently measured. Luna should retain the full 240-second lane
reservation conservatively; this STOP releases no resource budget for reuse.

No production implementation TODO is justified from these byte mismatches.
Luna owns dependency reconciliation and any future frozen-contract revision;
the leaf cannot re-pin sources or repair this contract. Exact falsifier for a
future reconciliation is any remaining mismatch against its newly approved
complete dependency table. Only after a fresh explicit grant can a proof owner
resume the direct key-authenticity/inequality derivation and apply it to P-ID.
Luna also owns any decision to revalidate changed source-to-runtime premises,
verification, fresh independent review, state, integration, and production gates.

All new paths are exactly this artifact and
`tasks/agent-loop/inbox/20261020-r114-proof-continuation.md`; no scratch path.
Writer STOPPED upon freezing the handoff; no background work, descendants, or
pending mutation remains. Original Simple-sub/evaluator A/B, all general
effect-hygiene, adoption, source-law and production gates remain OPEN.
