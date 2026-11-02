# Sprint R249 — prior replay/restoration owner lifetime

Status: ADMITTED under the unchanged full goal: Yulang inference soundness and its Rust implementation. Preserve the original parent theorem, all source forms, arbitrary independent satisfying assignment and semantic authority. Parent delta stays zero except for a justified result actually applied at its original edge.

## Fixed outcome

R248's reviewed inventory result reduces local entry-owner premises but leaves `R248-PRIOR-OWNER-1`: prior replay/restoration/typed-frame handles must remain attached to the same owner and child index/cursor after earlier successful terminal actions.

For accepted non-test successful histories, derive whether an unconsumed replay/restoration/typed-frame handle created earlier still designates the same operation, child index, cursor and owner after terminal processing, Ready delivery, commit or reclamation. Distinguish unconsumed ownership from a completed receipt and from a Running/Ready return barrier. Apply any derived preservation law to R248 §8 and the corresponding R245 current-return premise. If an equation remains open, freeze the first exact producer/consumer expression and its owner.

R142 theory/handoff are historical method inputs only. Rebuild correspondence against the currently pinned `candidate_context.rs`, `candidate_extrusion.rs` and `lib.rs` transitions; their old source hashes and bounded R143 result do not establish present coverage. Do not assume that numeric-ID validity proves operation or child identity.

Falsifier: an accepted non-test successful prefix reclaims an owner with an unconsumed handle, redirects it to another child, or permits duplicate consumption. Synthetic identifiers and test-only retry paths are not falsifiers. Keep evidence authenticity, R71, drain/ack settlement, F1/FK1, foreign continuation, and full parent soundness separate.

## Assignment, exact leases, inputs and limits

One registered `prover`, Sol/high, no descendants. Exact write leases:

- `notes/theory/2026-11-02-prior-replay-owner-lifetime-r249.md`
- `tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md`

Maximum 2,400 active seconds. Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git. If a needed owner lies outside this manifest, stop citing it and return the exact path/hash to Luna before reading its body.

Baseline HEAD: `5903770e4ee58cbae726ae3424010ab8d0853e94`.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `notes/theory/2026-11-02-extrusion-entry-inventories-r248.md` | `bc8ce026a4027110ee36c35178ec129d778bad2e7274c2789fdc5dad0a142713` |
| `tasks/agent-loop/inbox/extrusion-entry-inventories-r248.md` | `984bb9b3f878e7048efdf2aa1b75615b32b45426bad095b56674210caf6c21d3` |
| `notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md` | `7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e` |
| `tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md` | `647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322` |
| `notes/theory/2026-10-20-r142-replay-completion.md` | `5f1715db8ccef8777f89d9b64e8625efead68974be53beb8f55a84a86a014a2c` |
| `tasks/agent-loop/inbox/20261020-r142-proof.md` | `cbaa0c7e79ca9c04b4325b8358ec17664deb51eb4dc620be0c7e242041b44c26` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/candidate_receiver.rs` | `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade` |

Verify all hashes before citation. Record each current transition, owner and handle state, exact application, residuals, output hashes, resource receipt and STOPPED-writing status. Do not claim the unchanged parent theorem is closed.
