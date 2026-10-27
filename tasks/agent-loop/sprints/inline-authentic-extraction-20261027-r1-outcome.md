# INLINE-AUTHENTIC-EXTRACTION-20261027/r1 — failed incomplete outcome

Status: **FAILED_INCOMPLETE**, independently reviewed. No authentic source
trace was generated; no new Lean theorem or audit was produced. The result is a
resource-route failure plus reviewed defects in the provisional research tool.
It is not a counterexample to Yulang source behavior and does not close or
weaken the user’s full inference/executor goal.

## Frozen evidence

| Artifact | SHA-256 |
| --- | --- |
| Contract | `015c8c276dde26747b82cea6bf1ff14784a19ced91a8234487cff93c46b09254` |
| Provisional Rust candidate | `1ab6f3ed86d6bfc6d8f73baa40e5e46d5e3d451922af06fc1092a93ca29a39c0` |
| Implementation/source handoff | `a6b09733222243b779cfb8ed4c2e7ba4da3aa0fc3c765c0bc225ef7852463d30` |
| Proof/source-owner handoff | `001de7deee35769a92f7beacb12e253443fd74993aa04f327cb8979a996b880f` |
| Independent review | `2a861eb9d91ad7f800ed38ac826e290e09a71798528dab25252163c9a6d74f13` |

The reviewer independently checked all 28 contract input pins and the four
delegated artifact hashes. Both handoffs accurately state that neither Cargo
invocation reached the new executable; the historical process receipts remain
producer-reported and were not rerun. The reviewer confirmed that all expected
generated Lean outputs are absent.

## Adjudicated result

The two authorized offline, locked Cargo calls exited `101` while compiling the
unrelated `yu-solver` dependency under the one-CPU/1-GiB/120-second bound. One
used the playground package’s dependency graph; the other disabled dev debug
information and incremental compilation in isolated scratch. Both stopped
before extractor execution. No `LocalSourceIndex`, `HirParameterId`, occurrence
or source-range output was observed. Lean checker use was **0/6 calls** and
**0/360 seconds**. No tests were added or run. The first run’s repository
`target/` output remains untouched; the second target is under the leased
`/tmp/yulang-inline-authentic-extraction-20261027/impl/target`.

The fresh reviewer confirms three defects/omissions in the frozen candidate:

1. `inline_origin` emits `lambda_range.start..binder_range.end` as the binder
   token. It includes the Lambda prefix instead of using the exact binder
   `PositionId` range and checking equality with `LocalSourceParameter.range`.
2. It strips a raw `Group` callee to find a Lambda, then emits a Boolean that
   equates the raw Apply callee with the projected Lambda without recording the
   Group-to-inner edge.
3. It selects the Apply and restored sibling from an outer block but omits the
   outer body’s constructor, range and complete ordered child incidence.

Even after repairing these tool defects, the Rust owners do not yet provide an
equation from branded `SourceNodeKey` / `HirParameterId` / LocalSource indices
to original-model Nat `Site` / `Name`, declaration, root `Context` or ambient
event telescope. Runtime `offset + ordinal` labels and captured environments
are not that allocator. The proof handoff names this as the next original-model
frontier after a corrected executed trace; this packet establishes no universal
absence theorem about allocators elsewhere in the repository.

## Review disposition and gates

The fresh `compiler_referee` review independently verifies the three static
tool defects and confirms the handoffs do not overstate execution or proof
evidence. It accepts them only as an incomplete-probe report. The provisional
candidate must not be run unchanged or treated as source evidence. The reviewer
performed no build, test, checker or Git operation; its full read-only receipt
is in the frozen review file above.

The following remain **OPEN**: authentic extraction and universal frontend
refinement; original Simple-sub A/B; soundness; effect hygiene; principality;
progress and termination; complete Call and source/native executor
correspondence; receipt/readout/admission; whole-language coverage; and
production readiness. No compiler, HIR, parser, runtime, API, semantics,
manifest, lockfile, test source or expected output changed in r1.

The START/resource selector recommends a new, separately contracted r2 using
an isolated research package that depends on `yu-hir` and `yu-syntax` only, so
it does not compile `yu-solver`. It also requires the exact binder range,
explicit raw Group projection, and complete ordered body trace. This is a
proposal only; it grants no lease, dependency, resource, test or production
authority. Any continuation must preserve r1’s receipts and budget accounting,
freeze its own manifest/lock/dependencies before execution, and keep all parent
gates OPEN.

All r1 proof, implementation, selector and reviewer work is STOPPED. No Cargo,
Rust compiler, Lean, Lake or descendant process remains active. Legacy UNKNOWN
observations and quarantined paths remain unchanged; the user-released nine
capacity slots remain accounting-only.
