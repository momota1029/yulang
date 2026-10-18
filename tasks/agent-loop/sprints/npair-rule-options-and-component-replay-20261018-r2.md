# Rev2 amendment — fixed-c rule options and replay component trace

This is a same-parent amendment to `npair-rule-options-and-component-replay-20261018.md` rev1, SHA-256 `73a869e0b1ecabf52623f8723561b0ecb222045cd38a3f7e35daa9f2eb77211e`. All rev1 authority, source pins, exact write leases, proof proposal/review, and original parent scope remain unchanged.

## Added bounded read-only trace

Rev7 implementation helper runtime is closed FAILED by the first nonzero result; commands 2 and 3 remain unrun, and no retry is authorized. The failure is `authenticate_demand_transport(...).expect(...)` at `candidate_scheme.rs:2253`, after compilation and fixture analysis. The exact identity/owner/flow field causing `None` remains unknown.

Authorize one independent `compiler_referee` read-only constructor trace, 120s, Astra0, no descendants, no writes or tests. Revalidate these pins before work:
- `crates/yu-solver/src/candidate_scheme.rs`: `9d03043a1e34b808cea18b256cb7d6d1df2a543595e8f4c72b1608e31a60784d`
- `crates/yu-solver/src/candidate_source.rs`: `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`
- `crates/yu-solver/src/candidate_call.rs`: `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`
- `crates/yu-solver/src/candidate_context.rs`: `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`
- `crates/yu-solver/src/shadow_apply.rs`: `396b288b53be76631cd0a5d748b7f19c6d3a73fc42e35001c503bed468ecc996`

Trace one actual replay row backward and forward through source Apply, module/local route, copied demand, original relation, FreshUse mapping, physical emission, Replay upper/lower and four ports. Name the first failing predicate in `authenticate_demand_transport`; distinguish a sound route rejection from an incomplete fixture/owner capture and from an overstrong test loop over unrelated replay rows. If frozen source cannot reveal the actual row's discriminant without rerunning or adding instrumentation, state exactly what is unobservable and stop. Return a message handoff with exact source equations, pin receipt and STOP; do not change checker behavior or assertion expectations.

## Resource delta

Reclassify 120s of rev7's unspent runtime grant to this read-only trace. The remaining runtime sequence remains closed, cannot be reused or retried, and its unused allocation expires. No net tranche or cumulative budget increase. All rev1 proof author/review/integration resources and implementation integration resource remain as recorded; Astra stays 0.

The original theorem and new FCW proposal statuses are unchanged. This amendment supplies diagnostic evidence only. Any fixture/checker code repair or further runtime attempt requires a fresh versioned authority packet.
