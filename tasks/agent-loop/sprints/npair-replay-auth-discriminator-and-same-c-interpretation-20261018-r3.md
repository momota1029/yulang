# Rev3 amendment — static Replay positive-root ownership audit

This is a primary-authorized amendment to rev2 contract
`npair-replay-auth-discriminator-and-same-c-interpretation-20261018`, SHA-256
`2cf068bb099903c3f96c3a1a0a7eccb3525eb54d5de776bc1e9110f2bdadd9d4`. All
original proof scope, quantifiers, source domain, fixed `c`, semantic status,
review requirements and exact source pins remain unchanged.

## Outcome that triggered this amendment

The one post-review diagnostic command exited 101 after 19.106715464s; 3/4
tests passed. Exact row: `call=0`, child `RelationId(61)`, lower
`RelationId(58)`, upper `RelationId(35)`, `use_instance=1`, negative root term
299, output scope 32 and input 8. Module route index 0 matched; the first
reported rejection was `positive-function-node-absent` while locating the
positive function from lower-input term 310.

That label is ambiguous: `find_function` returns `None` for both zero and
multiple retained nodes. Do not infer absence, wrong row, missing capture or a
checker defect from this label alone. The runtime sequence is closed after its
first nonzero; no retry or further command is authorized by this amendment.

## One bounded read-only audit

Reclassify 120s from the unspent rev2 runtime remainder to a fresh
`compiler_referee` source-ownership audit. Exact frozen read pins:

- `candidate_scheme.rs`: `ebbfa6da533a6c90df9b34075c397ebe5dbf9a9bac991e6f853138c5df1f71ab`
- `candidate_context.rs`: `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`
- `candidate_source.rs`: `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`
- `candidate_call.rs`: `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`
- `shadow_apply.rs`: `396b288b53be76631cd0a5d748b7f19c6d3a73fc42e35001c503bed468ecc996`
- diagnostic runtime stdout: `0c2d9c47defa67f09c88342876684cb155f150609be755497ab0f3049b449e78`
- diagnostic runtime stderr: `70eea1ad69c49c58811a92c35425cff46af9ef02fcae38c1efd95691a803aeb4`
- diagnostic runtime metadata: `8e65af8f23f0959871e53ece7fa7166edb65dcfeab48eb455fdeeda0a75addbc`

Determine from actual source constructors and maps:

1. Whether route 0 contains zero, one or multiple `Node::Function` entries of
   the required polarity whose retained term maps to term 310.
2. Which original constructor owns lower relation 58 and its positive function
   ports, and whether that owner is inside the captured callee scheme or in its
   caller.
3. Whether the authentication contract legitimately requires that lower
   caller-owned function to appear in the callee graph, or whether required
   evidence should come from the relation/consumer owner instead.

Give the exact constructor and map path, the first missing source fact, and a
falsifier for each interpretation. If the frozen sources do not contain the
needed runtime census, say precisely which observation is absent and stop;
do not guess, insert the caller term into the callee graph, filter the row, or
weaken authentication.

## Boundary and resources

Audit output is a message only: no code/handoff writes, tests, Cargo,
instrumentation, runtime, Git, descendants or Astra. The previous runtime
sequence remains FAILED/CLOSED. The remaining 180s runtime allocation expires
and cannot roll over; a later verification sequence requires a new versioned
contract after an independently reviewed repair. Proof review is complete as
MINOR on an explicitly incomplete candidate; original-parent closure remains
0. The integration reserve remains 120s.
