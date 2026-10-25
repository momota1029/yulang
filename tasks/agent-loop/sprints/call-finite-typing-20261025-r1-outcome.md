# LEAN-CALL-FINITE-TYPING-20261025/r1 — outcome

Status: **ACCEPTED / CLEAN** for the exact bounded finite-prefix and conditional terminal-typing statements in the frozen contract. This does not close the original Call adequacy or inference obligations.

## Frozen result

P proves `call_state_typed_prefix_preservation`: every supplied finite `Prefix (CallControlStep md) n` preserves `CallStateTyped`, the state's result type, and its literal suffix. It includes `n = 0` and makes no successor or reachability claim.

Q proves `returned_call_state_typed` and `requested_call_state_typed` conditional on both a returned/requested head equality and `s.frames = []`. Requested continuation typing retains the response binder. Both conclusions use the state's `Original.Ty s.resultType`.

Luna's composition theorem `initial_call_prefix_terminal_typing` forms typing for the actual initial state from `TypedCall.CallTerm` and the separately typed suffix, applies P to a supplied finite prefix, then applies Q only under the endpoint's explicit empty-frame/head premises.

## Verification evidence

All 36 sprint pins were revalidated after both authors STOPPED: 12 source/configuration files, 20 reused `.olean/.ilean` files, and four author source/handoff artifacts. Three historical outcome/review/receipt pins were also independently rechecked by the fresh reviewer. No pin mismatch occurred.

Four serialized Lean invocations were used in the frozen order P, Q, composition, exact signature/axiom query. Each used `-j1 -M1024`, a 120-second timeout, exit code 0, and no timeout. Observed elapsed times were 0.206s, 0.225s, 0.227s, and 0.242s. Compilation stdout/stderr was empty. Query output was complete in the receipt; all five signatures match the contract. `call_state_typed_start`, `returned_call_state_typed`, and `requested_call_state_typed` report no axioms; P and composition report `[propext]`. This is within `[propext, Quot.sound]`.

A fresh, nonauthor `compiler_referee` independently reviewed the exact propositions, constructor use, equality directions, terminal premises, source/output pins, query, complete receipt, and scope. Verdict: **CLEAN**, with no blocking, major, or minor finding. The reviewer STOPPED before Luna adjudication.

## Artifact hashes

| Artifact | SHA-256 |
|---|---|
| Frozen contract | `dfff6b8af11651122ebc0b3be6cb6a8722b3ce7a60845eb4e82ba1a9488eee68` |
| P source | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| P handoff | `9a2e420d7fa7c19bfcf6509ad5a7fd8542abb500c08efa5ade7e4d469066a229` |
| Q source | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| Q handoff | `3b749fe6ce042a3e2c2f62c3e687fe6494778686cf73689a048faefb8d27c399` |
| Composition source | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| Query source | `63b5405da83ee2b2deb2ebfcf10bd5ee74910c931a5c3599c3f755636e5470ba` |
| Complete verification JSONL | `50a0c45503460cc166c45d5099698a1f7b8c3cd6a2cc5bd980f9386a1a86f108` |
| Independent review report | `5ad32dc61b81056348607ba8bda344fd6c117806f14bf67dbcc8ae7b268c94c4` |
| P `.olean` / `.ilean` | `a33de65647d6815ca017a570423f0818c02725b5b11e9487f68a8e2e017e5b4f` / `c72378488754c04a78ce95e0407081dadde9828a7b8cd8c03680c92b862c3573` |
| Q `.olean` / `.ilean` | `2ce15a4d3116b463b561eae036414a3093fd76bc0b9d1d5ee65b2db561fae5cd` / `69898b2f1e3ddba8884e675351d59b109accd0fb43142abf6f15578f1c5bf725` |
| Composition `.olean` / `.ilean` | `b7a78e73cfa6514255a48e5acccedd44ee8e13c57901304717a66c0b10c11101` / `035b106a76738aed9fca788f7c8814c197cbbe91f9b65300d4915e941cfbc791` |

## Preserved limits and next work

This result does not establish progress, successor coverage, terminal reachability, arbitrary endpoint emptiness, external resumption, world/effect/receipt invariants, source/native correspondence, original Call A/B, inference A/B, or production closure. The `.force (.view (.delay body) occurrence)` gap stays OPEN; r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`. Existing UNKNOWN quarantines remain unchanged.

The proof sprint is closed at its frozen scope. Further source adequacy or inference work requires a fresh dispatcher decision, accepted source inputs, new exact leases, and a new bounded sprint contract.
