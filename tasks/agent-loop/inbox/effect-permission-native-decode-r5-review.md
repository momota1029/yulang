# R5 independent review — EFFECT-PERMISSION-NATIVE-DECODE/20261029-r5

## Verdict

**ACCEPT the bounded proof repair and complete theorem audit.** No blocking,
major, or minor correctness findings. This accepts the submitted mathematical
instance only; native authenticity and the original parent gates remain open.

## Independent checks

- All 58 manifest entries, all 12 copied dependencies, target/scratch equality,
  and four raw attempt-1 receipt hashes match their frozen pins. The target is
  11,292 bytes, SHA-256
  `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`.
- The complete R4→R5 source delta is the two `/--`→`/-` delimiter changes at
  target lines 41 and 64. Definitions, theorem statements, observations,
  `encodeSource`, decoder, and bounded source domain are unchanged.
- The exact pinned isolated Lean 4.35.0 audit exited 0 with 13 theorem/type/
  axiom results. Stdout, empty stderr, status, and timing receipts match their
  hashes. Recorded wall time is 13.52s, maximum RSS 973172 KiB, with zero
  swaps or signals. Review ran no checker, build, or test command.
- Every printed theorem type matches its declaration, including arbitrary
  State/tag quantifiers, explicit `n + 1 = 22`, the nine-node inventory, four
  ordered births, retained entries, expected observations, and both parent
  applications using the same computed dependent output.
- The complete transitive axiom sets match stdout:

| Theorem | Axioms |
|---|---|
| `source_constructor_injective` | `propext` |
| `complete_source_inventory` | none |
| `complete_ordered_ports` | none |
| `code_from_exact_source` | `propext` |
| `allocation_and_decode` | `propext`, `Quot.sound` |
| `output_equations` | `propext`, `Classical.choice`, `Quot.sound` |
| `base_from_forward_allocation` | `propext` |
| `expected_observations` | none |
| `tags_and_unread_state_irrelevant` | `propext`, `Classical.choice`, `Quot.sound` |
| `first_source_port` | none |
| `second_source_port` | none |
| `extracted_instance` | `propext`, `Classical.choice`, `Quot.sound` |
| `source_coded_instance` | `propext`, `Classical.choice`, `Quot.sound` |

Static dependency-cone inspection found no holes, project axioms, or checker
bypass. The existing unused-simp warning in
`FormalPermissionSourceOrigin.lean:172` does not affect this repair.

## Source and observation boundary

`candidate_effect.rs:1639–1691` visits ordered tuple children and Function
argument/result values before argument/result ports; lines 1694–1744 allocate
omitted and negative concrete ports once each. `lib.rs:10487–10517` returns
the pre-push ordinal. The source handoff and R3 observation support bounded
births 21, 22, 23, 24 without asserting a native global initial State. The
explicit `encodeSource` projection preserves the fixed Int/Unit/Function/Tuple
input; root and bare tuple rows stay in the inventory and make no Effect-port
call.

The raw R3 observation matches metadata, paths, operands `[1]`/`[2]`, rows
22/24, capture 4, root 0, and negative exported nodes/returned ports 17/14.
Tags and the other seven model State coordinates cannot affect retained
entries or expected observations, though shapes may vary. No theorem proves
equality with an actual native State or authentic native execution.

Source/native authenticity, original A/B obligations, effect hygiene,
consumer residual, unequal transport, soundness, principality, termination,
and production remain **OPEN**. Review was read-only; no files were changed by
the reviewer.
