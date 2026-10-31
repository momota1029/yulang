# R10 source mapping: exact R5 SourcePair supplier

## Scope and source boundary

This is a read-only mapping of the frozen R10 inputs. It does not claim that a Rust execution has occurred, that native state 21 is present, or that every reservation succeeds. The source target is the exact R5 annotation tree and ordered port inventory in `FormalPermissionAuthenticatedNativeDecode.lean`, with the four-vector and permission operations taken from `candidate_effect.rs` and `lib.rs`.

## Entry, tree order, and polarity

`CandidateSession::candidate_formal_value_pair` is entered from the formal annotation path with `Polarity::Negative` (`candidate_effect.rs`, around line 1918). The R5 tree's root is a Tuple, whose child visits retain the incoming variance. Its first child is a Function; its second child is a Tuple whose second child is another Function. Thus the Function nodes are reached at `[.element 0]` and `[.element 1, .element 1]`, both at negative variance.

For each Function, `candidate_formal_value_pair` visits the value argument, value result, effect argument, then effect result (`candidate_effect.rs`, around lines 1668–1689). The argument effect receives reversed positive variance and is omitted in R5. The result effect receives negative variance and is the corresponding concrete row (`firstRow` or `secondRow`). The frozen Lean `orderedPorts false tree` inventory states the same sequence:

1. `[.element 0, .argument]`, positive, omitted;
2. `[.element 0, .result]`, negative, `firstRow`;
3. `[.element 1, .element 1, .argument]`, positive, omitted;
4. `[.element 1, .element 1, .result]`, negative, `secondRow`.

The root Tuple row is not an Effect-port call. The omitted positive argument ports and concrete negative result ports are the only four calls in this tree.

## Per-port state transition

`candidate_formal_effect_port` handles an omitted row by calling `fresh_effect_at_level`. It handles a negative concrete row with no variables by also calling `fresh_effect_at_level`, then copying the path and concrete source IDs into a fresh local `FormalPermission`, and appending that entry with `permissions.push`. In the R5 order above, every one of the four ports allocates one effect ordinal; only ports 2 and 4 append local permission entries. Positive concrete rows follow `candidate_signature_effect` instead, but that branch is not selected by this exact tree.

`fresh_effect_at_level` takes the next ordinal from `effect_bounds.len()`, reserves one slot separately in `effect_bounds`, `effect_levels`, `effect_metadata`, and `extrusion_effect_marks`, then pushes one corresponding entry into each vector (`lib.rs`, around line 10487). Therefore, for an aligned starting state with next ordinal `n`, the successive states after the four successful port allocations have next ordinals `n+1`, `n+2`, `n+3`, and `n+4`; the final lengths of all four vectors each increase by four, with matching ordinals and levels. This describes the successful return path only. Each `reserve_typed_route_lane!` delegates to `reserve_f5b`; reservation failure maps to `IdentityExhausted` and prevents that fresh allocation from returning successfully.

The omitted ports do not append permissions. Each concrete negative result port checks `permissions.len() != permissions.capacity()`, reserves and copies its path and concrete IDs, accounts for backing bytes, and only then pushes one entry. The caller reserves local permission capacity based on annotation node count before traversal (`candidate_effect.rs`, around lines 1900–1918). The two pushes append to the existing local vector; neither replaces nor truncates prior entries. Consequently an arbitrary prefix `P` is retained and successful traversal yields `P ++ [first-row local entry, second-row local entry]`, in source visitation order. The appended entries retain their parameter, occurrence, owner, scope, path, source row and concrete IDs. Capacity, integer-size, and nested-byte checks remain success premises; this mapping does not assume those checks succeed for arbitrary machine resources.

## Completion cut and what remains conditional

After the four port calls, each Function constructs its positive and negative terms. `positive_function_term` and `negative_function_term` route through `with_term_events`, which invokes the term arena constructor and propagates constructor/resource errors. The whole formal annotation is not published until the pair has returned, endpoint links have been admitted, permission ownership has been validated, and retained permission data is transferred (`candidate_effect.rs`, around lines 1920 onward). Thus a successful `SourcePair` is the right abstraction for the four-allocation and two-entry local-delta path, but it does not establish the Rust helper outcomes, allocator availability, term-arena success, source-to-Lean recursive correspondence, or native execution. Those are still explicit helper-frame/availability and source/native bridges, as already recorded in R9.

This source handoff supports a constructive exact-tree `SourcePair` witness from an aligned abstract allocator state and an arbitrary permission prefix, provided the proof explicitly supplies the four successful allocation helper transitions and the two successful permission-copy/append transitions. It does not justify an empty helper execution, a pair-level frame oracle, or any native-state conclusion.
