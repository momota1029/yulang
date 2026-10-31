# R9 source boundary

Read-only Luna source check against the R8 diagnosis and manifest-pinned `candidate_effect.rs` source.

`candidate_effect.rs:1617–1704` visits the Function argument value first using reversed variance, then the result value using current variance, then argument effects, then result effects. The R8 proposed paired derivation and `AllocationTrace.append` order matches argument → result → argument-port → result-port. Tuple recursion retains the ordered child traversal and the nonempty/no-element-effects guard.

The repair must keep `FreshReady` / `FreshStep` availability witnesses and `HelperFrames` premises exactly as admitted. `HelperFrames` is an explicit equality abstraction, not execution of Rust helpers. Preserve the full successful-return cut at `candidate_formal_value_pair`; do not infer native State 21, permission-prefix preservation, or exact-tree `SourcePair` existence. No source implementation edits.
