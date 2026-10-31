# EFFECT-PERMISSION-DEPENDENT-COMPOSITION/20261029-r8-diagnosis outcome

Status: **CLOSED_COMPLETE as a read-only diagnosis only**. The packet produced an implementable but unexecuted proof-structure proposal. No theorem was proved, no type/axiom audit ran, and no parent or production gate closed.

The diagnosis is recorded in `tasks/agent-loop/inbox/effect-permission-dependent-composition-r8-diagnosis.md`, SHA-256 `2f6d22c337b804b8e30c49ce2dfc11501397c245d34dc5495e0435abd0b9dd2a. All 17 manifest inputs matched.

Key adjudicated findings:

- For Function composition, eliminate the argument-port output equality before obtaining the result-port decoder, so the result witness is indexed by the transported `ad.out.state`. This removes the line249 dependent rewrite motive problem at the source level; an index-free decoder projection appears unnecessary.
- For mutual recursion, use paired derivation induction with motives universally quantifying polarity, annotations, code, entry State and decoded record. Keep the context fixed and preserve argument → result → argument-port → result-port sequencing. Existing mutual `ValueEvents`/`TupleEvents` proofs provide a source-level pattern only; exact recursor binder order needs executable implementation.
- The line239 kernel mismatch is separately a polarity-index mismatch (`p✝` versus `p`) in the well-founded mutual-call wrapper's `PSum`/`PSigma` package. It is not established as fallout from the rewrite or termination failures.

The proposed route retains `FreshReady`, `FreshStep`, `HelperFrames`, tuple guards and the successful-return cut. It does not establish concrete helper execution, availability from Rust, permission-prefix preservation, exact-tree `SourcePair`, or native state. No mathematical counterexample is identified.

All original parent, native/source, helper-execution, effect-hygiene, consumer, unequal-transport, soundness, principality, termination and production gates remain OPEN. A follow-on construction must use a separate exact packet and complete successful type/axiom audit before independent review.
