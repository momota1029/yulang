# R211 — Validation blocked before alias readback

The one authorized Cargo process exited 101 before entering the test. `test.stdout` SHA-256 is the empty-file digest `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; `test.stderr` SHA-256 is `e290fac66c0f3ec95a0e428f027a71c148ea6de11a5fef7d2c60efca29d852f2`.

The compile error is at the test-only filter in `local_source_observation.rs`: `crate::candidate_scheme::ComponentKind` is a private import. Rustc identifies the public enum as `yu_types::ComponentKind`. No alias representative, captured-bound enumeration or route-path output was produced. R211 did not retry.

The R210 evidence therefore remains the latest source observation: Effect(31) maps to Effect(32), Effect(10) is absent from the route Capture rows, and relation 71's slot-4 source bound has a completed physical emission. Whether Effect(10) aliases to a retained shared representative remains unresolved; R183 remains OPEN.
