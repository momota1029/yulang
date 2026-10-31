# R85 Amendment 01 — governing source and receipt ownership

Admitted exact proof/review reads:

- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5–7, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§1–6, SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.

The updated R85 input manifest pins these documents and the source ranges. Rust ranges now include `candidate_context.rs` 2265–2335, 2990–3095 and 3850–3895, and `lib.rs` 14272–14320. These expose source-drain completion inventories, Origin construction, and receipt attachment. The current source finding is that completion clones a receipt, flips the clone's `completed` bit and appends that clone to a separate completion vector; the Origin-attached receipt stays false. `checked_internal_use_root` requires the Origin-attached receipt to be true. The proof lane must formalize this exact producer behavior, and must check whether another admitted mutation changes the Origin receipt before concluding native root rejection.

This amendment restores the original A/B and birth-level context without changing either claim, grants only the hash-pinned reads above, and does not authorize execution or promote any theorem.
