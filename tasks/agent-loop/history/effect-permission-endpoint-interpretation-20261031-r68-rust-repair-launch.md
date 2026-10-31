# R68 Rust repair launch

R68 revision 1 received one BLOCKING independent finding: `InventoryOccurrenceFact` borrows `InventoryReifiedFact` from the local `reification.interpreted_facts` vector, and `internal_root_view` returns a view after that local vector is dropped.

The review is frozen at `tasks/agent-loop/inbox/effect-permission-endpoint-interpretation-r68-review.md` SHA-256 `8215a71808637f4e60f5b214e6a0cba8823e8fb61625e2a17f16952a700cd832`. Reviewer `/root/r68_review` is STOPPED / WRITES STOPPED.

A bounded R68 repair is assigned to `/root/r68_rust`, exact write leases: `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-endpoint-interpretation-r68-rust.md`. Keep the returned selected interpretation owner-safe for the full view lifetime; do not return references into the local reification Vec. Preserve exact selected fact/index/identity checks and all four raw/canonical endpoints. No semantic/routing changes. No builds, tests, Cargo, formatter, Lake, cache, target, scratch, worktree, environment, or Git. Freeze a revision-2 handoff and stop; a fresh independent delta review follows.
