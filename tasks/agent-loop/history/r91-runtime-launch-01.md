# R91 runtime launch receipt

At admission commit `760bcb7e9`, Luna dispatched the exact proof and read-only source lanes. `collaboration.spawn_agent` returned `/root/r91_formal_registration_proof` and `/root/r91_formal_registration_source`; a live roster read confirmed both `running`.

- Proof role: `lean_prover`; requested effort: high; exact leases are the R91 Lean artifact and proof handoff. Observed model/effort and process-level resource telemetry: UNKNOWN.
- Source role: `implementer`; requested routing: `gpt-6-luna` high; exact lease is the R91 source handoff. Observed model/effort and process-level resource telemetry: UNKNOWN.
- Both receive the admitted 1,400s / 1,000s lane caps. No extra worktree, environment, test, build or cache was created.
- This receipt records dispatch and the observed roster only; it does not claim either lane completed or stopped.
