# Sprint R242 — Direct-Name instance closure

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Baseline: `9692008c2` (`research/simple-sub-intrusion`), after R241 partial freeze.

## Fixed parent and outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`. Preserve its shared assignment, original formals, arbitrary finite chain length, repeated calls, simultaneous entries and finite-prefix quantifiers.

Compose R239's conditional FreshUse bound admission, corrected R240 source/capture ordering and R241's authentic Apply endpoint join to discharge the direct-Name provider's per-use mapped-admission premise for the actual constructor routes they cover. For the same source provider Lambda and actual use, identify original `e_t`, `e_n`, `e_R`, each original bound, one authentic per-use map `mu_i`, every mapped physical admission/activation, and the same Apply's actual argument effect and result route. Write the resulting inequalities into parent §6. Keep incoming Module FreshUse, same-SCC internal shared-root Module, and retained Local routes separate. Preserve the parent's original quantifiers; this is one provider base case, not the forwarding induction or operational theorem.

## Proof method and falsifiers

Establish action order: registered Computation formal and `FormalNameEffect` emit both `e_t`/`e_n` directions at the exact Name; Lambda slot 4 emits body effect `<= e_R`; both drain before Lambda slot 2 exposes the positive Function. For later incoming Module use, prove source actions precede graph capture. Follow the root Function ports and reached effect rows through `Capture::expand_node/expand_row/bound`; for each required bound, show a captured exact bound or an explicitly licensed shared anchor. Map original endpoints through one authentic `FreshUse`; use R239 only after the corresponding graph bound is captured, and retain source occurrence/relation/use identity through successful physical restoration/readback. Join that same use to the actual source Apply record and R241's typed Function children/effect admissions.

For Local, separately trace publication, the retained local route, local scheme capture and its map before claiming any result. Do not substitute a Module graph or internal shared-root route. Do not identify a diagnostic flag, RelationId, endpoint equality, or route position alone with `mu_i`.

Falsify if slot 2 precedes a required source bound, a required inequality is absent from both local captured paths and licensed shared anchors, a use map merges distinct source endpoints, physical restoration/activation is missing, or the Apply argument/AE/RE/output belongs to another occurrence/interface. Keep `ReplayUseAntecedentsNotRetained` and observer correspondence gaps explicit if they block authentication. Apply no conclusion to R71/R72 without their own proof.

Success is an integrated constructor-derived per-use certificate and the parent §6 chain under its unchanged typing hypotheses, or the first exact failed source-to-use transition and falsifier. Do not promote a finite search, candidate result or one use to whole-parent closure.

## Lanes, leases and limit

Serial Luna proof/source audit; no children or Astra. Read-only: no code, tests, builds or samples. `NO_SAFE_CODE_SLICE`; no production or semantic authority. Fresh independent review is required for promotion. Resource cap 900 seconds, no carryover. Unknown legacy leases remain quarantined. Freeze on certificate/falsifier, material blocker/dependency/lease change, or budget boundary.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-direct-name-instance-closure-20261021-r242.md`
- `notes/theory/2026-10-21-r242-direct-name-instance-closure.md`
- `tasks/agent-loop/current.json`

## Direct dependency pins

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md (§§1,6–7)
d638d4c2445d575619cf4e56033ab7b1c01a972637cd5dc1f10e65419250e8cf  tasks/agent-loop/sprints/simple-sub-parent-instance-admission-20261021-r239.md
8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f  notes/theory/2026-10-21-r239-parent-instance-admission.md
11c53272e36569c0d58c3292c89a97866b8316bac8601304e2206ff6378fb959  notes/theory/2026-10-21-r240-source-instance-correspondence.md
2796242a5c1cd0917716695d7fc18359ca964b232c7c9df71a43a5821c554704  notes/theory/2026-10-21-r241-live-root-apply-correspondence.md
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
ea5c141b31db8309908b4ee1e5c5465db0a2bfdc39551c372b8124ed633e9e84  crates/yu-solver/src/candidate_call.rs
```
