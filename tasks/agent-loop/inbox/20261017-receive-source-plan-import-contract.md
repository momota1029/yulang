# Frozen handoff: source-qualified plan importer contract

Sprint: `receive-source-derivation-and-plan-bridge-20261017`, implementation lane under contract revision 6.  
Assignment: `receive-source-plan-import-contract`, handoff revision 4 (revision 1 hash `7e290fdf369bcc96f78003ae4d6ad2381a1349369735dabdcf190578c6bbc4c0`; revision 2 hash `d7b8a15bf7c0cba40d5c63fd48b5596bc3f9064456d3a6e9a0f4ef1c74949e13`; revision 3 hash `d8ba557b3f22540ba48bd26abf2194c76d900ac2e6edca79f12cbdeeff34f446`).  
Parent: type inference and executor with proofs; original theorem and production gates remain OPEN.  
Baseline: `6dbb6ad2511b182c1761ecea73f25640eee68899`.  
Sprint-contract SHA-256: `d274cb3f18190e08f2c1f26d911d236583aee6a5aaeda0d57a781e6c0281617b`.  
Proof artifact SHA-256: `597830364071d165c46f18175b51753521fb237b0bed67e08bec8781f24e251c`; proof handoff revision 2 SHA-256: `6d988521fa369bae56e674611cd692ea236a10d77c5c3757378a0b4555cf057a`.

## Role, exact output, and producer-to-consumer path

- Role/worker/session: `/root`, Luna/high primary, current session. Requested `gpt-6-luna` / high; observed model/effort UNKNOWN.
- Exact outputs: `notes/design/2026-10-17-receive-source-plan-import-contract.md` and this handoff only.
- Output SHA-256: `d9d7e687fb54a9013e8e2cf5524872094d69a299c39e2b1af7f563845a0a9a66`.
- Frozen direct source dependencies and hashes: sprint contract revision 6 and importer design §§2–6; proof bridge §4.2.
- Class: Draft/unapplied implementation-readiness contract. No code changes, source restriction, API decision, semantic adoption or production authority.

Current path: `prepare` returns `(Arc<HirModule>, CandidateInference)`; `execute` discards the candidate and calls `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`. `RuntimeEvidence` currently supplies only Name consumption. `from_hir` maps original local source nodes to labels and produces Lambda/Apply instructions. Lambda carries parameter, role, optional narrow RootCompSchema, body. The machine enters at `Frame::Callee`; Value entry runs the delayed argument before `ValueEntry` binds the formal; Comp entry may install RootCompSchema first. `ReceiverReturn` returns the value/view but has no complete callable Return recipe. `Frame::Local` stores a completed RHS at its actual binder; body result follows its original enclosing return. Operation native result has a declared separate consumer. Continuation templates retain existing frames and an ExecutionView, with no callable plan recipe.

Established producers: source roots/occurrences/binders/local indices, labels, syntax-derived parameter role, narrow Comp RootCompSchema and Name consumption evidence. Missing producers: original valid source `T`, EntryPlan for Value(Function), complete per-Apply ExecPlan, and two-input tagged ReturnPlan. Candidate solve and HIR do not supply these missing fields.

## Contract requirements and open owner input

Initial independent review found one major omitted correspondence: source joins also need original instance identity, scope path and shared `xi=(nu,K,D)`, not only source node IDs. It also found stale section/revision locators. Luna accepted these findings. Revision 2 retained and validates those exact references at every dependent Entry/Exec/Return/future node, rejects mismatches without reconstructing fields, and corrected locators. Later spec deltas found stale revision numbers in the design header and in this handoff's dependency line. Revision 4 sets both to contract revision 6 and provides a final combined locator check.

Proposed distinct `plan(T)` importer input, joined against exact source roots, occurrences, formal/annotation/binder IDs, roles, source slots, actual provider, maps and destination, plus the original instance, scope path and shared substitution `xi=(nu,K,D)`. `RuntimeEvidence` remains Name-evidence only. Import privately validates all joins and registered graph edges before publishing `RuntimeProgram`. It rejects missing, foreign, mismatched, conflicting duplicate or unregistered-cycle nodes; repeated references to the same registered node remain valid.

Plan lifetime is the owning `RuntimeProgram`/HIR lifetime; frames store validated node references/indices, not cloned graphs. Construction and indexes are O(nodes+edges), proportional to the original finite graph, with no family scan, solver query, recursion unfolding or execution-history duplication. Use checked counts/fallible allocation; charge memory to the program lifetime. No new arbitrary source cap is selected. Allocation/validation failure publishes no partial program/result. Exact future memory budget remains with the resource owner before code lease.

At runtime, the plan must install the actual current-carrier and callable result ports before Value-argument Force; preserve the selected callee/provider and complete execution through its original entry/body/native return/designated consumer; combine the two actual tagged Return inputs with original maps at the same Return/world; route c1 to `b_g` and c2 to the Lambda body-result destination; instantiate a future-input instruction only at its actual later producer entry. No early receipt or second local-binding receiver.

Plan execution without its source producer returns bounded unavailable before machine start; it must not infer fields from tags, solved support or shape. The current tool path remains unchanged until approved producer/importer integration. This contract cannot establish source typing, caller-context satisfaction, provider acceptance or native MODEL.

## Review request and acceptance criteria

Independent architect review of revision 1: no blocking/major finding, one minor stale locator; it also identified separate plan input/arena/frame references as candidate architecture choices. Independent spec review: one major missing instance/scope/`xi` join and stale locators. Revision 2 labels the API/arena/frame representation as candidate architecture, adds the missing joins, and corrects handoff locators to importer §§2–6 and proof §4.2. Revision 3 corrected the design header but left this handoff dependency line at sprint revision 4. Revision 4 sets both the design header and handoff dependency locator to sprint revision 6. Architect delta was CLEAN. Final spec metadata review must verify both revision references and the three current hashes; semantic content is unchanged.

Proof application remains the reviewed conditional skeleton only. The precise open source supplier premise is the independently satisfying punctured caller context for c1 (including c2) at the same original indices; native route's anchored full MODEL is also absent. Related F5, Catch and NPAIR gates remain separate OPEN work.

## Checks, budget, and stop

Static source read only at pinned `lib.rs`, `runtime/program.rs`, `runtime/receiving.rs`, `runtime/machine.rs`, `runtime/continuation.rs`; no compiler edits, tests, builds, probes or execution. Implementation-contract cap 480s; no test/execution budget. Primary stops writing at freeze and does not self-review. Parent may continue with a new exact code packet only after review, source producer/semantics authority and required user approval.
