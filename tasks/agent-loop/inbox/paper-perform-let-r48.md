# R48 axiom diagnosis and failed proof repair

Status: FAILED / STOPPED. The exact choice origin was established; both allowed proof-repair builds failed at implicit predicate elaboration. Final strict audit NOT_RUN, primary verification NOT_RUN, independent review NOT_RUN. No further module edits or checker calls followed the second repair failure. R46/R47 remain FAILED and R45 remains unchanged.

## Authority, baseline and source mapping

- Worker `/root/r48_perform_let_axioms`, registered lean_prover, leaf, no descendants. Isolated checkout `/tmp/yulang-r48-perform-let-axioms`; exact baseline `334a3892c45518968cbea077a4bb0927c033d020`.
- Fixed packet: `tasks/agent-loop/sprints/paper-perform-let-axiom-repair-r48.md`. Read root AGENTS.md/base, goal-driven sprint rules, design authority, Lean skill and source/execution references, project README/toolchain/manifests, exact original manuscript passages, original R47 handoff/candidate/audit, execution typing and declaration resolver definitions, and pinned Init list/Nat/Ord plus Lean CollectAxioms sources.
- Original manuscript SHA `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`: source-owner correction :54–63, perform :318–319, request-bind and request normal-result type :340–359, frame plugging :1012–1026, original full-state/current-port/residual-graph parent :1860–1877. This bounded proof is not closure of that parent; informative corrected drafts do not add semantic authority.
- Governing Lean interfaces: `YulangClosure.PaperTypes.OperationDeclarationResolved`, `OperationDeclaration.instantiate`, `PaperComputationTyped.perform/request`, `PaperContinuationTyped.continuation`, R28 `TermSubstitutionTyped` and term substitution, R36 `PaperCoreControl.State/StackTyped/StateTyped/plug`, R45 execution/erasure/finite-prefix interfaces.
- Complete twelve source/environment hashes were recomputed before and after work and all matched. Both seeded candidate/audit hashes matched. Initial/final lists reside in the worker log.

## Actual dependency diagnosis

Call 5 exited 0. It used `Lean.collectAxioms` on every public root, then traversed actual constant bodies/types, printing every immediate choice-bearing edge. It visited 50 unique declarations. Every one of the 11 rejected roots reaches the same private helper:

`resolveOperation_iff → _private.YulangClosure.PaperPerformLetExecution.0.YulangClosure.PaperTypes.PaperPerformLetExecution.find_resolved → Nat.instTransOrd → Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le → lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le → _private.Init.Data.Ord.Basic.0.lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le._simp_1_1 → Classical.not_not → Classical.propDecidable → Classical.choice`.

`Classical.propDecidable._proof_1 → Classical.em → Classical.choose/choose_spec → Classical.indefiniteDescription → Classical.choice` is also recorded. No other direct choice-bearing dependency leaves the public resolver proof. The other ten public roots are `performStep_eq`, `performStep_arity_mismatch`, `perform_applicable`, `perform_preservation`, `evidence_preservation`, `preservation`, `trace_preservation`, `perform_through_stack`, `repeated_declarations_resolve`, `conflicting_declarations_rejected`; call 5 preserves their exact transitive edges. This is diagnosis of the successfully built frozen R47 seed, not acceptance of the repaired module.

The private helper's unrestricted Nat equality simplification introduced `Nat.instTransOrd`; the proposed proof-only repair replaces those simplifications with explicit `Nat.beq_refl` and `Nat.eq_of_beq_eq_true` witnesses. This proposal is not checker accepted.

## Failure and exact remaining repair

Call 4, the first diagnostic, failed due missing parentheses around an optional constant-body dependency array; corrected diagnostic call 5 passed. Both full raw outputs are preserved.

Call 6 failed when `Nat.eq_of_beq_eq_true (List.find?_some hf)` allowed expected-type inference to instantiate the list predicate with natural numbers. Call 7 introduced an explicitly typed Boolean equality intermediate, but that still allowed the same inference: at module :31:80 Lean expects `List.find? (BEq.beq candidate.identity) ?m = some operation`, whereas actual `hf` is `List.find? (fun entry => entry.identity == operation) operations = some candidate`. The remaining local proof repair needs explicit `p`, list/result arguments for `List.find?_some`, or an independent finite-list proof. That exact elaboration repair is unverified. Both permitted repair builds are spent; the spare literal-call slot does not authorize a third repair build. No final audit was run against stale seed artifacts.

## Fixed statements and artifacts

All 40 theorem headers (37 public, 3 private) are byte-identical through `:=` to the frozen R47 seed. Every definition, inductive, premise, quantifier and non-proof structure is unchanged. The exact delta modifies only private `find_resolved` proof terms. `R48Audit.lean` differs from the frozen R47 audit only by deleting unsupported `set_option pp.width 120`; all 37 theorem targets, kind/type/axiom checks, BEGIN/END logging and exact `{propext, Quot.sound}` whitelist remain unchanged. Static source equality checks are in the log. No claim that this revised audit executed is made.

- Candidate `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean` SHA `b70f3d35702d8ff8b28d10d850f74bcc86127b1f79c0516f7ca64a44d769bbe0` — FAILED build, not closure.
- Strict audit `.lake/R48Audit.lean` SHA `be0a8400df0f3696791f4ae4c176738fb9d38a2ee7e7a307b7a50f8df5b09c2e` — NOT_RUN.
- Diagnostic `.lake/R48DependencyAudit.lean` SHA `1f097d1095024130fc529d79c3116b06dfabae210a7d6549f8b1c5a129b57d65` — call 5 accepted, diagnostic only.
- Worker log `tasks/agent-loop/inbox/paper-perform-let-r48-worker.log` SHA `9f96f37df63b1f62491b9e2664811d1939a7896a3e7d0dcae68cc5fad37cf598`.
- Original frozen R47 candidate/audit remain unchanged with hashes `fba6990df8444daa163bdc6ec88892bde669072552ac15fef0b26eec81c8e2b7` / `8e82040c4345c8c80d73ff1006e9329ad7e6cb8963df5114b2873eb36890f5a1`.

## Process and resource receipt

All cwd `/tmp/yulang-r48-perform-let-axioms/notes/theory/lean`. Read-only `elan which lake` resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Actual Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Each exact launch records argv, cwd, UTC/monotonic start, 60-second timeout, LEAN_NUM_THREADS=1 and source hash; completion records exit, monotonic duration and full raw stream hashes. Project/direct Lean use `-j1 -M1024`.

| Call | Native Lake arguments | Exit | Monotonic seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.414978225999 |
| 2 | `env lean --version` | 0 | 0.114404202999 |
| 3 | `build +YulangClosure.PaperPerformLetExecution` | 0 | 30.777788358995 |
| 4 | `env lean -j1 -M1024 .lake/R48DependencyAudit.lean` | 1 | 1.918043660000 |
| 5 | `env lean -j1 -M1024 .lake/R48DependencyAudit.lean` | 0 | 0.414982408998 |
| 6 | `build +YulangClosure.PaperPerformLetExecution` | 1 | 0.965768980001 |
| 7 | `build +YulangClosure.PaperPerformLetExecution` | 1 | 1.066466693999 |

Literal calls 7/8; checker seconds 35.672432530992/120; no timeouts. Logged initial verification through stop 187.482 wall seconds; pre-log authority/source reads are additional, total worker runtime below 1200 seconds. Two diagnostic calls and two repair builds used; final audit NOT_RUN. No theorem type/axiom acceptance result for the repaired module exists. Bundled helper not invoked because it repeats checks and permits a broader axiom set than this packet.

- `tasks/agent-loop/inbox/paper-perform-let-r48-call-01.stdout` SHA `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`; stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-02.stdout` SHA `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`; stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-03.stdout` SHA `71618c19309fdc48c22c307b013bed9356fbbfc8413c602d8d0cb375f7494156`; stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-04.stdout` SHA `6e4a8c47aa66512875f7718b4891fa98fa5374d0cdb1817959de01905062ea0c`; stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-05.stdout` SHA `8cb695a8be7269963219fa046046e7de800e1fc4d0f153aaaab5ededae3be881`; stderr `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-06.stdout` SHA `71dc7df48264d6c5b8b6efff65366bdf1ef05e253d92018d9c5acf7488b0c026`; stderr `c4a27db198c4d8632369ee6102944ef46e83c20d685f7c17a6aaff9cfcfc710f` (corresponding `.stderr`).
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-07.stdout` SHA `c003606dfbeabb362969152d66590f9fd49df37ff4b1655a2c6b014e6b44a6cf`; stderr `c4a27db198c4d8632369ee6102944ef46e83c20d685f7c17a6aaff9cfcfc710f` (corresponding `.stderr`).

## Parent application and represented scope

Unchanged namespace `YulangClosure.PaperTypes.PaperPerformLetExecution`; bounded parent theorem `perform_through_stack` retains shared d/g/e, one declaration instance for identity/payload/response, declaration resolution and arity, arbitrary finite typed ordinary let stack, and outer final type. Request response, continuation normal result and outer final result remain distinct. The source cases and discriminators are unchanged: repeated identical declarations, conflicting declarations, arity rejection, same instance fields, R28 response insertion (0 fixed and n+1 shifted to n+2), two lets in innermost-first order, empty-owner propagation, finite-prefix typing and erasure, nonempty-owner and unsupported-body rejection. Failed proof repair prevents strict acceptance of this component.

First remaining bounded obligation: explicit predicate/result instantiation in private `find_resolved`, successful module build, then complete strict 37-target theorem type/axiom audit. Owner: primary's next bounded proof packet. Original full-state/current-port/residual-graph and source-owner bridges, general owner/handler alpha-renaming, nonempty-owner propagation, omitted constructors/frames, native/Rust correspondence, inference A/B, whole executor and production remain OPEN with their primary/source owners.

## Writes stopped

Authored only the candidate proof terms, R48 diagnostic/audit sources, exact leased worker log/call captures, dedicated isolated build artifacts, and this handoff. No root import, compiler/Rust, tests, manifests/toolchain, questions, shared task/status/index, Git or other worker writes. No descendants or pending worker-owned processes. Module/checker writes stopped; STOPPED at `2026-10-25T21:08:37.660402+00:00`. Handoff is the final worker write. Preserve failed build output and exact dependency graph for the next packet; no self-certification or integration authority claimed.
