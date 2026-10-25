# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r26 — mapOperation transport repair

Status: CANDIDATE; no worker edits or checker calls before exact hash, fresh Astra runtime receipt, exact leases and committed acknowledgement. This follows the user's explicit requirement that proof and review subagents use Astra.
Branch: research/simple-sub-intrusion
Baseline: 036e97ef905a50bcd6a5257709ee8f6d1228ff1e (R25 adjudicated FAILED_CHECK)
Contract revision: r1

## Parent, evidence and bounded outcome

The unchanged parent remains the original full-paper simultaneous type-substitution theorem at `docs/yulang-operational-type-safety-ja.tex:953–977`, followed by inference/executor semantics and original A/B obligations. R24 remains an accepted prerequisite for separate operation-adapter typing. R25 was a source-grounded candidate but its first focused build failed at `PaperExecutionTypingSubstitution.lean:471`; no proof or source counterexample was established. Its isolated worktree and partial cache stay frozen.

R26 targets that exact constructor-inference mismatch. The frozen R25 mapOperation constructor and iff shape are inputs. In the new isolated worktree, make the substitution branch instantiate the constructor with mapped instances explicitly (`source := source.subst σ`, `target := target.subst σ`, and mapped declaration/witness indices), fixing body, adapter and unchanged result-type indices to the actual mapped judgments. Then connect the resulting derivation to `mapPaperComputation`/`mapMapperPlan`. Do not change the mapOperation typing rule, contexts, adapter directions, operation declaration/witness identity, six public transport theorem types, or arbitrary-σ scope.

Success requires the focused build, exact inversion and iff, all six unchanged transport theorem statements, the R24 mapper relation/transport/polarity results, complete axiom audits with no `sorryAx` or project axiom, and fresh non-author M1 review. The failed R25 candidate is not evidence for any theorem until the new dependency cone passes.

Falsifiers: explicit mapped indices still fail to align; adapter contexts or operation identities change; result type changes; any public transport statement or arbitrary-σ scope narrows; failed declaration/axiom dependency; or mismatch with manuscript `:694–719`, `:1024`, `:1109`. Stop at the first ambiguity or failed check; no repair/retry within this packet.

R26 does not prove one-step execution preservation, request/frame/continuation composition, response plugging/freshening, term substitution, R23 or R18, full inference/executor, A/B, source/native/Rust or production readiness. No implementation change; `NO_SAFE_CODE_SLICE` remains.

## Frozen inputs

    docs/yulang-operational-type-safety-ja.tex a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
    notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean eec31d92375ea700061ff6b0a8c5ac7742db5fe77aa96dd28bc75ad7c93fc2dd (frozen R25 candidate; primary seeds the isolated checkout)
    notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean 6e8c1b8d1cf62736d6df172430bf20e44d35b6d527d468b07dc80ebe7ce736f3 (frozen R25 failed candidate; worker may repair only the mapped constructor application)
    notes/theory/lean/YulangClosure/PaperMapOperationIntegration.lean 98e78766e2d2671d6d4aae6250fbe001c3eb8e9825df1aac62e5c97efcf1851f (frozen R25 candidate; worker may repair only integration proofs if the focused build exposes an in-scope mismatch)
    notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
    notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean 175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77
    tasks/agent-loop/inbox/paper-typing-subst-r25-adjudication.md efc475c8ebfd3e4ce5fcdfd4c06f2cb092b519ebfebd311d4c9a14d9e947e1e4
    tasks/agent-loop/inbox/paper-typing-subst-r25.md d31aff1170c0219c851c349c420a788a4a941071a38cf6182bf21e69eca54056
    tasks/agent-loop/inbox/paper-typing-subst-r25-worker-checks.txt 0da3d9820e2d635b7ab7fe7dbfb076491dfeabcc9ac7829da636ff7292a52a92

The primary revalidates every listed hash and the R24/baseline dependencies in `/tmp/yulang-r26-mapop` before acknowledging launch. Seed the three frozen R25 candidate sources into a fresh checkout at the exact baseline commit; never touch `/tmp/yulang-r25-mapop` or reuse its partial cache.

## Exact leases and sequential lanes

Only after a fresh Astra worker/session receipt, reconciled capacity, exact hash verification and committed acknowledgement, one `astra_prover` at medium effort may write in `/tmp/yulang-r26-mapop`:

- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` (repair only the mapped constructor application and any direct premises needed by that case)
- `notes/theory/lean/YulangClosure/PaperMapOperationIntegration.lean` (only if the focused build shows an in-scope proof mismatch)
- `notes/theory/lean/.lake/R26Audit.lean`
- `notes/theory/lean/.lake/build` (dedicated cache; worker sole owner during construction, then stops and hands it to primary)
- `tasks/agent-loop/inbox/paper-typing-subst-r26-worker-checks.txt`
- `tasks/agent-loop/inbox/paper-typing-subst-r26.md`

`PaperExecutionSyntax.lean` is a primary-seeded frozen R25 input and read-only for the worker. R24, the paper and all other dependencies are read-only. The worker source-audits the exact mismatch and indices first, then may construct and check the repair. No child agents and no Git operations.

The worker is sole checker/cache owner during construction, with at most 6 serial invocations and 100 shared checker seconds. If the focused build passes, the worker writes an exact audit file and runs its audit; then freezes the artifact/log/handoff and sends an actual writes-stopped receipt. After that receipt only, the primary owns the exact cache and `tasks/agent-loop/inbox/paper-typing-subst-r26-primary-verification.txt` for the final focused build and final audit (2 invocations). Commands, serially:

    lake build +YulangClosure.PaperMapOperationIntegration
    lake env lean -j1 -M1024 .lake/R26Audit.lean

One heavy build at a time, pinned Lean 4.35.0, `LEAN_NUM_THREADS=1`, Lean `-j1 -M1024`; Lake build uses the lakefile's existing `moreLeanArgs`. Failed calls count. First failed check stops all checking, including primary verification; no retries or budget transfer.

After freeze, one fresh non-author `astra_prover` M1 reviewer at medium effort may write `tasks/agent-loop/inbox/paper-typing-subst-r26-review.md`; the reviewer runs no checker and does not overlap worker/cache ownership. The proof author must have a confirmed writes-stopped receipt before the reviewer starts. Proof and review Astra assignments are sequential and together consume at most 300 seconds aggregate Astra time and three substantive stages; record requested and observed model/effort separately. If that envelope or the global one-Astra-at-a-time quota cannot be met, do not start either assignment.

## Resource and stop contract

Envelope: 1200 active seconds, 8 literal serial Lean/Lake invocations total, 120 checker seconds; worker cap 6 and primary reserves 2; one heavy build at a time. R25's unused budget is not transferred. Version queries count if used. No tests, default/full build, Rust build, network/dependency activity or shared/generated cache reuse. Current state retains 8 UNKNOWN reservations, including prior Astra-role rows; R26 remains CANDIDATE until those reservations and the one-Astra quota are reconciled. The user-requested Astra route does not release their quarantined leases. Stop at source ambiguity, first failed check, budget edge, authority/dependency/lease change, STOP or session end. Preserve R25 as FAILED_CHECK; R23/R18 and all original parent gates remain OPEN.
