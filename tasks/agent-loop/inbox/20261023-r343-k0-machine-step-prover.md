# R343-K0-MACHINE-STEP — frozen assignment handoff

Handoff ID: `R343-K0-MACHINE-STEP-PROVER`; revision **1**, immutable on
submission. Outcome class: **candidate mathematics and source/native evidence**.
Fresh independent review and Luna adjudication remain required.

## Contract, parent and inputs

Sprint R343; contract revision 1:
`tasks/agent-loop/sprints/r343-k0-machine-step-safety-20261023.md`, SHA-256
`e6fdba88c644fdc094ea451f83fd8ce35d87d9b513db9a99f06e5bd3aa82fa16`.
Baseline supplied by Luna: `research/simple-sub-intrusion` commit
`2ddee9031fc43bb5fdf7b93424b86822de599407`; no Git command used.

Parent: unchanged user-directed full Yulang2/Simple-sub source/native A/B,
audit §§4.1, 5, 6 C/M and S, 10.3, audit SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
Bounded target: reachable typed K0 machine-state preservation/progress and
semantic Unavailable exclusion, starting from an independent D0 root typing
and the exact same-source ordinary selected-definition RuntimeProgram.

Direct dependency hashes and provenance are fully enumerated in proof §2:
R336 rev4 `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`;
R339 D3 `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666`;
R340 proof `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`;
R340 final census `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`;
R341 proof `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`;
R341 accepted outcome `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc`;
R342 proof `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420`;
R342 accepted outcome rev2 `93dff5d9704c747366d822eff588a348f346eaff5270a47882a03928e6e1b988`;
R342 census `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5`;
R343 primary census `0816397bd4e6ef493a050f95b13e3e10d90a67fe98e804e577fb33bddecfbe1a`.
The five pinned runtime source hashes also matched; exact values are in §2.
Contract/census/runtime pins matched again at the proof freeze.

## Actual candidate result and parent application

Proof:
`notes/theory/2026-10-23-r343-k0-machine-step-safety.md`, revision 1, SHA-256
**`e221150460d391c04a400b65cef1ca86df167685d68304bc74aab13adb907706`**.

The proof constructs `TState₀` independently of execution success: authentic
source derivation and lexical realization for the current Eval; independent
source TypedVal/RecvReal for Return; a typed continuation whose erasure is
the entire actual stack, including selected Root; valid append-only storage;
and the complete ReceiverReturn/active-owner chain. Each call retains its
actual callee handle, exact captured environment, whole argument Delay and
caller environment, formal/body, receiving view, actual invocation and source
labels. Argument/body phases do not assume a future return.

Induction on actual step count covers every K0 source form and all six
reachable frames: Root, Callee, ValueEntry, ReceiverReturn, Condition and
BlockExpression. CodeReal/lexical storage supplies the reference/binding/view
guards; R342's independent canonical-form lemmas exclude nonclosure Apply
and non-Bool tests; the entire owner chain supplies every leave_owner guard.
The only checked reachable refusal is new_invocation's IdentityExhausted.
No concrete source-qualified counterexample or missing local supplier was
found by this producer.

Running preserves the certificate. Completed publishes the actual selected
cache handle at the independent root type; accepted R342 finite-return is
used only after the actual matching root Return exists to identify the same
source result. ResourceExhausted is an unchanged live caller-budget pause,
including budget zero, and is resumable. IdentityExhausted is stopped,
nonpublishing checked resource refusal, without rollback/resumability claims.
Every other Unavailable is excluded under the explicit same-source/runtime
premises. No termination or host-OOM protection is claimed.

Apply to parent now: R341's unchanged four S0 premises supply the independent
root derivation. Given the same constructed selected-definition P, instantiate
the candidate TState₀ theorem to obtain finite-prefix K0 machine safety and
normally typed selected completion. This composition neither assumes a
successful return nor supplies native-model existence. Full M's native
receiver/result/future/effect/continuation interpretation, independent F1/FK1
and foreign continuations, N/cache beyond accepted families, W/Z, recursive
models, broader source completeness, export transport, principality, original
A/B/catalog and production remain OPEN.

## Source/native path and prior work

Actual path: authentic HIR child/formal/occurrence constructors in program.rs
-> independent D0 typing (or accepted R341 source constraints/retention/row
transport under the original four premises) -> same Program CodeReal labels
-> Evaluate/Return and exact frame payloads in machine.rs -> handle-keyed
closure/whole-Delay/ValueEntry bind/owner return -> selected Root cache and
complete_selected_definition. No native constraint operation is bypassed or
changed. Native Function ports remain one four-port inequality tied to the
same actual closure witness; result/future native interpretation is separate.

Reused at their actual scopes: R336 finite algebra/D0/subsumption; R340 actual
Apply and protected stack/owner; R341 conditional S0; R342 independent
canonical forms, captures, lexical same-value binding and actual finite-root
return identification. R339's trace is guidance, not an adequacy/progress
supplier. Rejected shortcuts: inferred output-shape typing, machine success,
empty unresolved, four separately chosen Function witnesses, provider-site
closure identity, erased caller/capture distinction, assumed dispatch
idempotence and one local frame action as a foreign-continuation theorem.

## TODOs, ownership and exact falsifiers

`R343-STEP-REVIEW-1`, Luna: consume this frozen proof/census with one fresh
non-contributor reviewer under the existing contract. Falsifier is an authentic
independently typed selected K0 prefix whose CodeReal/EnvReal/RecvReal,
call/capture/whole-Delay/owner/view correspondence, guard exclusion or selected
completion fails. Proof §§4–7 identify each responsible source symbol/guard.
No additional producer review appointment or self-certification is made.

`R343-M-REST-1`, Luna plus the audit C/M suppliers retained in R342-M-REST:
after adjudication, apply the accepted step supplier and allocate the exact
native receiver/result/future-interface/effect premise separately. Required
input: original Function/Call meaning with its independent quantifiers;
falsifier: authentic same-provider Call satisfying that premise without the
required same-result/future/effect witness. New leases/dependencies require
Luna. No local missing supplier is silently transferred into this result.

Implementation: **NO_SAFE_CODE_SLICE**. Actual Machine evaluation/return,
invocation/owner/root, RuntimeProgram lowering/entry, Receiving, dispatch and
literal owners were inspected read-only. No concrete typed K0 defect was
identified; no provisional production edit is requested or authorized.

## Runtime, checks, resources and writer stop

Role/actual worker: prover `/root/r343_k0_machine_step_prover`.
Task receipt: primary's NEW_TASK granting these two paths and 3,000 seconds.
Requested model/effort: `gpt-6.1-sol` / `high`.
Observed effective model/effort: **UNKNOWN / UNKNOWN**; no metadata attests
them. Own runtime session/launch timestamp: UNKNOWN. Containing primary
session is `4a30d8bc-cf58-442a-ac35-a6026b4e35b5`, not claimed as child session.
No model-switch claim, children or contributing descendants.

First observed clock: `2026-10-23 07:36:16 UTC`.
Final handoff/write-stop clock sample: **`2026-10-23 07:50:21 UTC`**, immediately before
the final handoff write. Exact subsecond cessation and active CPU/model time
are UNKNOWN. The observed elapsed span is below the 3,000-second total grant;
conservatively retain the full reservation charge if Luna lacks a complete
launch/active-time receipt. No carryover, renewal or budget expansion.

Checks: source/authority inspection, direct SHA-256 matching and manual
constructor/frame/guard proof coverage. No tests, builds/Cargo, probes,
network, Git, central records, compiler/tests/expectation/config/tool edits,
nested CLI, or external/other-worker contact. These checks do not certify
the mathematics independently.

Exact leased/new paths: the proof above and this inbox only. No scratch
paths; no unresolved descendant leases. Worker state: **STOPPED WRITING**
after this final write; both revision-1 artifacts are FROZEN. Only read-only
hashing follows. The inbox's own SHA-256 is returned in the final message;
it is not embedded in itself. No worker activity continues while awaiting
review. Next step belongs to Luna: exact frozen intake and fresh independent
review, then adjudication/integration. Commit-ready status: **pending review**;
the parent remains OPEN.
