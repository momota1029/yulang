# r17 revision 4 — preserve fixed operation owner and separate callback realizer

Status: Luna-issued continuation of the same goal. r1/r2/r3 contracts, designs and review receipts remain frozen. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0; original quantifiers and source domain are unchanged. Baseline last observed `2a3f2a47d5013761f0e0717b0c6073c54c62d36`; local `.git` is read-only and origin unverified.

## Fixed outcome

For the proposed exact source, retain original fixed Operation contribution `c` at `u_ping`; separately derive callback-body realizer contribution `c_outer` at `u_outer`; derive complete typed Written field/license `q` owned by `c`; admit the negative callback port through `q` only; prove a typed realization `m0` relating the callback body effect to the field owned by `c` without equating the contributions; insert and propagate a versioned static field-bound consumer before runtime; then pass the same source closure through captured resumption and the live outer handler, and match its runtime receipt to the successful solver candidate.

Do not infer old `At(c,...)` or any original NPAIR closure from `c_outer` propagation. An owner/realizer bridge would need its own explicit rule and evidence. No future `d_run` is allowed as a premise to source solving.

Frozen Luna design: `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r4.md` SHA-256 `494cd5ac6ff2926eb0d55e614537e3aec6d1311a48e7bf0ecdf7129b4ee84f6b`. r3 remains immutable: design `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r3.md` SHA-256 `24f340783b0236c8fbd2ae270444b7fdcde4483f9385c99f211a4caa0db1fff1`; its review was BLOCKING on changing c from `u_ping` to `u_outer` and on underindexed q/neg0/consumer identity. r1 source/native obstruction remains frozen at artifact SHA `4147ee01443f8e89187d7fcd99d83865a1ee4458bc8146525989f6c48a01c524`, handoff SHA `4ec480644768ec3dae0212543dd9f5c2aa42b0bcbd595c2ee24843f15b753196`.

## Proof and source/API correspondence

Luna’s r4 rules must keep `c`, `c_outer`, source occurrences, native instances and runtime events distinct. `q=(c,u_ping,decl,s1,j,d_sig,d_pos,ell)` indexes the original Operation owner. `neg0` is an allowance-only port indexed by q. `m0` retains the typed callback source definition, exact response field mapping and separate lower realizer `c_outer`; it contains no runtime environment. The static solver consumer is a versioned `FieldBound_v1(owner=c,realizer=c_outer,field=q,lower,upper)` record and propagation edge, not an alias for old `ConstraintOccurrence` unless exact source/API evidence justifies that representation.

Sol proof author owns exact outputs:
- `notes/theory/2026-10-18-operation-v1-source-completion-correspondence-r4.md`
- `tasks/agent-loop/inbox/20261018-operation-v1-source-completion-r4.md`

The proof packet derives or falsifies source syntax -> complete `Sigma_theta` -> c/q/license -> exact negative allowance -> callback source type/body realizer -> actual v1 stored constraint/propagation -> successful solve -> exact closure through continuation -> saved suffix -> live outer handler -> matching runtime receipt. Inspect actual code and types in `candidate_source.rs`, `candidate_effect.rs`, `lib.rs`, `shadow_apply.rs`, `machine.rs`, `continuation.rs`; pin exact owners/slots/terms and distinguish current API from proposed v1 API. Do not use guessed slots, fake endpoints, runtime evidence during solve, family equality, or allowance-to-lower conversion. If no coherent actual consumer edge can be constructed, freeze that precise obstruction; no code lease follows.

Fresh independent spec review of frozen r4 and proof is required before any code. Conditional implementation owners only after Luna issues exact lease: solver `candidate_source.rs`/`candidate_effect.rs`, runtime `machine.rs`/optional `continuation.rs`, and additive focused tests `candidate_operation_catch.rs`, `runtime_resume.rs`. Read-only API owners are `lib.rs` and `shadow_apply.rs`; any needed wiring requires exact additional Luna lease. Preserve current behavior and expected outputs; explicit v1 entry only. A passing test/runtime does not close the original theorem or production gate.

## Lanes, falsifiers, unresolved scope

Luna owns design/integration; Sol owns constructive source correspondence and owner trace; fresh spec auditor is not a coauthor. Astra 0. First falsifier: changing `u_ping`/`u_outer` changes neither fixed owner nor evidence, or `c=c_outer` is inferred. Further falsifiers: q/neg0 omit c/source identity; no generated lower or q-indexed upper; invented occurrence/slot; `d_run` is required before solve; allowance creates lower flow; omitted type child; replaced closure/environment; altered suffix; removed/wrong outer handler; injected 42; consumer records a marker without stored propagation. Original W/Z/futures/domains/F1/FK1, whole-use transport, soundness, principality, termination, full NPAIR and production remain OPEN.

Pending preserves request/event/history/live state/ordered suffix. Running and ResourceExhausted are finite prefixes, not Diverged. This concrete source closes no original universal condition.

## Resources

Retain r17 prior charge 1,920s: Sol source audit 1,200s plus r1/r2 spec reservations 720s conservatively; actual reviewer elapsed UNKNOWN. No reset. Available continuation 2,280s is allocated once: Luna design and exact API audit 300s; Sol identity/phase proof 420s; fresh spec review 240s; conditional implementation 780s; compiler review 240s; focused runtime plus integration/state 300s. Astra 0. If design/proof fails, do not charge implementation allocation. No automatic renewal. At most one heavy runtime process and one verification owner.

Only Luna owns `current.json`, adjudication, path staging and Git. Local Git writes remain blocked; preserve all dirty workspace state and do not claim a commit/push. At closeout report original conditions actually closed (currently 0), concrete implementation/test behavior, and the next one unresolved condition.
