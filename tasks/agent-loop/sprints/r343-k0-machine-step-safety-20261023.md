# Sprint R343 — K0 reachable machine-step preservation and progress

Status: frozen, revision 1.  
Branch / baseline commit: `research/simple-sub-intrusion` /
`2ddee9031fc43bb5fdf7b93424b86822de599407` (same as upstream).  
Selector: `/root/r333_selector` recommends this D3/M continuation after R342;
Luna accepts.  
Primary: `/root` (Luna).

## Parent and bounded outcome

The parent remains the user-directed full Yulang2/Simple-sub source/native
theorem and original A/B, with unchanged quantifiers, authentic source domain,
and accepted semantics. Follow the user audit
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`,
especially §§4.1, 5, 6 C/M and S, and 10.3. R341's source-typing implication
and R342's finite-return value/environment result remain bounded suppliers at
their reviewed scopes. This sprint does not assume an expression returns.

R343 targets D3: one-step preservation and progress for every reachable state
of the authentic selected-definition K0 machine. Start from an independently
typed `ValidK0(s)` root and the exact `RuntimeProgram` built from the same HIR;
retain the actual value handle, saved closure environment, whole-argument
Delay, caller environment, invocation owner, receiving view, and K0 frames.
Define a reachable typed machine-state relation independently of successful
execution. Prove that each active reachable K0 state either advances to a
state satisfying that relation or reaches the selected definition's normally
typed completion. Never use successful return as an invariant premise.

The progress statement must distinguish these outcomes:

1. `Running`: one machine step preserves reachability/typing and advances the
   small-step configuration.
2. `Completed(handle)`: the selected definition result is the exact returned
   source value and retains its source type.
3. `ResourceExhausted { steps }`: only the caller's depleted run budget; the
   machine remains live and resumable, with no partial result published.
4. `Unavailable(IdentityExhausted)`: checked finite identity exhaustion, a
   resource refusal kept separate from semantic progress.
5. Any other `Unavailable`: excluded for an authentic reachable typed K0
   state, or recorded as the first exact source-qualified counterexample / the
   precise missing invariant and owning transition.

Do not claim protection from host OOM, machine termination, or completion of
arbitrary programs. Exclude module/global/import entry, Comp formals,
operations/handlers, records/defaults, variants/case, member/operator dispatch,
local bindings, annotations and all other non-K0 cases exactly as the audit
does. The reachable ordinary K0 frame set is the selected `Root`, `Callee`,
`ValueEntry`, `ReceiverReturn`, `Condition` and binding-free
`BlockExpression`, together with `Evaluate`, `Return`, and `Stopped`; Group is
the authentic `Forward` instruction. If source inspection finds a further
authentic K0 frame, record it and include it rather than narrowing K0.

**Fixed success result:** a frozen constructive one-step invariant/progress
argument for all authentic K0 states and owners, including semantic
`Unavailable` exclusion under explicit source/runtime premises; or the exact
first owner/transition and missing supplier, with a concrete reachable
counterexample when one exists. R342's finite-return VREAL result supplies
actual returned values only at its stated boundary. It does not provide
future/result-port realization, whole M, preservation, progress, or
unavailability exclusion for this packet.

## Source correspondence and falsifiers

Primary census the exact selected-definition startup and transition owners in
`machine.rs` and K0 code/lowering in `program.rs`. Trace all K0 cases:

- literal decoding and authentic `GroundData`/`Return`;
- parameter Name resolution, lexical lookup, dispatch metadata, same handle,
  receiving-view validation and observation;
- Lambda allocation with exact formal/body/saved environment;
- Apply callee evaluation, actual handle lookup, one invocation owner,
  substituted saved environment, inert whole-argument Delay, ValueEntry bind,
  body evaluation and matching owner return;
- ordered Boolean If tests/else, Group forwarding, and binding-free block
  prefix order/discard/final result;
- selected-definition root cache/completion, machine step/run budget pause,
  and each K0-reachable error-producing guard.

The proof may reuse R336's exact finite Value preorder and independent K0
typing, R340's whole-Delay/callee/frame/owner prefix, R341's unchanged
conditional S0 result, and R342's canonical forms, `TypedEnv₀`/`EnvRep₀`,
capture, same-value binding and body-entry composition. It must state each
premise at the point used. Four independently chosen Function ports are not a
single runtime realization. A budget pause is not a semantic step or normal
completion. `candidate.unresolved().is_empty()`, graph/model existence and a
successful machine return are not typing assumptions.

Fresh reviewer falsifier: an authentic independently typed K0 trace whose
reachable evaluation or return step (a) changes the source expression/value
or captured environment represented by the runtime state, (b) loses the exact
callee/Delay/argument/owner/view relation, (c) produces a non-Boolean If test
or non-closure Apply callee without violating the D0 derivation, (d) reaches a
semantic `Unavailable`, or (e) reports completion with a mismatched selected
definition result. Separate a missing proof invariant from an executable
counterexample. Review all reachable K0 frame variants and all guards on their
transitions; no tests/builds/execution probes are review evidence.

No compiler repair is authorized by this packet. Current source lane is
`NO_SAFE_CODE_SLICE` unless the census finds a concrete source-qualified defect;
such a finding returns to Luna for an exact authority decision. Compiler
source remains read-only.

## Inputs and source pins

- User audit: `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`,
  SHA-256 `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- R336 rev4 D0/D1: `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md`, SHA-256
  `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
- R339 D3 definitions: `notes/theory/2026-10-23-r339-k0-machine-call-simulation.md`,
  SHA-256 `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666`.
- R340 proof: `notes/theory/2026-10-23-r340-k0-apply-continuation.md`, SHA-256
  `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`.
- R340 source census: `notes/theory/2026-10-23-r340-k0-machine-continuation-source-census.md`,
  SHA-256 `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`.
- R341 proof: `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`,
  SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`.
- R341 accepted outcome: `tasks/agent-loop/sprints/r341-k0-source-constraint-retention-20261023-outcome.md`,
  SHA-256 `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc`.
- R342 proof: `notes/theory/2026-10-23-r342-k0-value-environment-realization.md`,
  SHA-256 `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420`.
- R342 accepted outcome rev2:
  `tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023-outcome.md`,
  SHA-256 `93dff5d9704c747366d822eff588a348f346eaff5270a47882a03928e6e1b988`.
- R342 source census:
  `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md`, SHA-256
  `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5`.

| Read-only source owner | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

All direct inputs and source pins must match before proof dispatch. A mismatch
stops only claims depending on that pin while Luna reconciles the baseline.

## Continuing lanes, exact leases and resources

**Constructive proof:** one `prover`, requested Sol/high, 3,000 seconds, no
carryover. It owns only:

- `notes/theory/2026-10-23-r343-k0-machine-step-safety.md`
- `tasks/agent-loop/inbox/20261023-r343-k0-machine-step-prover.md`

The producer may pursue multiple related invariant/preservation/progress steps
inside the fixed K0 packet. It records the complete state relation, each
transition case, unresolved supplier and first exact obstruction, hashes both
frozen outputs, then stops. No code, tests, current state, contract, census or
other path writes; no descendants.

**Primary source lane:** Luna, up to 2,400 seconds, owns only this contract,
`notes/theory/2026-10-23-r343-k0-machine-step-source-census.md`, and
`tasks/agent-loop/current.json`. Inspect the actual runtime owners and
counterexample paths while proof proceeds. Compiler sources remain read-only.

After producer and census freeze, one fresh non-contributor
`compiler_referee` receives the exact proof, handoff, census and pins for
message-only review, up to 1,500 seconds. Review state-relation independence,
transition/frame exhaustiveness, exact value/environment/Delay/owner/view
correspondence, terminal classifications and each semantic-unavailable guard.
No tests, Cargo/builds, execution probes, Git, network, file writes or
descendants.

**Integration:** Luna, 300 seconds. Adjudicate, write the frozen outcome,
compact current state, and integrate only approved R343 paths. Unused time is
discarded. Fresh total envelope: **7,200 seconds** (proof 3,000; primary 2,400;
review 1,500; integration 300), no carryover. Three UNKNOWN legacy worker
identities remain quarantined. Do not reclaim them or exceed the six-slot cap.

## Stop and scope boundary

Stop at the frozen reviewed one-step result or the first precise
source-qualified obstruction, or at the allocated resource boundary. R343 can
close only its stated bounded D3 supplier. It cannot close full M, D3 beyond
K0, S0's independent premises, N/cache coverage, W/Z, model existence,
principality, broader source completeness, export transport, original A/B,
catalog or production. No change to expected outputs, language semantics or
production authority follows from a conditional result, test, or runtime
checkpoint.
