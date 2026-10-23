# Sprint R344 — K0 Call same-witness interface interpretation

Status: frozen, revision 1.
Branch / baseline commit: `research/simple-sub-intrusion` /
`5baf93fc64930b2b54fd13b40576985f8ec3db00` (same as upstream).
Selector: `/root/r333_selector` recommends this C/M seam after R343.
Primary: `/root` (Luna).

## Parent and bounded outcome

The parent remains the unchanged user-directed full Yulang2/Simple-sub
source/native theorem and original A/B, with their original quantifiers,
authentic source domain and semantics. Follow the user audit
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`,
especially §§4.2, 5, 6 C/M and S, and 10.3. This is a new 7,200-second
envelope. R343's unused time does not carry over.

R344 targets the audit's same-witness Call interface in ordinary authentic
K0, at selected-definition entry. Relate one authentic source Apply and its
independently typed derivation to the native Function demand using the exact
four-port order `(argument value, argument effect, return effect, return
value)`. Construct one joint interpretation that retains, together:

- the native Function demand and all four ports under one solution `ρ`;
- the actual callee value handle and the closure's saved environment;
- the entire argument `Delay`, including its caller environment;
- the invocation and owner chain, actual received value and receiving view;
- the source result, normal-return value, and result/future/effect obligations
  for that same call and witness.

Prove the forward call-prefix connection after an actual callee return reaches
entry, and the audit's reverse connection from a correctly interpreted native
Function demand to the K0-permitted actual Value entry. For an actual normal
return, relate the same witness to the selected result and its future/effect
interface. Preserve divergence and budget pause; neither call termination nor
future return may be a premise or conclusion. Use R340, R342 and R343 only at
their reviewed boundaries: continuation/whole-Delay identity, finite actual
return and environment/capture, and typed reachable-machine-step safety.

**Fixed success result:** either (a) a frozen constructive same-witness K0
Call/interface argument for these directions under plainly stated existing
premises, or (b) the first precise missing premise/owner/transition with a
concrete authentic counterexample only if one is established. Distinguish an
unproved supplier from a source-qualified counterexample. Four separately
chosen port witnesses, `candidate.unresolved().is_empty()`, model existence,
successful return, or termination cannot substitute for the joint relation.

Keep the scope at ordinary selected-definition K0 and actual Value entry.
Comp entry, operations/handlers, foreign continuations, non-K0 source, module
admission, whole-module execution, solver termination, recursive model
existence and export transport are outside this packet. Do not add semantic
assumptions to S0 or weaken original A/B. Full M remains open unless its
independent native receiver/result/future/effect interpretation is actually
supplied. No compiler repair, tests, build or expected-output change is
authorized; source lane is `NO_SAFE_CODE_SLICE` unless a concrete
source-qualified defect is found, in which case Luna records it without
editing code.

## Inputs and source pins

| Frozen input | SHA-256 |
| --- | --- |
| Audit `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R336 rev4 D0/D1 | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R339 D3 definitions | `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666` |
| R340 Apply continuation proof | `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737` |
| R340 source census, corrected rev | `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078` |
| R341 source-typing proof | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` |
| R341 accepted outcome | `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc` |
| R342 value/environment proof | `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420` |
| R342 accepted outcome rev2 | `93dff5d9704c747366d822eff588a348f346eaff5270a47882a03928e6e1b988` |
| R342 source census | `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5` |
| R343 machine-step proof | `e221150460d391c04a400b65cef1ca86df167685d68304bc74aab13adb907706` |
| R343 accepted outcome | `d411262307cc2a578ed1295091958bbc0a3a0ab23a85d706f49ec1395f70f0a9` |
| R343 source census | `0816397bd4e6ef493a050f95b13e3e10d90a67fe98e804e577fb33bddecfbe1a` |

| Read-only source owner at baseline | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

All pins were checked against the frozen baseline before proof dispatch.

## Lanes, exact leases and resources

**Constructive proof — one `prover`, requested Sol/high, 3,000 seconds, no
carryover.** Exact write leases:

- `notes/theory/2026-10-23-r344-k0-call-interface.md`
- `tasks/agent-loop/inbox/20261023-r344-k0-call-interface-prover.md`

The prover may develop related joint-interpretation lemmas within this K0
packet, state each reused premise at its use, freeze either the bounded bridge
or the first exact obstruction, hash both outputs, then stop. No code, tests,
current state, contract, census, unrelated path, or descendants.

**Primary source lane — Luna, up to 2,400 seconds.** Exact write leases:

- this contract;
- `notes/theory/2026-10-23-r344-k0-call-interface-source-census.md`;
- `tasks/agent-loop/sprints/r344-k0-call-interface-20261023-outcome.md`;
- `tasks/agent-loop/current.json`.

Trace source Apply, native port construction and unresolved suppliers to the
actual runtime handle/closure/Delay/owner/view/result/effect paths. Keep code
read-only and record falsifiers and any missing interface supplier.

After the proof and census freeze, one fresh non-contributor
`compiler_referee` gets the exact frozen artifacts and pins for message-only
review, up to 1,500 seconds. Review both call directions, joint witness
identity, all four ports, the actual closure/capture/Delay/owner/view, normal
return/future/effect interpretation, and circularity/termination. No tests,
Cargo/builds, execution probes, Git, network, writes or descendants.

**Integration — Luna, 300 seconds.** Adjudicate, write the bounded outcome,
compact current state and integrate only approved R344 paths. Fresh total
envelope **7,200 seconds** (proof 3,000; primary 2,400; review 1,500;
integration 300), no carryover. No Astra assignment. Preserve and quarantine
the three UNKNOWN legacy worker identities; do not reclaim them or exceed the
six-slot cap.

## Stop boundary

Stop at the reviewed bounded joint-witness result or the first exact
source-qualified obstruction, or at the allocated resource limit. This packet
cannot close full M/C, F1/FK1, Comp/foreign-continuation semantics, solver
termination, W/Z, N/cache, principality, source completeness, original A/B,
catalog or production. No whole-theorem promotion follows from a local
supplier or a green test.
