# R340 — Authentic Apply handoff and continuation preservation

**Revision 1. Status: ACTIVE.** Fresh sprint after R339 closeout; no R339
budget or authority carries over. Luna `/root` owns this contract, primary
source census, current state, review adjudication and Git integration.

## Parent claim and governing authority

The unchanged parent is the full Yulang2/Simple-sub source/native A/B theorem,
catalog and implementation correspondence. Follow the user-directed audit
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
The immediate claim is audit §6 C: an authentic K0 source `Apply f a` and a
reachable typed runtime configuration must correspond through the actual
callee, whole argument, invocation and Value-entry prefix. Keep the audit's
original `ValidK0`, independent source typing and runtime realization. Do not
assume termination or successful execution to define realization.

R339 is closed with D2 PASS only for its actual `candidate_replay_bound` child
family and D3 OPEN / MAJOR. The R339 reviewer found that its D3 configuration
`Evaluate(k_f, ηcaller)` has no stack, call-site or owner relation, while the
proof consumes the `Callee` frame installed by the preceding authentic Apply.
Preserve, without editing, the reviewed D3 note at SHA-256
`4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666` and R339
outcome receipt at SHA-256
`07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701`.
R338 admission-delta review remains OPEN / incomplete and is independent of
this sprint.

## Bounded outcome

Prove or precisely refute the missing source Apply-to-machine continuation
bridge. Define a typed configuration/continuation relation that retains the
actual source Apply identity, lowered child labels, call site, caller
environment, stack prefix `κ`, current owner, and relevant source/runtime
value/environment relation.

The required chain is:

1. From an authentic source Apply configuration
   `Evaluate(k_apply, ηcaller), κ, owner ω`, derive the actual machine step to
   `Evaluate(k_f, ηcaller), κ · Callee(k_a, ηcaller, site)` with the exact
   lowered children, site and whole argument.
2. By induction over actual reachable K0 machine transitions above this
   distinguished prefix, preserve the same waiting Callee frame and stack
   prefix through the callee-evaluation segment. Nested invocations may change
   the current owner; prove stack/owner coherence and restoration to `ω` at
   this segment's matching return. A divergence or budget pause need not return.
3. Reapply the R339 handle-based transition trace at the actual return. Under
   its explicit Value-closure realization premise, derive the exact
   `ExecutableValue::Closure` lookup, whole
   `Delay { code: k_a, environment: ηcaller }`, fresh activation with previous
   owner `ω`, and
   `κ · ReceiverReturn(activation, ω) · ValueEntry(parameter, body, ηc')`
   for that same handle, binder, body and saved closure environment.
4. Apply the same prefix invariant to the conditional argument-return segment.
   On return, show the actual received value is bound to that exact parameter
   in `ηc'` and evaluation begins at that exact body, with the matching
   ReceiverReturn retained below it.

Success repairs only R339's missing continuation premise for this stated
conditional prefix. Canonical-form/ValueReal adequacy from source typing,
capture-environment substitution transport, full argument/body preservation,
normal return, the rest of M, progress, S0 and production remain separate
OPEN suppliers. If one supplier is needed, state it exactly; do not strengthen
the input and call the original obligation closed.

**Method:** continuation-parametric induction over the actual K0 machine
transition relation with a distinguished stack prefix, using each frame push,
pop and owner transition at its source owner. A finite-state model that assumes
the transition facts is not source correspondence. No termination argument is
required.

**Falsifier:** an authentic reachable K0 trace replaces, consumes or changes
the waiting Callee frame/payload before the matching return; fails to restore
the saved caller owner at that boundary; or enters with a different closure
handle, argument code/environment, activation, binder or body.

## Exact lanes, writes and review seam

**Constructive proof lane** — requested role `prover`, default Sol/high,
maximum 1,200 seconds. It owns only:

- `notes/theory/2026-10-23-r340-k0-apply-continuation.md`
- `tasks/agent-loop/inbox/20261023-r340-k0-continuation-prover.md`

**Primary source lane** — `/root`, maximum 1,500 seconds. It owns only this
contract, `tasks/agent-loop/current.json`, and
`notes/theory/2026-10-23-r340-k0-machine-continuation-source-census.md`.
Record the actual Apply lowering, transition/frame pushes and pops, owner-stack
updates/restoration, child/binder/body identity and exact source hashes. This
is source evidence, not a self-review of the proof.

**Implementation lane:** `NO_SAFE_CODE_SLICE`. R339 found a missing proof
premise, not a compiler defect. Runtime/HIR/compiler code and tests remain
read-only.

After both outputs freeze, Luna assigns one fresh non-contributor
`compiler_referee`, requested Sol/medium, maximum 600 seconds, to review the
frozen source census and proof together against this contract and audit §6 C.
Require separate dispositions for authentic Apply-to-Callee creation,
callee-segment stack/owner preservation, invocation/Delay/ValueEntry identity,
and the argument-return boundary. Any accepted major finding remains OPEN;
no same-byte repair or new review cycle is assumed by this sprint.

## Baseline and direct dependencies

- Branch `research/simple-sub-intrusion`; HEAD and upstream at start:
  `e801dfa604c1e6e0b1ba5760d589fc0e77526406`.
- User audit:
  `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- R339 rev2 contract:
  `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00`.
- R339 D3 note and outcome are pinned above. The rev2 contract contains the
  inherited R336–R338 contract/proof/review/census pins; reuse only within
  their reviewed premises.
- `tools/inference-playground/src/runtime/program.rs`:
  `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0`.
- `tools/inference-playground/src/runtime/machine.rs`:
  `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840`.
- `tools/inference-playground/src/runtime/dispatch.rs`:
  `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873`.
- `tools/inference-playground/src/runtime/receiving.rs`:
  `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551`.
- Inherited literal mapping pin:
  `tools/inference-playground/src/runtime/literal.rs`,
  `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f`.

Recheck exact pins before adjudication. Extend the manifest only for an
additional source owner actually reached by the proof, with reason and hash.
The user audit remains untracked and must never be staged.

## Resources and stop conditions

Fresh cap **3,600 seconds total**: proof 1,200 + primary source lane 1,500 +
fresh review 600 + integration/state sync 300. No Astra, no carryover, no
renewal and no second heavy process. Charge grants conservatively when issued;
discard unused time. Preserve the three legacy `UNKNOWN` quarantined identities
and their reservations. Selector proposals grant no leases; Luna grants only
the exact paths above.

Stop the bounded packet on any source/input hash mismatch, unknown writer that
overlaps a leased path, source-qualified counterexample, resource cap or user
STOP. Consult the selector on a substantive counterexample/missing owner,
dependency/lease change, coherent frozen review seam or cap. No code edits,
tests, Cargo/builds, probes, descendants, external contact or worker Git.
Root owns exact-path staging, commit and non-forced push after adjudication and
integration. No D3/M, D5/S0, full N/W/Z, principality, original A/B, catalog or
production gate closes automatically.
