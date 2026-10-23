# R343 outcome — K0 reachable machine-step safety

**Status:** closed as a bounded research sprint after fresh independent review.
The result is accepted only for the authentic selected-definition K0 machine
and the explicit premises stated in the frozen proof. The full Yulang2 /
Simple-sub source/native theorem and original A/B goal remain unchanged.

Frozen contract rev1 SHA-256:
`e6fdba88c644fdc094ea451f83fd8ce35d87d9b513db9a99f06e5bd3aa82fa16`.
User audit SHA-256:
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

## Dispositions

- **`R343-K0-STEP` — bounded PASS.** The frozen proof gives an independent
  typed relation for intermediate machine states; its `Store₀`, `Accept`, and
  `TState₀` premises do not assume successful execution or a future return.
  Accept subsumption has the required direction and composes with D0's
  Value-subsumption rule. The proof covers all seven authentic K0 constructor
  families and six reachable frames, including the exact closure handle and
  saved environment, whole argument Delay and caller environment, invocation
  owner, view, and exact argument record at `ValueEntry` binding. Normal
  selected-root completion publishes the exact returned handle. The R342
  finite-return result is used only after the actual protected root-return
  segment exists.
- **`R343-K0-SEMANTIC-AVAILABLE` — bounded PASS.** Every `leave_owner` guard is
  supplied by the complete `ReceiverReturn` enumeration and the active
  receiver/descriptor/current-owner relation, including nested calls. Budget
  exhaustion preserves the live resumable state. Checked `IdentityExhausted`
  stops without publishing completion. Other semantic `Unavailable` outcomes
  are excluded under the proof's explicit source/runtime premises; this does
  not assert arbitrary machine termination or host-OOM protection.
- **DecodedString domain — conforms to audit §4.1.** The audit requires an
  authentic HIR form and excludes interpolation. The sole `DecodedString`
  constructor is generated interpolation text in
  `crates/yu-hir/src/module/local_source.rs:1850–1852`, owned by
  `InterpolatedString` built by `interpolated_string` at `1829–1832`.
  A non-interpolated `StringLiteral` constructs `String` directly at
  `2171–2175`. Thus the audit's conjunction admits no standalone
  `DecodedString` K0 root. This records the exact source domain without
  narrowing the audit.
- **Conditional S/D3 composition — accepted at proof §9's exact boundary.**
  Preserve the same four S0 premises,
  `ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)`, and R341's
  independent typing conclusion. Once the ordinary `RuntimeProgram` for the
  same HIR/candidate has actually been constructed and entered through
  selected-definition execution, every finite active prefix satisfies the
  accepted K0 state relation, semantic `Unavailable` remains excluded, budget
  pauses remain resumable, and any normal completion is the selected result
  at `ρ(v_s)`. This does not prove that `ρ` exists, that construction succeeds,
  or that evaluation terminates; it supplies no full native receiver/result/
  future/effect interpretation.
- **No compiler defect / no safe code slice.** The census and independent
  referee found no reachable authentic typed K0 source/runtime counterexample.
  Compiler source remained read-only; no code or expected-output changes were
  authorized or made.

## Independent review and frozen evidence

Fresh non-contributor `/root/r343_machine_step_review`
(`compiler_referee`) returned bounded PASS with no BLOCKING, major, or minor
finding and no authentic source-qualified compiler counterexample. It checked
all seven constructors, six frames, initialization, completion, transition
guards, value/environment/Delay/owner/view correspondence, and the
`DecodedString` domain. All 17 direct proof input/source pins plus the proof
and handoff hashes matched independently before and after review: 19 matches,
zero mismatches. Luna separately rechecked the audit, contract, census, proof,
handoff, and R342 outcome hashes at closeout.

The reviewer stopped at `2026-10-23 07:56:56 UTC`. Exact active time was
unavailable, so the full 1,500-second review allocation is charged
conservatively. Review was message-only and read-only. Relevant existing test
bodies were inspected only as context; no tests, Cargo, builds, execution
probes, Git, network, file writes, or descendants were used.

| R343 artifact | SHA-256 |
| --- | --- |
| Contract rev1 `tasks/agent-loop/sprints/r343-k0-machine-step-safety-20261023.md` | `e6fdba88c644fdc094ea451f83fd8ce35d87d9b513db9a99f06e5bd3aa82fa16` |
| Source census rev1 `notes/theory/2026-10-23-r343-k0-machine-step-source-census.md` | `0816397bd4e6ef493a050f95b13e3e10d90a67fe98e804e577fb33bddecfbe1a` |
| Proof rev1 `notes/theory/2026-10-23-r343-k0-machine-step-safety.md` | `e221150460d391c04a400b65cef1ca86df167685d68304bc74aab13adb907706` |
| Producer handoff rev1 `tasks/agent-loop/inbox/20261023-r343-k0-machine-step-prover.md` | `0b5d8c8d07a86adef21b60d641a0a8f36290f66613f62857c1ba2461add095e1` |

The prover stopped writing at `2026-10-23 07:50:21 UTC`; its observed wall span
was 845 seconds, exact active time UNKNOWN, so the complete 3,000-second grant
is charged. The primary source census allocation is charged at 2,400 seconds.
Review is charged at 1,500 seconds. The full 7,200-second sprint envelope is
charged conservatively at integration closeout; unused allocation is
discarded, with no carryover. Three legacy UNKNOWN worker identities remain
quarantined.

## Remaining gates

Full M, native receiver/result/future interfaces, effect and continuation
interpretation beyond this K0 step result, independent completion/future
realization, S0's unchanged four premises, N/cache, W/Z, model existence,
principality, broader source completeness, export transport, and the original
Simple-sub A/B and production gates remain **OPEN**. No audit-wide or
production claim follows from this bounded supplier.

The static `python3 tools/agent_sprint.py check` is workflow evidence only; it
is not mathematical proof or independent review. No unit tests, Cargo, builds,
or runtime probes were run.
