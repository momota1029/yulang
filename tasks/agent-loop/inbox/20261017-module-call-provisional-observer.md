# Frozen handoff: provisional module Call observer

Sprint-ID: `module-use-source-map-and-provisional-observer-20261017`
Contract revision / SHA-256: 2 / `e575fed444457c34bc229c5f10ca6510d8fb85d9e4ecc3f582f485d72952ec6e`
Assignment-ID: `/root/module_call_provisional_observer_implementation`
Handoff revision: 1
Parent gate: original Yulang inference/execution theorem, unchanged A/B claims,
quantifiers and source domain; implementation outcome is candidate-only evidence.
Exact source: `my id x = x; my answer = id 0`
Source SHA-256: `e7e69237a7162663a304493b462fbaadc787ffd38701a3d2671761aed9351fbf`
Baseline: `26ccc56f1`; current code baseline unchanged at assignment freeze
`da185f966`.

## Runtime and authorship

Role requested: Luna/high, `gpt-6-luna` / high. Observed effective model and
effort: UNKNOWN; runtime metadata was unavailable. Author: this worker only;
no descendants. Assignment cap: 360 seconds. Active-work telemetry is
unavailable, so conservatively charge the full 360-second envelope; remaining
authorized time: 0. **STOP: all writes ceased after freezing this handoff.**

## Outcome and exact changes

Outcome class: provisional candidate-source implementation. The borrowed
`CandidateSourceCall::module_callee_target()` returns a `DefId` only when the
validated callee expression itself is a direct `Name(ModuleDef(target))`.
It performs no endpoint lookup, wrapper peeling, provider/root selection,
formal inference or certificate construction. `PendingCallSupplier` now
exposes the two canonical module obligations only for such a direct module
callee, while retaining every pre-existing supplier.

The exact-source regression is authored to distinguish module `id` from formal
`x`, Integer literal `0` from a lexical Name, retain the checking occurrence
and all native ports, retain the original Call/whole-carrier/result-future and
module source/use pending obligations, and observe the existing candidate
fresh-use and nonempty `answer` export after candidate solving. A formal-callee
negative control checks that a formal `f` is not exposed as a module target
and receives neither module-specific supplier. All assertions are candidate
source evidence only; this handoff claims no original admission or execution.

Exact writes and SHA-256:

```text
crates/yu-solver/src/candidate_call.rs 2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359
crates/yu-solver/tests/research_accepted_call_vertical.rs dfc0a48087772f78e404e6f1daa6770bf5d6b4c23d88bd3f61fe967a78736162
tasks/agent-loop/inbox/20261017-module-call-provisional-observer.md (frozen handoff SHA-256 returned with receipt)
```

No scratch or generated paths. No other path was written. Exact diff: one
borrowed direct-module observer, two conditional supplier variants, and one
focused exact-source test with formal-callee negative control. No source
admission, production path, expected output, fixture, diagnostic, or inference
behavior changed.

## Reused evidence and validation boundary

Reused the frozen implementation recipe
`notes/design/2026-10-17-ordinary-call-generation-implementation-contract.md`
(`04f67087908e0658fb20dfea492c11b43979e84333d7a32ab43ad3f92b48e794`), which
maps source collection through the module-use route, candidate Apply
propagation and candidate consumers. Reused original proof
`notes/theory/2026-10-17-ordinary-call-original-generation.md`
(`bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab`) and
the new source-use map handoff: its conditional `mu*`/`b_use*` construction
leaves authentic original module syntax-to-publication/use embedding open.
Candidate `PendingDefinitionUse`, routing, fresh-use and native ports were not
treated as that original certificate. The conditional construction and this
observer close **zero** original theorem conditions.

Checks performed: inspected the leased code and frozen owner recipe/proof,
reviewed the exact diff and path scope, computed source/artifact hashes, and
`git diff --check` passed for the three leased paths.
No Cargo, build, test, formatter or executable probe was run. No test result is
claimed. After a clean independent pre-run review, the sole authorized
verification recommendation is:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

One invocation only, cap 120 seconds, no retry. A pass would establish only the
named candidate assertions.

## Open premises and next in-envelope step

The genuine source-to-constraint/propagation/consumer route is reused as prior
candidate evidence and targeted by the new regression; independent execution
is pending. The original source/use embedding remains open under
`MODULE-SOURCE-EMBED-20261017`; native interpretation of the whole copied
tuple remains open under `MODULE-NATIVE-FIELD-MAP-20261017`. Original
Gen-Call-0 membership, O0 substitution, complete Call satisfaction,
source/native adequacy, soundness, principality and termination remain open.

Provisional boundary: the observer and names are reversible candidate-only
instrumentation. Falsifiers are a non-direct/wrapped module callee being
reported as direct, a formal callee receiving module suppliers, lost source
occurrence/native ports, missing pending obligations, failed existing
candidate propagation/fresh-use/export, or any need to change another owner.
Luna owns cleanup after an authentic module-name Application producer replaces
this instrumentation, or if that rule is declined. A failure requiring source
routing/admission or another path returns to Luna; this lease cannot repair it.

Next related step: freeze these bytes for the assigned independent
compiler/source, spec, architect/API and regression reviews; only a CLEAN
pre-run regression review permits the single Cargo invocation above. This
handoff is not its own review or certification.
