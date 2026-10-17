# Operation Self source-realization sprint closeout

Sprint: `npair-operation-self-source-realization-20261018`, contract rev1 SHA-256 `66df3255cc83d18009238dc4e7e18ff4963003ebc8beb6f489f526de1f8fba19`.
Baseline: `b3a9b1739b59d8c7991b5f798e98f71f96904b19`. Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

## Original conditions and result

Original parent conditions closed: **0 → 0**. The sprint established a working-rule descriptor lemma but did not establish original semantic H0, L2's `eta`, NPAIR P3/P6, or the parent theorem. Original source domain, quantifiers, W/Z alternatives and independent F1/FK1 requirements remain unchanged.

The reviewed proof artifact ([Operation Self source field](../theory/2026-10-18-npair-operation-self-source-realization.md), SHA-256 `cc8c96d288ae5fb548acbb8437a504ee0691e86f9f8e2915ded2e67ecbca0b85`) constructs C1/C2 Self introduction and tagged descriptor elimination for the same `w`, reference, `theta` and root field. It pairs this with the authentic omitted-root native member address. Fresh independent spec review returned CLEAN within that claim. It does not derive dynamic request execution, compatibility with every original Operation tuple, or a provider-to-formal transition.

The exact field discriminator is now explicit: the Operation root Self is at `s0 = root Function.ResultEffect`; the returned Function's `[ctrl]` is a distinct `Written` contribution at `s1`; receive's formal Permission at `[Result,Result]` selects `s1`, not `s0`. The fixture contains no `f0 → receive` Apply/provider edge. Treating the root Self as the inner Permission contribution would be an invalid field move.

The implementation lane inspected the pinned native owners and returned `NO_SAFE_EVIDENCE_SLICE`. The existing compiler representation retains a whole-view Operation origin, not member-level origin; `FormalPermission` has no operational arrival consumer, and the accepted fixture never passes `f0` to `receive`. Pairing exported `f0` with that Permission would invent an edge. Fresh independent compiler/source review returned CLEAN within this bounded conclusion. No code, tests, fixtures or expected output changed; no checks or Cargo commands ran.

## Remaining premise and next packet

The missing edge is actual argument use through the returned Function field into the exact negative port. The next sprint tests the actual call-site route while preserving the original receive body:

```text
f0 → actual Apply to receive's formal f
→ f() → same returned R1 installed as g → g()
```

Dispatcher inspection found the existing receive body already contains `f() → g binding → g()`. The only missing input is the call-site `my received = receive f0`. This is one reversible addition to an existing source fixture inside the original source domain, not a change to the theorem or adopted C1/C2 rule. Acceptance is not assumed. If the normal compiler rejects it, that exact result is recorded and the fixture is restored to its pinned bytes. No compiler source, harness, tests or expected outputs are leased for edits.

The next exact owners are `candidate_source.rs` (Name/Apply/formal registration), `candidate_call.rs` (argument and Function-child comparisons), `candidate_scheme.rs` (same-value Install/FreshUse), `candidate_effect.rs` (written returned field and Permission), `candidate_context.rs` and `candidate_extrusion.rs` (FunctionPort, scopes and ordered Replay), plus the existing registration example and fixture. The next contract pins all hashes, authorizes one focused run of the already-existing `research_source_registration` example, and distinguishes run acceptance from source-level derivation of each internal edge. Matching `s1` and D in one snapshot without the actual comparison and both Replay inputs does not count.

The user-authorized C1/C2 interpretation remains a working semantic rule. Its original-domain lift/forgetting, original Operation consumer/`Prim/T` field laws, W/Z and admission/domain certificates remain open; selecting the rule does not establish them. A source-qualified compatibility failure returns for revision or rollback without narrowing the original theorem.

## Runtime and Git

Proof writer STOPPED after freezing its artifact and handoff; implementation writer STOPPED after freezing `NO_SAFE_EVIDENCE_SLICE`; both independent reviewers STOPPED with CLEAN findings. Sprint cap 2400 seconds: 1860 seconds charged (primary180, proof600, implementation720, two reviews180 each); reserve540 unspent, no rollover. Astra0.

Check run: `python3 tools/agent_sprint.py check` — STATIC CHECK PASS. This checks compact state and tooling only; it is not theorem, compiler or runtime evidence. The preceding sprint commits were `8732e2326`, `965194af1`, `9f118e8e7`, `851676eb5`, and `cd63505fc`, all pushed to `research/simple-sub-intrusion`.
