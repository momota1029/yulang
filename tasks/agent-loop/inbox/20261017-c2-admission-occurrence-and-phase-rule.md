# c2 native call occurrence correction — source handoff

Sprint-ID / contract revision / SHA-256: `c2-typed-call-occurrence-correction-20261017` / 2 / `56dfb9a7eec800088341b99d659b9fcabacedbe969f8891b31f1784cd166f54e`  
Assignment-ID / handoff revision: `C2-TYPED-CALL-OCCURRENCE-CORRECTION-20261017` / 2  
Parent: original FORWARD-FIRST-CALL A/B and c2 admission/VIEW/CHECK remain OPEN  
Baseline: `8f012935e`; no semantic/code adoption  
Author / worker: `/root`, Luna primary and sole Git integrator; current session  
Requested model/effort: `gpt-6-luna / high`; observed effective settings: UNKNOWN  
Launch: 2026-10-17 04:09:16 UTC; STOP/freeze: 2026-10-17 04:11:51 UTC; 155 seconds active

## Frozen source outcome

Class: corrected typed source/native call-use correspondence; no admission proposal.  
Artifact: `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md`  
Artifact SHA-256: `a78c3b32db064e3e6add46daeb7395703fe453fb6aba74ba9d98ce82ed409d25`

The revision withdraws rev1's `Aarg_c2^cand := Unit+ <= arg(N2)` and
`C-AppArg` admission claim. The native Apply constructor embeds the actual
argument endpoint as the positive argument child of the negative Function
Demand, then constrains the positive callee against that negative Demand at
c2 checking slot 0:

```text
callee2+ <= N2-
```

The source observer authenticates the same `LocalSourceForm::Apply`, exact
callee and argument child identities, c2 occurrence/cause, and the native
Demand's child/port identity and polarity. Construction does not emit a
separate `Unit+ <= arg(N2)` pair. Only if an actual positive Function `P+` is
compared and decomposed against `N2-` does ordinary contravariant Function
decomposition yield `arg(N2)+ <= arg(P)-`; this is explicitly conditional on
the parent comparison and remains a call-check consequence, not F2 admission.

The useful prior wrapper-graph retention and conditional identity-substitution
facts are retained with their typing limits. No semantic `IF(g)`, F2 clause,
complete inlet, VIEW, CHECK or parent theorem is constructed. Original A/B
domains and all quantifiers remain unchanged and OPEN.

## Source pins and static gate

Before the correction, all twelve contract pins matched the recorded values:

- prior source-gate review: `35536c07acd17b8531eae9e62f12c7089f712385685812814df2a58c7bea1bf2`
- prior contract: `1b2c953011a2ffbfb7fdc8d0783869b7b85ef2e2a9824e23d284de1417fdf491`
- prior source artifact / handoff: `e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9` / `814f3a723664b9a48d81a282efb8c9becaca20ffaae7d0f807b15cf2695b6204`
- prior proof artifact / handoff: `3dc2aee3594ecadbf42a6dee4b52c6767d058cbc5fcca0ee89067fd81f28c865` / `cdea6601d58bf41c812209bb48eb385801770d976646b1fd36632d499eaab04f`
- `shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
- `candidate_call.rs`: `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1`
- `candidate_source.rs`: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`
- `lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- approved Function-view direction: `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`
- original joint forward parent: `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6`

`python3 tools/agent_sprint.py check` passed after correction. This is
workflow/static validation only, not proof, runtime evidence, or independent
review. No compiler edit, tests, builds, probes, or execution were performed.

## Next exact lease

The selected next lane is the independent Sol proof at
`notes/theory/2026-10-17-c2-native-call-operand-correspondence.md` with handoff
`tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence.md`,
maximum 180 active seconds. It must prove the typed equations and conditional
Function child consequence from the pinned source, then state the admission
limits. It must not use the withdrawn candidate predicate as a theorem or
upgrade the call-check constraint into F2 admission. Fresh sequential
compiler_referee and spec_auditor reviews follow proof freeze.
