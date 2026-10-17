# Sprint module-use-source-map-and-provisional-observer-20261017

Status: READY FOR PROOF. Revision1; baseline `26ccc56f1`. The parent remains
the original Yulang inference/execution theorem with unchanged A/B claims,
quantifiers, source domain and source/native correspondence.

## Fixed outcomes

### Proof: `MODULE-DECL-USE-SCOPE`

For the exact source

```yu
my id x = x; my answer = id 0
```

derive, from the actual original source constructors, the `id` module
declaration's final-root/publication/reference path and its dependency-closed
whole-tuple use map at the `Name(id)` occurrence. Keep the declaration root,
use root, source anchors, provider, scopes, and actual resolution edge distinct.
Apply the result to the precise missing source-use premise in
`notes/theory/2026-10-17-ordinary-call-original-generation.md` §7.2.

Do not substitute the Lambda formal `x`, a native endpoint, a chosen public VP
root, or candidate `fresh_use` for the original publication/use derivation.
Keep the full source constructor alternatives, the whole dependency tuple, and
all original quantifiers. If the selected original constructors do not derive
the map, freeze the first unsupplied premise and owner; do not assume the
missing binding certificate.

One genuine module-use premise is closed only if an authentic derivation at the
original indices substitutes into that §7.2 obligation. A candidate test,
conditional constructor, endpoint map, or parallel source reference closes
zero original conditions. Complete Application/Call formation, embedding,
O0 and Code-Call substitution remain downstream.

Exact proof outputs:

- `notes/theory/2026-10-17-module-declaration-source-use-map.md`
- `tasks/agent-loop/inbox/20261017-module-declaration-source-use-map.md`

### Implementation: provisional candidate observer

Independently implement the exact reviewed recipe's candidate-only observer
slice for the same source. It may add only:

- a borrowed direct `Name { resolution: ModuleDef(target) }` observer and
  conditionally exposed pending module obligations in
  `crates/yu-solver/src/candidate_call.rs`;
- one exact-source regression in
  `crates/yu-solver/tests/research_accepted_call_vertical.rs`;
- paired handoff `tasks/agent-loop/inbox/20261017-module-call-provisional-observer.md`.

Preserve all existing pending suppliers and canonical unresolved premises. The
observer must not peel wrappers, infer formal registration from a Lambda,
choose a provider/root, add source admission, or emit an original typing
certificate. No production path or expected-output/diagnostic/fixture change
is authorized. This candidate lane is independent of the proof result.

The regression must falsify at least these confusions: actual `id` module
callee vs formal `x`; actual Integer literal `0` vs lexical Name; checking
occurrence and native ports retained; Call, whole-carrier, result/future and
module source/use obligations remain pending; existing candidate propagation,
callee fresh-use observation and nonempty `answer` export. Label every green
assertion as candidate-source evidence, not original admission or execution.
Include a formal-callee negative control for the direct observer/supplier
classification.

## Lanes, exact leases and order

Authors execute sequentially under current worker capacity.

1. Astra/medium, <=600s, owns only the two proof outputs above. Work through
   the actual Source Generalize/FinalRoot and module reference constructors,
   instantiate one full dependency-closed use map, then substitute into §7.2
   or report the exact owner/premise. No executable commands.
2. After Astra STOP, Luna/high, <=360s, owns only the two code paths and paired
   implementation handoff above. Consume reviewed recipe and fixed source;
   stop at any mismatch requiring routing/admission changes or another path.
   No descendants.
3. After both authors STOP and all artifacts freeze, sequential reviews:
   compiler/source review180s, spec review120s, architect/API review90s,
   regression pre-run review45s, one verification owner runs exactly one Cargo
   command <=120s, then regression receipt review45s. Each reviewer is fresh
   relative to the author whose work it reviews. No retries.

The sole verification command, after pre-run CLEAN, is:

```text
cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

Only the feature-enabled target above is in scope; its pass proves the named
candidate assertions only. A failure is evidence to fix or report within the
same exact two code paths. Do not infer full compiler/runtime success.

## Resources and stop conditions

Fresh envelope: 1800s total — Astra proof600 + Luna implementation360 + reviews
480 (compiler180 + spec120 + architect90 + regression pre/post45 each) + Luna
coordination120 + one Cargo verification120 + reserve120. Charge unavailable
runtime telemetry conservatively at the assignment cap; never claim an
unobserved model. Retire unused verification/review reserve at close.

Stop on dependency pin mismatch, absent actual publication/root-use input,
need to choose a provider or change source admission/observable behavior,
formal/module root conflation, scope/dependency loss, need to change paths,
candidate supplier loss, test expectation changes, command failure/cap, or user
STOP. Any semantic choice must be distinguished from conservative derivation;
ask the user only if validation requires a material admission/meaning choice.
This contract grants no rule adoption and no production authority.

Three inherited UNKNOWN worker assignments remain quarantined; no lease or
capacity is reclaimed from them.

## Frozen input pins

Baseline: `26ccc56f1`; contract revision1.

```text
notes/theory/2026-10-17-ordinary-call-original-generation.md bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab
tasks/agent-loop/inbox/20261017-ordinary-call-original-generation.md 1ff0c3dc71c4b7e09de5e00ff47b158627cc67320d29d820d38d76ed330b98d3
notes/design/2026-10-17-ordinary-call-generation-implementation-contract.md 04f67087908e0658fb20dfea492c11b43979e84333d7a32ab43ad3f92b48e794
tasks/agent-loop/inbox/20261017-ordinary-call-generation-implementation-contract.md 4d6808edab05e5b2aaff9d2f4d465feb03cad5b3398650688d0a2b18290fccda
notes/design/2026-10-08-source-generalize-definition.md 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
notes/theory/2026-10-08-source-generalize-definition-and-proof.md e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240
notes/theory/2026-10-08-id-descriptor-source-bridge.md dcc91b8cb958f68208b61f490b68cbc3d42318b65f14604b0ad80742b1798a10
notes/theory/2026-10-12-apply-reference-construction-proof.md 16d7c66828698992b36dcf1a6d8890303d10d6ed24809cd8da25ba8d1aa9e91a
notes/theory/2026-10-17-local-use-retention-applied-correspondence.md 198046b6eb398734cf657ab03f05e171f8be568c1e8feb31115b9adc46d5f1ff
notes/design/2026-10-16-source-remaining-root-constructor.md 4f9c483b6f3ca7a41ba3af622f91c17446823724269f2f1473b844b9f534cbd5
notes/theory/2026-10-16-module-expression-receiver-construction.md 18ad3edb997aacd0c744c3b292681f1f98704fbd101e9302173c52e2f646cb75
crates/yu-solver/src/candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
crates/yu-solver/src/candidate_call.rs cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1
crates/yu-solver/src/candidate_scheme.rs 52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a
crates/yu-solver/src/shadow_apply.rs bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf
crates/yu-solver/src/lib.rs 2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f
crates/yu-solver/tests/research_accepted_call_vertical.rs 9c3dea05d11c49bae09520d5f6fe27430f1706185232daf2cf8e8d801a42d71a
```
