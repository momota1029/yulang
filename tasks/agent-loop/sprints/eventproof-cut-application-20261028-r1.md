# Sprint EVENTPROOF-CUT-APPLICATION-20261028/r1

Status: READY after proof-worker ACK. Baseline: committed `yulang3` HEAD `8fd68e2618ea6b3ccd5299809c7101ace1da0a98`. Work occurs only in `/tmp/yulang-eventproof-lifetime-20261028` on branch `research/eventproof-cut-application-20261028-r1`. The primary launch receipt will state the exact contract/current-state commit used to create the branch; workers must report that exact HEAD and must not treat the baseline as the branch HEAD.

## Fixed outcome

Apply the existing `OriginalSourceClosure.generated_value_body_consumer` result at its actual generated EventProof cut. For the original arbitrary pattern/body and admitted Build derivation, derive the exact decoded-field preservation supplied by `proof_packet_preserves` for the EventProof packet and generated body consumer. Preserve event current/history, active call fields, installed/interface/descriptor and the other actual fields; allow logical eta, witness and view interpretation to change. Keep the existing Value-entry / Return quantifiers, entry mode, original source context and body.

This packet is scoped to the existing constructed `closureKernel` and `proofAdmissions` path used by `generated_value_body_consumer`. It does not claim conservativity for every raw payload accepted under arbitrary original admissions, and must not impose a new empty-write restriction on the original EventProof payload. Any specialized theorem must retain the exact original Build and `Satisfies` hypotheses.

`OriginalEffectHygiene.Native.return_then_name_cannot_revive` is stated over `Native.World`/`Control`; this sprint's generated cut is `OriginalSourceEnvironment.Decoded`. No authenticated Rust-to-decoder or `Decoded`-to-native correspondence is pinned. Do not identify these states or claim actual native lifetime/permission preservation from decoded equality. A conditional corollary is permitted only if it adds explicit, owner-derived equality premises and is useful; otherwise omit it and record the missing bridge. Native lifetime, whole effect hygiene, original parent and production gates remain OPEN.

Success requires a new kernel-checked theorem that actually composes the generated Value-body consumer with decoded-field preservation, full theorem type and transitive axiom audit, then fresh independent review. A wrapper that merely renames `proof_packet_preserves`, assumes its conclusion, narrows the original Build quantifiers, or treats runtime projection equality as semantic membership is not success. If the generated cut already yields the exact target or the stronger application is not derivable under the original hypotheses, freeze that exact result and the first missing premise without weakening the scope.

## Exact leases

All paths below are inside the isolated clone except the absolute proof scratch root. Source modules and project files listed in the dependency table are read-only.

### Proof lane

- New `notes/theory/lean/YulangClosure/OriginalEventProofCut.lean`
- New `tasks/agent-loop/inbox/eventproof-cut-20261028-proof.md`
- New `/tmp/yulang-eventproof-lifetime-20261028/proof/` (exclusive scratch and generated project copy/cache/audit outputs)

All other paths are read-only. Do not modify `OriginalSourceClosure.lean`, `OriginalSourceEnvironment.lean`, `OriginalEffectHygiene.lean`, original contracts, source definitions, project configuration, manifests, runtime files, fixtures or expected output. Before any write, check every new output absent and use exclusive-create semantics. Do not write to the existing tracked `notes/theory/lean/.lake` scratch files or its build cache. No semantics decision, source-domain widening, nested sprint, test, Cargo, dependency change, `sorry`, `admit`, or output overwrite.

## Pinned dependency cone

All hashes must match in the isolated clone before proof edits or verification. A mismatch stops the affected work.

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean` | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` |
| `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `notes/theory/lean/YulangClosure/OriginalCheckingAdmission.lean` | `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7` |
| `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `notes/theory/lean/YulangClosure/OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `notes/theory/lean/YulangClosure/OriginalRecursivePair.lean` | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` |
| `notes/theory/lean/YulangClosure/OriginalRetainedParameter.lean` | `ae8915cf002019541d0658895f0604e98700ac23f47aac479fc8382cf65ef799` |
| `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| `notes/theory/lean/YulangClosure/OriginalSourceClosure.lean` | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalWorldReadout.lean` | `edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00` |
| `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| `notes/theory/lean/YulangClosure/SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| `notes/theory/lean/YulangClosure/SourceSignatureConstruction.lean` | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |
| `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean` (scope boundary only) | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## Resources and gates

Fresh ceiling **1400 seconds**: proof 900s, fresh independent review 350s, Luna 100s, dispatcher 50s. No transfer or renewal. Proof: at most 8 top-level Lean/Lake calls and 300 seconds total under pinned Lean 4.35.0, one project verifier, one CPU, 1 GiB RSS target, complete theorem type and transitive axiom audit. Cargo=0, tests=0, Astra=0. Record actual UTC starts/stops, commands and resource results; UNKNOWN stays UNKNOWN.

The proof lane may start only after its ACK, exact checkout/dependency verification and output absence gates. A fresh non-author reviewer distinct from the author starts after write-cessation ACK, read-only ≤350s. Reviewer runs no Git, Lean/Lake, Cargo or tests and checks the original quantifiers, generated-cut application, theorem types/axioms, dependency hashes and Native.World boundary. Any restricted payload assumption, false runtime/native identification, mismatched artifact or unsupported premise leaves outcome INCOMPLETE.

This sprint does not close the source/native bridge, full EventProof conservativity, whole effect hygiene, A/B, principality, termination, implementation or production.
