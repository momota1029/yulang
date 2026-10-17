# Sprint `npair-actual-argument-ingress-20261018`

Status: ACTIVE, primary-issued 2026-10-18. Revision 1.
Branch/baseline: `research/simple-sub-intrusion` / `b3a9b1739b59d8c7991b5f798e98f71f96904b19`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original theorem, source domain, quantifiers, receive route, C1/C2 working rule and F1/FK1 obligations are unchanged.
Prior closeout: `notes/progress/2026-10-18-npair-operation-self-source-realization-closeout.md`, SHA-256 `886af9097fafe0bab83e1e87f9382750f0e12d1de9d5490e0dc9b93ae2171add`.

## Fixed outcome

Test and trace the authentic source route

```text
f0 → actual Apply to receive's formal f
→ f() → same returned R1 installed as g → g()
```

The returned Function's written `ctrl` field `s1` must be traced to receive's Permission negative port D through actual argument comparison, Function children and both ordered Replay inputs. Preserve the operation root Self `s0` as a distinct field/origin. Apply the result to the same original contribution at the relevant NPAIR ingress edge only if every constructor/action is established. An accepted top-level call or coexisting `s1`/D metadata alone is insufficient.

The existing source fixture contains the full receive body but has no call site. This contract authorizes one reversible source input addition to that same fixture:

```yu
my received = receive f0
```

The added source is an experiment inside the original source domain, not a theorem premise, source restriction, semantic change, new test, or expected-output change. Restore the exact pinned bytes after recording the result if the normal compiler refuses the source. Do not invent a fallback transition.

## Proof and implementation lanes

1. **Constructive proof, Sol/prover/high, cap600s.** Derive the exact source/HIR action and ordered field comparisons from the pinned owners, from actual f0 argument through same returned R1 and `s1` to D. Keep original contribution identity, theta, provider/world/assignment, complete Function children, guard, scopes, both Replay inputs, continuations and independent alternatives. Apply only the established edge to original `NPAIR-OP-SOURCE-WITNESS-20261017` / H0, L2 `eta`, P3/P6; report any edge not derivable. Universal original-domain compatibility, W/Z, Call residual, F1/FK1 and parent closure stay separate. Write only:
   - `notes/theory/2026-10-18-npair-actual-argument-ingress.md`
   - `tasks/agent-loop/inbox/20261018-npair-actual-argument-ingress.md`

2. **Implementation/source path, Luna/implementer/high, cap720s.** Read only the pinned source owners and existing example first. The only writable compiler-input path is the one leased fixture, and only for the exact call line above. No code, harness, test, expected output, Cargo manifest, lockfile or public API changes. Run the exact existing example once:

   ```sh
   timeout 120s cargo run --offline \
     --manifest-path crates/yu-solver/Cargo.toml \
     --example research_source_registration \
     --features shadow-apply-candidate
   ```

   Report acceptance/refusal, source/HIR occurrence and declaration resolution, collector coverage for the added binding, and each actual edge. If output does not expose internals, source inspection must derive them; do not present the run as evidence for unseen consumers. Structural recovery, HIR error, solve refusal/conflict, absent collector coverage or absent actual comparison/Replay means that edge remains unestablished. Write only:
   - `notes/progress/2026-10-18-npair-actual-argument-source-path.md`
   - `tasks/agent-loop/inbox/20261018-npair-actual-argument-source-path.md`
   - the single fixture path below, restored exactly if refused

Exact read owners and pins:

| Path | SHA-256 | Access |
|---|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce` | read-only |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` | read-only |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` | read-only |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` | read-only |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` | read-only |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` | read-only |
| `crates/yu-solver/examples/research_source_registration.rs` | `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c` | read-only |
| `tasks/agent-loop/fixtures/20261017-receive-choose.yu` | `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0` | one-line reversible write |

If a new source owner is indispensable, stop before reading it and return its exact path and the required evidence. Luna will pin and lease it through a sequential contract revision.

## Frozen authorities and prior result

- C1/C2 working semantic rule: `notes/design/2026-10-18-npair-operation-self-effect-contract-candidate.md`, SHA-256 `c8c9854c32cdb3dc5e9fe8e1be15293e3b05bb0b393daff3632f9ba516df1455`; Luna adoption and compatibility debt are in prior contract/closeout.
- Reviewed same-reference/root Self descriptor result: `notes/theory/2026-10-18-npair-operation-self-source-realization.md`, SHA-256 `cc8c96d288ae5fb548acbb8437a504ee0691e86f9f8e2915ded2e67ecbca0b85`; independent review CLEAN. It proves no inner field move.
- Original source interface: `notes/theory/2026-10-08-call-source-interface-construction.md`, SHA-256 `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`.
- Approved Option 2: `questions/2026-10-05-production-function-bound-membership/approved-answer.md`, SHA-256 `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179`.
- Original NPAIR and adopted P1–P6 obligations are referenced and preserved in the proof artifact's direct manifest.
- Previous implementation/source audit SHA `ae65cf84502e60bab5743f177ef6f8369c0c793564e0a96e22c729ddbd0343d6`; review CLEAN. It proves only the former fixture lacks an f0→receive edge and the then-leased compiler APIs cannot join it.

## Review, resources and stop

Fresh independent reviews: 150 seconds proof/spec and 150 seconds implementation/compiler. Luna primary/integration180 seconds. Total sprint envelope1800 seconds, Astra0, descendants0. Previous sprint reserves do not roll over. One heavy process at most, assigned solely to the exact 120-second Cargo command above; no other builds/tests/probes. Effective model metadata remains UNKNOWN absent runtime observation.

Stop at a source refusal/conflict, unleased owner, unsupported semantic case, missing actual `s1→D` comparison or either Replay input, resource cap, unknown writer, or need for public semantic changes. A failure at one edge does not erase established earlier edges. No `At`, N-Subtract, H0/L2 completion or parent closure is inferred from an accepted call alone. Only Luna stages explicit paths and pushes non-forced.
