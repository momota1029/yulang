# WHOLE-PRINCIPALITY-SOURCE-20261026/r2 handoff

Author: `/root/principality_source_r2`, generic lean_prover fallback; no descendants.
Baseline: `45d307a0aa01722b5aac289b07d71953630abca7`, branch `yulang3`.
Status: source-side construction kernel-accepted; original whole principality OPEN.
Independent review: pending separate nonauthor review. No self-certification.
Runtime model/effort: inherited; not independently inspected.

## Frozen outputs

| File | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SourcePrincipalTransport.lean` | `ab86c4448dcddcb5e20ef1495e317c4d0fc04ad0ff52c4323779d12f5fde33ee` |
| `notes/theory/2026-10-26-source-principal-transport.md` | `971f61bceab6cdbc68ea3900066b84a41176679960fb2ccfd35900b963c93857` |

Only these two files and this handoff were written in the repository. No root
imports, compiler, expectations, configuration, shared status, Git or shared
cache changes. All producer writes stopped after this handoff.

## Concrete result and original parent boundary

Original parent: source-preservation (2026-10-13) §§1,3,5, immutable birth-level
SCC correction (2026-10-24), top-level inference principles (2026-10-11).
All-source/full Call/effects, monomorphic recursion, scope, shared witness,
publication/use and future quantifiers remain unchanged.

The actual raw source is
`top = lambda h. let rec f = lambda x. lambda y. {first=h x,next=f {a=y}} in f`.
The complete source builder constructs both original Apps and recursive context.
New checked facts include the ordered Return/rebind suffix after h, a genuine
local source Name h derivation from the current allocated installed tuple,
source owner retention under every original frame class, and a constructed
returned-object readout of h's current actual value/provider at the App subject.
The supplied Return binder/data are not claimed admitted; the finalRoot versus
returnedValue distinction is explicit.

Ten authored roots in `YulangClosure.SourcePrincipalTransport`:

- `program_call_owners`
- `actual_body_bindings`
- `recursive_name_is_monomorphic`
- `h_call_complete_rule`
- `recursive_call_complete_rule`
- `recursive_field_retains_h_suffix`
- `h_name_source_derivation`
- `source_owners_after_all_frames`
- `source_subjects_after_all_frames`
- `h_return_supplies_current_receiver`

The note gives every material theorem input and conclusion. The exact complete
printed types (including private/generated declarations) are in the audit log.
No original principal package, instanceOf, native success, whole source judgment
for program, nonempty qualifying occurrence or source counterexample is claimed.

## Exact obstruction, applying AR/RZ rather than restarting them

AR1/AR2 construct the actual recursive input -> fresh x binding -> inner closure
capture -> future Name x -> h family. RZ1-RZ5 supply this concrete T/Y event's
local whole checking packet with existing view I and its source receiving index
H. The new source construction exposes the actual h owner and returned-callee
readout from the original tree/environment before erasure.

Still missing:

```text
actualOccurrence(z).receiver = receiving_index(source_frame(Z_real))
```

Here `z` is the actual fresh Record-field copy at
`p = Replay(Argument/Swap(Replay(recursiveCompletion, fCall)), hBoundary)`.
Its positive pair is T/Y, target 1, new operation-local memo, empty selected
lower list. Direct F/F is birth-qualified but creates no copy. The delayed p
has support from both F/F and cross-birth F/H. Native Parent stores that set,
not an authenticated receiving projection; current activation uses any qualified
support member. ScopedDemand is consumed at FunctionPort and reset for a Value
ExtrusionLink, so it cannot supply the missing scalar receiving field.

This is not global information-loss: existing Derived/Replay/FunctionPort and
creation data retain both routes. The smallest next construction is a source/native
ExtrudeFresh correspondence for THIS original signed boundary and telescope,
proving it is the same occurrence ID/pair/memo. Source traces supply its source
half before erasure, but the all-future dependent family cannot be replaced by
one successful trace. If needed, retain an original signed-boundary evidence
handle from the App/bound producer through ordered replay/ports; do not add an
arbitrary receiver selector or read any source set element as the conclusion.
A proved H association would make this case nonqualifying and resolve the local
attribution seam; actual principal coverage still needs a qualifying case's
joint source strategy and the original instance ordering.

## Verification receipt and failures

Owned scratch/cache: `/workspace/scratch/e3678bef96db/principality-source-r2`. All nine imported source files match the
initial frozen source snapshot and current repository bytes. No shared .lake
was copied or mutated. Read-only installed toolchain:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.

Actual versions, exit 0:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Nine dependency modules were built sequentially with `lake build +Module`;
last was `YulangClosure.OriginalSourceEnvironment`. The sequence took 40.7s.
Each process had `LEAN_NUM_THREADS=1`, project `-j1 -M1024`, 120s timeout.
Then three focused module checks (first failed, next two passed):

```sh
lake build +YulangClosure.SourcePrincipalTransport
lake env lean -j1 -M1024 AuditSourcePrincipalTransport.lean
```

Final module and complete audit exit 0 without warnings. Complete originating
census: **114 declarations, 41 definitions, 73 theorems, 10 required authored
roots**, including private/generated helpers originating outside the public
namespace. Theorem axiom distribution: **35 empty, 19 propext, 19 propext +
Classical.choice + Quot.sound**. No project axioms, sorryAx, native evaluation
assumptions or kernel bypass. Every authored root except actual_body_bindings
uses the three standard axioms; that root uses none.

Material failures preserved: unsupported Lake `-j` scheduler flag (no Lean
spawned); first source module pass required well-founded equation unfolding and
subject rewrite order repair; first scratch audit needed explicit Nat/String
counter types. No scope or theorem statement weakened to fix the checks.
Total Lean compilation/audit invocations: 14, under the 20-check ceiling.
No full/default build and no native compiler/test execution.

Complete dependency source scan found only one `axiom` word in a comment.
The audit recursively checks actual constant dependencies; source scanning is
not used as an axiom audit. The bundled checker was not additionally repeated:
the complete originating declaration audit covers all ten public roots and all
private/generated ones at the same pinned limits. Root also independently
reported a successful 11-job focused build.

## All scratch outputs and hashes

The full copied source project and generated cache are owned scratch outputs.
Key evidence (paths relative to `/workspace/scratch/e3678bef96db/principality-source-r2`):

| Artifact | SHA-256 |
| --- | --- |
| `AuditSourcePrincipalTransport.lean` | `57bcdf0639d70ca182c0b0467a5f492928afae3023300a456380a77a4f1d6df0` |
| `evidence/audit-01.log` | `194da7afcb18ead18ba54be549910e226c3bbd1d56b134dcc17ddc327f572342` |
| `evidence/audit.log` | `01eb3640f9d3b5d38bb08147b9e9dc5a70749ad348a5b1e413ca294669559f48` |
| `evidence/census.json` | `8f387af620faf3c54e81b4b09d464ec35c5539ecb443b67262bb387c1492bfb1` |
| `evidence/check-01.log` | `e9d363bbc3549cdc41a89e2823f8b7c861bc5a5fbcdacad375e8c4303f9b45e4` |
| `evidence/check-02.log` | `0db68e20b92f848099519306441000814c2e1749e7d1c98eca6861198b902eb2` |
| `evidence/check-03.log` | `ff01d8fff70a1e5a2823a5445bb6b24f5e4cfea53e3731d71eb8eeab5bffe2a8` |
| `evidence/dependency-build.log` | `1df7cfa339802d5bfa11f7ce6a94d98f1171544cfd4806751b69ba73f38575b6` |
| `evidence/dependency-order.txt` | `657c4a4d298fad567b99308e5a2c34159a89d53eb0183e56ff68934d10548268` |
| `evidence/direct-source-hashes.json` | `e06aee2cddfb51c6f9f6f4c65c0c9c7f08734ef829b1c85d750ad670227dc62d` |
| `evidence/frozen-inputs.json` | `2593a85e551623c78283b5fa94a71f25dec741c0c693714d05ab956582aed940` |

Full exact types and axiom output are in `evidence/audit.log`; all declaration
names/kinds/axiom arrays are in `evidence/census.json`. The copied 167-file
initial source/config manifest is `evidence/frozen-inputs.json`. The dependency
order is explicit, and failed logs have not been overwritten by successes.
The primary may archive these immutable logs with the review/integration record.

## Complete direct-input hashes

| Original repository input | SHA-256 |
| --- | --- |
| `AGENTS.md` | `ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f` |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` |
| `.agents/skills/yulang-lean-proofs/SKILL.md` | `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7` |
| `.agents/skills/yulang-lean-proofs/references/sources.md` | `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` |
| `.agents/skills/yulang-lean-proofs/references/execution.md` | `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b` |
| `.codex/agents/lean-prover.toml` | `a595880badf28482ad64c61d141e7eaa3781fe079d831e9e5d44b60669181109` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/theory/2026-10-24-birth-level-extrusion-redundancy.md` | `3d447e6982069023d2be69cee3e4cfc208e3f231f92407f34c0d1d8942a44211` |
| `notes/theory/2026-10-24-residual-demand-source-association.md` | `c96289283cd427d949160f6973c925d1faec6a4fa43ce8fae3e7ae47dc65936e` |
| `notes/theory/2026-10-24-source-indexed-constraint-derivation.md` | `f11968c9e30d64a96e0a0f7bfebd75d31ff53a36e0af884d1d0cc3fe32491698` |
| `notes/theory/2026-10-24-actual-replay-receiving-diagram.md` | `f7050f30bde37bc46ff764078ae948ec67b74ecb96ac320fcf5db36b8d4c2f18` |
| `notes/theory/2026-10-24-concrete-extrusion-source-realization.md` | `d7e61d29ccec67ab77e05c0ebde232a8787370647d4fce0a4c65bf3d8cee31ed` |
| `notes/theory/2026-10-24-actual-copy-history-transport.md` | `270cda463f47d6229def252a8a5e43ae08a04d268ee08538a529a1dd7990c910` |
| `notes/theory/lean/YulangClosure/OriginalPrincipality.lean` | `c9d214cd086aa1fbdf8f471e7b52c8cccddaa971fc68a8bb0956c9539d098dc7` |
| `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `notes/theory/lean/YulangClosure/BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `ab37f3739d89dff9e7918fb745f5a308a3e597ab4aaa9e5a172fcacaeddabf0b` |
| `notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean` | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07` |

**STOP: producer module, note and handoff frozen; no descendants or running checker.**
