# Sprint R60 — derive the paired annotation interface

Status: Revision 2 candidate contract; live activation authority is recorded in `tasks/agent-loop/current.json`.
Branch / baseline: `research/simple-sub-intrusion` / `b62bf4bed359ed5f8bd4728923d1807044f9e8c9`.
Primary: `/root`; proposed session `current-conversation-2026-10-19-r60`.
Authority: original computation-forwarding preservation §§1,6–7; selected annotation policy §§1,1.1–1.2,4–5; top-level inference principles §§1–5; reviewed R59 partial constructor result. R50 remains NOT ADOPTED.
No author writes before exact pins, clean baseline, dispatcher start check, live identity reconciliation, and Luna approval.

## Fixed goal and source

Preserve the original forwarding theorem's quantifiers, source domain and OPEN 0→0 status. The fixed source is unchanged:

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

R59 established a partial polarity/slot derivation and the exact first missing premise: an authentic admitted same-position, same-provider path from the exposed Function-argument AE to the checked original provider AE (or a proved same-instance alternative into the open entry effect), carrying that position's local permission and ordinary constraints. Its finite scalar assignment refutes only the uncoupled open-AE factorization; it is not a source/native or parent counterexample.

Fixed question: **Can the existing source/native constructors establish that same-position/same-provider exposed-AE to checked-provider entrance, with source-local permission correspondence and correlated result compatibility, while preserving every solution permitted by the original selected source/annotation contract under its actual premises, with an explicit correspondence for auxiliary constructor variables? If not, what exact theorem, source, or authority premise is missing?**

The original formal row `p_t`, whole-function argument row `p_A`, and result row `p_R` are distinct original source positions even though each resolves `io`. Keep incoming `E` open in the selected sense: do not derive a permission-based closed input cap; retain ordinary generated constraints and symbolic dependencies. Distinguish declared interface, actual inflow, and residual after actual subtraction. Do not treat covariant allowance as actual inflow or residual evidence.

## Success evidence

Either:

1. A source-indexed joint constructor judgment relating checking `A_c` and exposed `A_e` at the same original `p_A` and same provider; it carries source-local permission and generated constraints, proves the actual admitted `A_e -> A_c -> T` entrance or a genuine same-instance alternative, and accounts for the correlated `B_c/B_e` result interface without discarding any solution permitted by current semantics; or
2. The first exact missing premise/authority theorem preventing that constructor under current authority, naming the required entrance/permission obligation and stating whether exclusion of the R59 scalar assignment has been established or remains open.

Any proposed shared open AE row is only a candidate representation. Prove preservation of every solution permitted by the original selected source/annotation contract under its actual premises, with an explicit correspondence for auxiliary constructor variables; also preserve source scope/position identity, permission ownership, result correlation, and ordinary inference behavior before recommending adoption. Scalar entailment alone is insufficient. Do not invent a semantic rule or call for a new annotation-policy vote: selected polarity meanings are settled.

The result is a proof/design contract, not a claim that ordinary inference currently accepts the fixed source, that capture/FreshUse executes, that the parent is closed, or that any implementation is approved.

## Lanes and exact outputs

- Sol/high constructive lane, 600 seconds: derive the same-position/provider entrance and permission correspondence, prove preservation and result compatibility, or isolate the first exact premise preventing it. Outputs: `notes/theory/2026-10-19-r60-paired-annotation-interface.md` and `tasks/agent-loop/inbox/20261019-r60-proof.md`.
- Luna/high read-only source-owner lane, 500 seconds: independently specify constructor inputs/outputs, original positions/provider/scope, current slot and consumer owners, ordinary constraints, permission route, and exact source/native obligations without editing code. Outputs: `notes/progress/2026-10-19-r60-paired-constructor-owners.md` and `tasks/agent-loop/inbox/20261019-r60-implementation.md`.
- Fresh independent compiler and spec reviewers: 200 seconds each after both author lanes stop and all four exact output bytes freeze. Review the full correspondence, constraints/permissions/result interface, and the first-gap alternative; do not assess only whether a guard is bypassed.
- Luna integration: 300 seconds. Astra 0; no carryover.

## Boundaries and falsifiers

No code or semantic edits, tests, parser/solver/compiler execution, builds, runtime, probes, instrumentation or measurements. No production promotion. Keep both current R58 preflight and native guards authoritative. No safe code slice follows automatically from a CLEAN review.

Reject a proposed constructor if R59's uncoupled scalar assignment still satisfies it while `E_arg <= T` fails; if permission becomes a cap/contribution/automatic subtraction; if an unrelated provider or annotation position supplies evidence; if a shared row erases a legal source distinction or correlated result behavior; or if the constructor loses ordinary constraints/symbolic dependencies. Treat capture, signed transport, qualified merge, actual FreshUse restoration, result/Name correspondence and executable permission consumption as separately open downstream gates.

Stop at the reviewed joint constructor or exact missing premise, changed authority/dependency/source, cap, STOP or session end. No descendants. Unknown writers retain quarantined leases. Record requested and observed model/effort separately; unobserved runtime/resource measures remain UNKNOWN.

## Frozen dependency manifest

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
477ada20e61ce5355601af138b37016ba1a8036e65f4f39627beda2abe062adf  notes/theory/2026-10-15-computation-signed-copy-source-bridge.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
a67623a17f6c007ae0660135e3befd0c8d323886ea0fc7f5bc800eadc82bdf9d  notes/progress/2026-10-19-r59-closeout.md
31798df3416e4b9de029124df5eba66abdb430164c826becd337fad43289229b  notes/theory/2026-10-19-r59-negative-function-argument-row.md
b5bd0fe27373fc1d89668bb6357103ea1c5ebed903353d3d31d069e73f879ec7  tasks/agent-loop/inbox/20261019-r59-proof.md
486eff8031c3d0137d39dbb2163b5cc95f72cb73df219c2bbabd74e932424a12  notes/progress/2026-10-19-r59-annotation-constructor-owners.md
a6d0fecd56770e7aa5fd36ea2a6bb1e68f4b72da971ed4ad71e05c2dbd662cd2  tasks/agent-loop/inbox/20261019-r59-implementation.md
155d8817f050566f4a51ccbb82dabb4c809bcabb82654fdce07a6fbaf867fdcc  tasks/agent-loop/sprints/negative-function-argument-row-20261019-r59.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
```

The R59 closeout, proof and owner artifacts are the immediate prior evidence. Any changed byte or dependency returns through Luna before authors start. At sprint end, Luna alone synchronizes `current.json`/`tasks/current.md`, stages explicit reviewed paths, inspects the commit range, and commits/pushes. This candidate grants no authority until dispatcher start check and explicit primary activation.
