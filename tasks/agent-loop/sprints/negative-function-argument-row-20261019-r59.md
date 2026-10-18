# Sprint negative-function-argument-row-20261019-r59 — derive the annotation constructor contract

Status: CANDIDATE pending dispatcher start check and final Luna activation. Revision 1.  
Branch / baseline: `research/simple-sub-intrusion` / `2b92f53082e609989b69f22bcbc498a4a2bb089d`.  
Primary: `/root`, proposed session `current-conversation-2026-10-19-r59`.  
Authority: original computation-forwarding preservation §§1,6–7; selected annotation policy and integration §§1,1.1–1.2,4–5; top-level inference principles §§1–5; reviewed R58 obstruction and closeout. R50 remains NOT ADOPTED.  
Contract revision / SHA-256 / approval: revision 1; record SHA in current state. No author writes before dispatcher start check, clean baseline, exact pins, live-identity reconciliation and primary approval.

## Original outcome and success evidence

Original forwarding theorem and Simple-sub A/B retain their original quantifiers, source domain and OPEN 0→0 status. This packet targets a necessary annotation source/native constructor contract; it does not close the forwarding theorem or authorize production.

Fixed source (unchanged from reviewed R58):

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The original formal Computation row, the whole-function Function argument row and the whole-function Function result row are three distinct annotation positions, even where they mention the same resolved `io` declaration. Incoming formal effect `E` stays open. The negative concrete Function-argument row cannot be removed from preflight or native checking by an unproved exception.

Fixed question: **Under the existing annotation authority, what exact checking and exposed signature constraints should represent the negative concrete Function-argument effect row, and how must they preserve annotation position/identity and reach their actual propagation, capture and consumer owners without constraining the original incoming `E`?**

Success evidence is either:

1. A polarity-indexed constructor/consumer contract derived from the selected annotation policy that maps each of the three source positions to its exact checked/exposed type and effect endpoints, source scope/identity, constraints and downstream consumers; traces actual intended slots 40/41/42 and the first captured provider map while keeping open `E`; and identifies every required propagation, extrusion, merge, FreshUse and admission premise; or
2. The first exact missing semantic, theorem or source/native premise that prevents that contract from being derived under current authority.

The result is a proof/design contract, not a claim that ordinary inference accepts the source, that the existing compiler implements the constructor, or that a whole solve succeeds. Do not choose a new annotation meaning or source restriction. Do not equate equal family spelling, row shape or provenance with native endpoint identity. A formal-permission constructor cannot be assumed to implement a whole-function ascription.

R58 is accepted only as the bounded fact that the ordinary candidate entry rejects this exact whole-function negative concrete row before collection/session/action/FreshUse; it is an implementation-coverage obstruction, not source exclusion, compatibility proof or parent counterexample. The matching native `candidate_signature_effect` guard is corroborating source evidence only. Do not bypass either guard, execute the candidate or use failed preflight as semantic evidence.

## Two continuing lanes

- Sol/high constructive lane: derive the polarity-indexed checking/exposed constructor from existing authoritative semantics and follow the exact constraints to physical consumers, then apply the result to the original forwarding obligation or name the first missing premise. Exact outputs: `notes/theory/2026-10-19-r59-negative-function-argument-row.md` and `tasks/agent-loop/inbox/20261019-r59-proof.md`.
- Luna/high read-only source-owner lane: independently map HIR annotation tree/identity, preflight and native annotation builder owners, all physical effect endpoints and constraints, open-row formal entry, levels/non-generic metadata, support/allowance views, extrusion/equality/FreshUse/consumer routes, and exact source-to-native requirements. Exact outputs: `notes/progress/2026-10-19-r59-annotation-constructor-owners.md` and `tasks/agent-loop/inbox/20261019-r59-implementation.md`.
- Astra: none; the principal risk is a source/native constructor correspondence, not a bounded core proof needing Astra.
- No code, semantic changes, tests, parser/solver/compiler execution, builds, runtime, probes, instrumentation, measurements, expected-output/diagnostic changes, or production promotion. No safe code slice until this constructor contract is reviewed.
- Related in-envelope work may refine the polarity proof, source identity, constraint graph, physical owners and exact remaining premise. Any changed source, annotation meaning, implementation edit, execution request or added dependency returns to Luna before dependent work.
- Keep the complete forwarding theorem, dynamic receiving/Name/Force correspondence, soundness, principality, termination, complete Call and production gates separately OPEN unless directly discharged under their own original obligations.

## Permissions and resources

Exact output leases are the four paths above plus this contract for Luna only. No wildcard, scratch or generated-output leases. The frozen baseline and all direct inputs are pinned below. Primary current-state and Git paths remain Luna-only.

Fresh resource envelope: 1800 seconds total: Sol 600; Luna source-owner audit 500; independent compiler referee 200; independent spec auditor 200; Luna integration 300. No Astra and no carryover. Record actual durations/CPU/RSS only when observed. Review only after both author lanes stop and the exact output bytes freeze. Requested and observed model/effort stay separate; absent observations remain UNKNOWN. No descendants.

Static source/theory/hash inspection only. No process probes. Stop at the justified constructor contract or first exact missing premise, source/authority/dependency change, cap, STOP or session end. Unknown writers retain quarantined leases and reservations.

## Frozen seams and handoff

Frozen dependency SHA-256 manifest:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
477ada20e61ce5355601af138b37016ba1a8036e65f4f39627beda2abe062adf  notes/theory/2026-10-15-computation-signed-copy-source-bridge.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
a4f1b9ff32a550ad11bcc4b8cfe8d3b0a293c99a4c7e2ad26e6195cc008d4164  notes/progress/2026-10-19-r58-closeout.md
6f10c1469bf99636d1399ce1de3e8a3be11036c5f53bfd84385320461c2efbe3  notes/theory/2026-10-19-r58-provider-publication-exposure.md
a9602e9993fdaf5bdba5fd6ffcfbe5073094978d9296fc92c6994b4aa0c59d59  tasks/agent-loop/inbox/20261019-r58-proof.md
50752e1d119df65c42e79e54c8bd2d84a0796c70f1e257a087f9910eb95714a3  notes/progress/2026-10-19-r58-provider-publication-owners.md
3fd4eaea54e84efd9501e65e4b853d3888496c851ea77794c7cdae53c946bf75  tasks/agent-loop/inbox/20261019-r58-implementation.md
87491930517debeea7c96baf14a74fe6cdd6a94dd8619554512ec672a6f71223  tasks/agent-loop/sprints/original-name-prepublication-exposure-20261019-r58.md
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

R59 output, live-receipt and review hashes are recorded only after exact freeze. Fresh reviewers check the constructor contract as a whole, not merely that preflight stops refusing. The proof applies any derived rule to the original parent without changing quantifiers or accepted semantics. The closeout records the exact missing premise, review, resource outcome, checks and separate implementation/production status. Luna alone synchronizes current state and commits/pushes explicit reviewed paths.

Next dispatcher consultation: sprint start/end, material authority/dependency/lease/resource change, proof obstruction/counterexample, integration seam or replanning. This candidate remains inactive until Luna records a start-boundary check, final pin verification, reconciled live identities and approval.
