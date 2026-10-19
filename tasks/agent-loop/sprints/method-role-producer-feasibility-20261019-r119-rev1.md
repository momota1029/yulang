# Sprint R119 — method member producer feasibility and vertical path

Status: CANDIDATE pending a fresh pre-spec review and Luna's grant.  
Branch / baseline: `research/simple-sub-intrusion` at `af551a720`, with the R111–R118 checkpoint range pushed.  
Goal: advance the original proof-backed inference/evaluator goal while giving method/role syntax a concrete producer path. Keep all six effect-hygiene parents, ordinary/effectful runnable-surface work, Simple-sub and evaluator A/B visible and open.

## Fixed outcome

For the exact R100 source fixture

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

produce two linked but non-authoritative results:

1. **Proof/source refinement.** Starting from R112's source-qualified obstruction and R116's conditional callable/role bridge, derive the minimal source facts and identities a future authentic producer must provide for this fixture. Map each fact to the existing consumer and show conditionally how the binder-owned §21 roles and receiver-first curried Apply continue through the inspected LocalSource, candidate and RuntimeProgram consumers. Record the first missing producer premise precisely. Do not repeat R100/R112 as a repository-wide absence claim or claim current execution/result `2`.
2. **Implementation packet.** Inspect the current HIR/source, candidate and runtime owners and specify one exact post-adoption vertical implementation contract: authentic member identity, ordered executable binders and annotations, body/root and lexical environment, source-qualified `Apply(Apply(C_member, E_receiver), E_argument)`, candidate admission and runtime publication. Name prerequisites, owner-local edits, source origins, falsifiers and the first public CLI observation. This is planning evidence only; do not edit code or tests.

The R85 offer remains the sole proposed semantic decision surface, Draft and unadopted. This sprint must not rewrite or adopt it, decide lookup/ambiguity/diagnostics, or grant implementation authority. No semantic claim follows from the packets. The R116 and R118 public CLI results remain prior finite observations; this sprint runs no command.

## Method and falsifiers

Use a constructor-refinement table. For every required source fact, identify (a) the exact syntax/HIR owner that currently retains it or rejects the member, (b) the proposed producer output that would carry it, and (c) the existing consumer that reads it. Validate identity and scope from source structure rather than spelling. Apply R116's conditional bridge only after its actual producer premises are listed.

The proposal fails if it needs synthetic top-level bindings, signature-derived executable roles, loses body/binder provenance, treats parser association as semantic resolution, bypasses ordinary inference/admission, or cannot point to a distinct owned producer and consumer for any required field. An existing authentic path that already constructs and admits this exact member falsifies the R112-based obstruction and must be reported instead of proposing a duplicate.

## Authority, dependencies and exclusions

The R85 canonical offer remains Draft at SHA-256 `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`. Reuse, at the listed hashes, the R100 exact-source result (`84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971`), R112 obstruction (`7f6e27c07a7a39424eed647a0250822075ec65233e06ead3677ceff3a6a6a6b1`), R116 conditional bridge (`39183afeac8b11366bb68fd357c95ed18de0a969a40640f4908c4a05f53b65ef`), and current owners:

```text
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
```

The proof lane may inspect only those frozen documents and source pins. The implementation lane may additionally inspect the exact producer/consumer owners it needs from `crates/yu-hir/src/shadow.rs`, `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-solver/src/candidate_source.rs`, `tools/inference-playground/src/runtime/program.rs`, and the CLI entry owners. Any dependency drift returns to Luna before writing. No code, tests, builds, CLI, semantic edits, question-board writes, expected-output changes or Git are authorized.

No six-front proof expansion is in this packet. R118 supplied the latest bounded ordered-handler/outside-selection CLI witness. At R119 closeout, select an under-covered distinct front such as continuation capture/resumption or a genuine outward request plus suffix, while retaining §21 and static-to-runtime projection in the coverage map. Ordinary/effectful surface work remains active after R118's exact `7\n` and `11\n` observations.

## Leases, lanes and review

After CLEAN pre-spec review and Luna's grant:

- Sol/high proof lane, cap 420 seconds; writes only `notes/theory/2026-10-19-r119-member-producer-feasibility.md` and `tasks/agent-loop/inbox/20261019-r119-proof.md`.
- Luna/high implementation-assessment lane, cap 300 seconds; writes only `notes/design/2026-10-19-r119-first-method-implementation-packet.md` and `tasks/agent-loop/inbox/20261019-r119-implementation.md`.
- Fresh independent compiler/source and specification reviews, 240 seconds total, only after both writers stop. Reviewers check the conditional consumer proof, exact source-owner refinement, authority boundary and vertical packet. Authors cannot review their own outputs.
- Luna owns `tasks/agent-loop/current.json`, closeout, Git and any next-sprint contract.

Total cap 1,200 seconds: inventory 120, proof 420, implementation 300, reviews 240, closeout 120. Astra 0. No executable commands are authorized. Preserve the three inherited UNKNOWN reservations and quarantined board lease. Stop on a blocking finding, missing owner, dependency drift, authority ambiguity, exhausted budget or falsifier. R85 adoption remains an explicit user decision after the complete reviewed offer is presented; a clean review does not supply it.
