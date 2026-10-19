# Sprint: bounded receiving source bridge and first role-call decision

Status: CANDIDATE — exact selector delta and Luna activation pending  
Revision: 1  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Prior milestone: R78 rev2 OPEN/UNFINISHED; no budget carryover  
Original parent: Simple-sub, evaluator and A/B remain OPEN 0→0; R50 NOT_ADOPTED

## User priority and whole outcome

Balance proof depth with breadth: continue a bounded proof of effect hygiene at source receiving/selection; advance role/member semantics toward a real runnable surface; stop automatic storage/fiber investigation. The first surface milestone should be a small role-qualified receiver call whose exact selected member can be carried end-to-end. All proposed syntax and role laws in this packet remain unadopted until the user decides.

R79 has two parallel, independent lanes:

1. Derive the missing actual parser/HIR/LocalSource producer evidence for the three frozen R78 relay fixtures, or identify its first unsupported premise. Apply any result to the existing conditional runtime derivation. Stop at 900 seconds or the first genuine missing rule.
2. Prepare and independently review a decision-ready first role-call package comparing explicit role qualification with dot-member syntax. Prefer a role-qualified first runnable slice only as a proposal, because it avoids claiming that the first vertical slice settles general field/method precedence. Include exact competing declarations, expected outcomes, §21 parameter-role behavior, complete member identity/admission/runtime path, and a short route to `1`/`2`-style executable output. Explicitly leave general dot-field collision open unless a real source example is established.

No semantic adoption, code, test, expected-output or production change is authorized by this contract. After review, a user decision and a separate exact implementation contract are required before implementation or executable verification.

## Lane A — bounded source-producing proof

**Question `R79-SOURCE-HIR-1`:** For each frozen U/O/S source in the R78 certificate, do the authentic source constructors establish the exact premises assumed by its conditional runtime derivation: parsed declaration and expression ownership; Lambda and outer parameter annotation; resolved formal Name; resolved operation family/operation identity; Catch arm order and pattern forms; and the corresponding `LocalSource` forms/occurrences? Then compose those premises with the frozen receiving/selection trace. Prove the source-to-runtime joins from constructors and consumers; test assertions or printed output do not discharge them.

**Success:** an occurrence-indexed derivation for all three exact strings, with each constructor, projection and consumer named, or a precise first missing rule/owner. State exactly what parent portion follows and what stays open. The scope is these three source projections only; it does not cover native K/D, residual typing, arbitrary continuations or universal hygiene. No storage, fiber, capture-inventory or representation work.

**Exact read pins:**

- `crates/yu-syntax/src/full_parse.rs` SHA-256 `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`.
- `crates/yu-syntax/src/declaration/binding.rs` SHA-256 `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544`.
- `crates/yu-syntax/src/declaration/act_decl.rs` SHA-256 `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74`.
- `crates/yu-syntax/src/expression/case_like.rs` SHA-256 `6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961`.
- `crates/yu-syntax/src/pattern/mod.rs` SHA-256 `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883`.
- `crates/yu-hir/src/module.rs` SHA-256 `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`.
- `crates/yu-hir/src/module/local_source.rs` SHA-256 `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
- `crates/yu-hir/src/module/source_annotation.rs` SHA-256 `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`.
- `tools/inference-playground/src/runtime/program.rs` SHA-256 `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`.
- `tools/inference-playground/src/runtime/machine.rs` SHA-256 `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.
- `tools/inference-playground/src/runtime/receiving.rs` SHA-256 `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` (direct receiving owner; do not treat the frozen R78 derivation as accepted theorem evidence).
- Governing principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md` SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Original fixture/test correspondence owner `tools/inference-playground/tests/runtime_receiving.rs` SHA-256 `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf` (read source only; no test execution).
- Frozen runtime derivation `notes/theory/2026-10-19-r78-receiving-selection-certificate.md` SHA-256 `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` and source fixture identities in its §2.

No wider source search, new dependency, test, probe, build, runtime command or source edit is authorized. A pin mismatch stops this lane before changed bytes are read or used. Reaching the first missing premise closes only this bounded attempt; `R79-SOURCE-HIR-1` stays OPEN unless the required derivation is established.

## Lane B — role-call decision package

Compare two unadopted call forms using the pinned role/impl grammar and current owner map. The role-qualified form may already parse; its role/member interpretation, not assumed parser acceptance, is the unadopted choice:

```yu
role SecondInt {
    my second: int -> int -> int
}

impl int: SecondInt {
    my second self selected = selected
}

my answer = SecondInt::second 1 2
```

Candidate outcome: the unique role-qualified member receives the integer receiver and explicit integer argument, returning `2`. This is a proposal, not a consequence of syntax acceptance. Compare with `1.second(2)` and explain which lookup decisions the role-qualified form avoids and which method-like behavior it still requires.

Include exact complete source examples and draft outcomes for unique selection, missing role/member, a duplicate implementation for the same receiver/role, same-spelled members under two distinct roles, effectful receiver and argument, an explicit Computation formal, and an outward request from the selected body. Use §21 exactly: all arguments are constructed inertly; outer unannotated/ordinary-annotated formals are Value and force/rebind once at their receiver activation, while explicit computation-annotated formals retain the carrier. Distinguish source diagnostics, valid draft behavior and provisional executable-admission refusal. State malformed syntax diagnostics separately. General field/method collision is OPEN and deferred from this role-qualified pilot unless a genuine, source-valid collision is demonstrated; do not imply it is solved.

Map all owners from source occurrence through RoleId/ImplId/member identity, declaration/member validation, member source root and lexical environment, unique selected callee identity, ordinary application elaboration and provenance, CandidateInference admission, and RuntimeProgram metadata/execution. Name every unavailable owner and typing/source-native proof obligation. Give a first runnable milestone and a focused command set for a later implementation contract; do not run those commands now.

Exact owner pins:

- `crates/yu-syntax/src/declaration/role_decl.rs` SHA-256 `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634`.
- `crates/yu-syntax/src/declaration/impl_decl.rs` SHA-256 `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` and `impl_tail.rs` SHA-256 `085fd4d0aac3735d9ac61a75a0a7b363a83b2a4bd0e78954a6908144e8853c24`.
- `crates/yu-hir/src/shadow.rs` SHA-256 `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856`; `crates/yu-hir/src/module.rs` SHA-256 `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`.
- `crates/yu-solver/src/candidate_source.rs` SHA-256 `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`; `crates/yu-solver/src/shadow_apply.rs` SHA-256 `b28193a5141b019afd6e10766dd77f86366f7a3c04e822b2a4fce784673b665b`.
- `tools/inference-playground/src/runtime/program.rs` SHA-256 `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11`; `machine.rs` SHA-256 `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`.
- Charter §21 owner `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` SHA-256 `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`.

Do not inspect unpinned dependencies without returning to Luna and updating this contract. The role-qualified grammar and any selected design remain unapproved.

## Leases and deliverables

Luna owns the candidate/activated contract, `tasks/agent-loop/current.json`, `notes/progress/2026-10-19-r79-closeout.md`, and these exact design artifacts:

- `notes/design/2026-10-19-r79-first-executable-role-call.md`
- `notes/progress/2026-10-19-r79-surface-readiness.md`
- `tasks/agent-loop/inbox/20261019-r79-implementation.md`

Proof owner `/root/r79_proof` owns only:

- `notes/theory/2026-10-19-r79-source-receiving-bridge.md`
- `tasks/agent-loop/inbox/20261019-r79-proof.md`

Fresh compiler reviewer owns only `tasks/agent-loop/inbox/20261019-r79-compiler-review.md`; fresh spec reviewer owns only `tasks/agent-loop/inbox/20261019-r79-spec-review.md`. If their read-only roles prohibit file writes, Luna records inline verdicts with target hashes and STOP provenance. Freeze design/proof targets before review. Do not edit reviewed bytes.

No source, HIR, solver, runtime, test, fixture or expected-output path is leased. No semantic adoption, test, build, probe, CLI or Git command is authorized.

## Resources, stop and success

One fresh 3000-second grant: proof 900s, Luna design/readiness/handoff 900s, compiler review 450s, spec review 450s, integration 300s. Astra 0. No old R78 time refund/carryover. Charge unknown execution at the full issued allocation. Preserve the integration reserve for closeout; do not spend it on retries. Stop proof at the first exact missing constructor/premise or 900s. A blocking/major finding, pin drift, missing source example or exhausted lane leaves that gate OPEN/UNFINISHED; no automatic retry.

Success closes only (a) the three-fixture raw-source→LocalSource projection or its exact first obstruction and parent application, and (b) an independently reviewed role-call decision package. Neither result adopts method/role semantics or proves full effect hygiene. At the sprint boundary, seek the user's choice from the concrete package; only after approval can Luna activate an exact early-runnable implementation contract. Parent/evaluator/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED.
