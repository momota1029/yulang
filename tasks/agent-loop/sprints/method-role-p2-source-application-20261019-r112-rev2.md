# R112: apply exact source entry to the method-member constructor gap

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW, revision 2**. Revision 2 supersedes
rev1 only to pin the referenced R100 implementation-assessment input.
Primary and sole Git integrator: Luna `/root`. This packet rotates from R111's stopped continuation attempt to
the user's requested proof-backed method/role work. R111's test remains
FROZEN_UNVERIFIED and quarantined; R112 neither edits nor runs it.

## Fixed finite outcome

Apply the already reviewed R100 constructor/consumer analysis to the exact
source-entry premise established by R108, and prove a source-qualified,
finite obstruction at the HIR method-member producer boundary.

The exact R100 fixture is 148 bytes, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`,
without final LF:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

R108 established that this exact source enters one authentic ParsedFile and
retains its RoleDeclaration and ImplDeclaration roots, member ancestry, raw
child order and distinct `selected` occurrences in that same parse. R100's
`R100-ENTRY` premise is therefore discharged only for this exact fixture.
The remaining target is the original R100-P2-MEMBER obligation: connect that
authentic implementation member to the current owning HIR producer and show
whether it creates executable member binders, annotations, body and lexical
environment.

## Proof and falsifier

Reuse the exact pinned R100 proof rather than repeat its syntax/parser
inventory. Apply R108's observed direct-root identity to the complete current
owners `module::plan_root` and `module::lower_plan`; trace the root ordinal to
the planned variant and lowered HIR item. Then inspect only the already pinned
LocalSource boundary needed to establish whether an executable member source
can be formed from that output.

The expected finite result, subject to direct branch verification, is:

1. `plan_root` recognizes only a direct OperatorChain or an admitted plain
   BindingStatement as supported executable roots; RoleDeclaration and
   ImplDeclaration take the UnsupportedItem branch without descending to the
   nested member.
2. `lower_plan` maps that unsupported root to `HirItem::Error`; it does not
   allocate a member DefinitionRootId/HirParameterIds or call member body
   formation.
3. The LocalSource consumer skips `HirItem::Error`, so the authentic nested
   `second self selected = selected` member does not acquire an executable
   binder/body/environment through this route.

Keep the claim source-qualified to this exact fixture and these complete
owners. A distinct owner-local route that consumes this exact nested member
and creates its authentic executable binders/body/environment falsifies the
obstruction. Report any such route; do not enlarge the source domain or add a
new source pin. No semantic role lookup/dispatch rule, method type, member
selection, runtime result, or production repair is authorized.

The R85 positive role-call contract remains Draft and unadopted. This result
does not solve R85 P2/P3/P4, original Simple-sub/evaluator claims or A/B,
F1/FK1, R50, semantic approval, or production authority. It does not infer
that `SecondInt::second 1 2` evaluates to `2`.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| R100 revision-6 contract | `d595f4878b9f931214e5da0cba6d7e53cf3e2e0ca243ecad784e55cac1611dec` |
| R100 conditional proof | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R100 proof handoff | `1a692cb7f3c31e83bf60ee90763216ef3253f2c357747c9258eff16e2f8cec19` |
| R100 implementation assessment (`NO_SAFE_ROLE_CODE_SLICE`) | `60a1a90c37b5c8377addf12cd07d9703f98a093a9c1eeb86fb5db2b81f847596` |
| R108 exact-source closeout | `cfc0e6a45b329e099f1263833bc7c0160c8d0e034bf7596ffef1dc5da10666e8` |
| R108 exact-source test | `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a` |
| R85 positive role-call contract (Draft) | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |

Any pin mismatch or new required owner stops this packet. No pin expansion.
Rev1 SHA-256: `64b53cd9a0f7c5d29858fe6f879822542fac0172d2c8249c16169a8ddf431ff4`.
Its pre-edit review is preserved at
`tasks/agent-loop/inbox/20261019-r112-pre-spec-review.md`; it does not clear
rev2.

## Lanes, outputs, and review

- Proof producer, Sol/high, cap 300 seconds; exact writes only:
  `notes/theory/2026-10-19-r112-method-member-constructor-gap.md` and
  `tasks/agent-loop/inbox/20261019-r112-proof.md`.
- Implementation lane: **NO_SAFE_ROLE_CODE_SLICE / WAITING**, using the
  existing R100 assessment at `tasks/agent-loop/inbox/20261019-r100-implementation.md`.
  R85 remains unadopted; R112 grants no implementation or test lease.
- Fresh pre-edit spec review writes only
  `tasks/agent-loop/inbox/20261019-r112-pre-spec-review.md`.
- Fresh post-output spec review and independent compiler/source review write
  only `tasks/agent-loop/inbox/20261019-r112-post-spec-review.md` and
  `tasks/agent-loop/inbox/20261019-r112-compiler-review.md` respectively.
- Luna owns central state, review adjudication, closeout
  `notes/progress/2026-10-19-r112-method-member-constructor-gap.md`, and
  explicit-path Git integration.

No test, build, compiler invocation, runtime, CLI, formatter or code edit is
authorized. Static source inspection and frozen dependency hashing only.
Fresh independent reviews must be CLEAN before closeout acceptance. A review
blocker, exact-member alternate producer route, source mismatch, missing owner
or budget exhaustion stops the packet. The report must remain an obstruction
proof or a precise falsification; do not silently narrow it.

## Resources and breadth

Total cap: 600 seconds: proof 300, pre/post spec review 60, compiler/source
review 180, Luna closeout 60; Astra 0; executable command budget 0. R111's
spent or unknown resource use remains charged and is not reset or returned.
Preserve three inherited UNKNOWN identities, board quarantine, and the legacy
slot reservation.

This advances one method/role source-to-HIR boundary. Keep the six effect-
hygiene fronts, runnable ordinary/effectful surface, original claims and
adoption gates open. At the next sprint boundary, rotate to an under-covered
effect-hygiene front or a safe runnable source slice; do not repeat this exact
entry or continue method/role by default.
