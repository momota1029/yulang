# Independent review: formal permission projection r8-r2

## Recorder provenance

The assigned reviewer `/root/formal_permission_projection_r8_r2_review` had a read-only role and returned this review in its final response. The primary recorded the response at the primary-owned review path; no reviewer file write is claimed.

## Verdict

**ACCEPT as conditional, incomplete static source evidence. No BLOCKING, major, or minor findings. STOP.**

The submission investigates the forest invariant at its mutation owner; it makes no compiler repair or theorem-closure claim.

- The local production write inventory agrees with the admitted code: default initialization, self-parent births (`candidate_intrusion.rs:342,348`), merging (`:679,691`), compression (`:536–565`), reverse journal restoration (`:203–215`) and truncation (`:222–223`). Whole-state replacement and lifetime provenance remain explicitly outside that inventory.
- The closed finite forest lemmas are valid with their stated hypotheses. Missing-entry fallback establishes syntactic idempotence without establishing row validity. Merge preservation requires distinct in-range self-roots **at the write**. Conditional rollback requires complete, correctly ordered inverse entries paired with their checkpoint; reverse replay and truncation alone do not establish that premise.
- `candidate_opposite_count` at `candidate_intrusion.rs:639` is the first missing **direct callee body on the visible bound-copy path**. Restricted searches of all eight admitted source files found only the reported count/read/insert callsites. Its declaration owner and receiver signature remain unobserved. This finding does not certify transitive journal/resource helpers.
- The prospective inverse entry at `:624–630` precedes intervening helpers. Consequently journal ordering and root stability cannot be inferred from the enclosing mutable receiver.

The exact remaining equation is:

> Given distinct, in-range same-kind roots `r,s` selected at `:613–619`, immediately before `:679/:691`, their entries still exist and satisfy `F(r)=r`, `F(s)=s`; every effective intervening forest mutation has the correctly ordered inverse entry for the associated checkpoint.

Closing it needs authenticated source evidence for the intervening calls and journal association. No new owner path was inferred or opened.

No r7 premise is removed. B, D, reachable forest/lifetime preservation, r1 Lean verification, original parent A/B, source/native, full inference/executor and production gates remain **OPEN**. No reachable counterexample was established.

## Authentication

Every SHA-256 below matched:

| Input | SHA-256 |
|---|---|
| Reviewed r8-r2 | `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9` |
| Original r8 contract | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` |
| Amendment 01 | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` |
| Original r8 STOP | `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8` |
| Actual r7 outcome | `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8` |
| R7 contract | `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767` |
| R7 source | `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d` |
| R7 review | `635e94a1eec04348fdd87b7c1802101bca10a6fa8631e3e82d0eb39f26a12c7c` |
| candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| candidate_effect.rs | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| candidate_scheme.rs | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| shadow_apply.rs | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| term.rs | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| Playground scheme.rs | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Reviewer session: `/root/formal_permission_projection_r8_r2_review`. Model/effort UNKNOWN; exact total runtime/RSS/CPU UNKNOWN, charge the full 120-second review grant. Static reads/hashes only; no writes, tests, builds, probes, Cargo, Lean, Git, network or descendants. STOP; no active work remains.
