# Independent review: formal permission projection r3

Verdict: accept as qualified static source evidence. No blocking, major or
minor findings in the submitted derivation. The original endpoint-image,
effect-hygiene, source/native, parent theorem and production gates remain OPEN.

## Accepted claims and boundary

The reviewer independently checked the frozen r3 handoff against its contract,
the pinned `lib.rs` and `term.rs`, and the frozen r2 source handoff. Immediate
same-branch successful read-back is supported for the exact Effect payload,
the four Function fields, and ordered Tuple elements, including interning
hits. The handoff correctly conditions this on successful wrapper return and
the handle remaining live in the same branch.

The source-derived rollback witness is valid: truncating a retained page can
allow a later allocation to reuse the same brand/index with a different
ordinal. It establishes a lifecycle hazard and refutes unrestricted persistence
of opaque term identity across rollback. It is not a successful permission
projection counterexample: no permission record/domain surviving rollback and
later successful capture/export was established.

The first remaining source premise is r2 B: preserve the owner-matching
permission record, parameter domain and original term association across
publication, rollback/replacement, capture and export. C remains open for
canonicalization/store association; D remains a successful capture/export
premise. A later successful lookup alone cannot establish original provenance.

## Authentication and execution

| Artifact | SHA-256 |
| --- | --- |
| r3 handoff | `104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956` |
| r3 contract | `f3f81eead20bf7f9229844894fa4e71ae2eb19d2a39acf14200f1f8bd452ee5e` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| r2 contract | `34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877` |
| r2 handoff | `f4a3ca3491d36e35e1d066aeafbe0e17f672e90014eeeb063b0cc6ca8a42b8d2` |
| r1 review | `a64d9bafde670a2c6e580741c8fc94e58b8d4b417c6e2768330ebf505f868203` |

Reviewer: `/root/formal_permission_projection_r3_review`, fresh non-author
`compiler_referee`; STOP after read-only review. No files, tests, builds,
probes, Cargo, Lean/Lake, Git, network or descendants. Embedded tests were
read as context but not executed. Resource measurements and observed
model/effort: UNKNOWN.

The source r3 result is accepted only as a qualified source derivation. No Lean
bridge, semantic change, implementation permission or theorem promotion follows.
