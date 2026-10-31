# R4 amendment 02 independent review receipt

Verdict: **accept the shared first unsupported edge as bounded receipt evidence
only**. Neither supplier nor any parent/native/production gate closes. The
review validates receipt consistency, not producer execution history or
underlying source bodies.

## Bounded result and open obligations

The frozen r4a1 proof and r4a2 source receipts independently report that, when
the direct callee is a `Name(ModuleDef(t))`, the current `suppliers()` branch
retains both module supplier requests. They do not establish authentic
`E0/D_pub/Reg(C)/I_C/theta_C`, exact occurrence lookup, branch-specific use,
HIR admission or complete Call typing. Target identity and native-port
validation alone do not supply these premises.

The source handoff reports zero body coverage for `candidate_source.rs`,
`shadow_apply.rs` and `lib.rs`. Receiving/export construction, fieldwise
source/native interpretation, transport and lifetime remain unverified. The
first unsupported edge is accepted only as a bounded audit lead: actual typed
entry/lookup/admission is unsupplied before receiving/export correspondence.

All named suppliers remain OPEN, as do `ModuleContractRoot*`, complete Call
telescope/effects, `Sig`, `Phi_u`, N-Transport, F1/FK1, callback → Call result
→ tuple `left`, original A/B, soundness, principality, termination and
production. Preserve `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE`.

The r4a1 source receipt is a primary dispatch error only: the dated preflight
path caused checksum exit 1 before preflight or any body read. Its complete
350-second grant remains charged; it has no semantic weight. The r4a2
amendment corrects the script path; primary and source receipts report the
same corrected path and successful 21/21 preflight.

## Pins and read coverage

All five supplied pins matched before and after inspection:

```text
r4a1 proof       6cf112381cc575ff2bdd5d4f8c0823a79c26d888e52c03bf6c369325a579814f
r4a1 source      2692c3800af58e7abe130d64abdd54db29eb0b8886fc4fc6ac6466a537f46b70
r4a2 amendment   3b8c408a97197777c0e40a9f293a35149d1ede70869c69f9ae53662060092f91
primary receipt  64c77475362bf7f1bd171816d2718c82235236671c263adf785b0b274be6ec39
r4a2 source      e219b4210ba24fd97d15b128be67ae07242e6d34acca8a5bdede32d25ffb1e1e
```

Receipt reads reached EOF in separate <=4,096-byte ranges:

| Receipt | Byte boundaries |
|---|---|
| r4a1 proof | 0, 4096, 8192, 12288, 13646 |
| r4a1 source | 0, 3897 |
| r4a2 amendment | 0, 4096, 5009 |
| primary preflight | 0, 635 |
| r4a2 source | 0, 4096, 8192, 12288, 16384, 17979 |

This review did not inspect source/design implementation bodies or producer
tool histories. The producer's actual page sequence is therefore not
independently authenticated. The reviewer initially bundled the four proof
receipt ranges, then reread them separately; an attempted `python` read failed
and a `python3` read succeeded. These deviations remain recorded.

The source's observed interval is at least 242.098 seconds against its
350-second grant, with startup uninstrumented; exact total elapsed is unknown.
No cap compliance claim is made. Reviewer clock samples were 04:22:17–04:23:03
UTC (46 seconds observed); startup/final-report time and CPU/RSS are unknown.
The full 200-second grant is charged. No writes, tests, builds, Cargo, Lean,
Git, descendants or background work occurred in review.
