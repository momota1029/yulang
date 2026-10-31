# EFFECT-PERMISSION-NATIVE-DECODE/20261029-r4 outcome

Status: **CLOSED INCOMPLETE**. The bounded mathematical construction was written and source/code correspondence was added, but the only authorized focused audit failed before theorem checking.

## Frozen construction

- Lean artifact: `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedNativeDecode.lean`, 11,294 bytes, SHA-256 `10f28441b17b8900f2d21bde3c0bfee83549214c464eb2e48178cafd3e3add10`.
- Proof handoff revision 2: `tasks/agent-loop/inbox/effect-permission-native-decode-r4-proof.md`, 14,743 bytes, SHA-256 `ab0ea610990fd7cf652b22ee0ca3639d7a47e007824edfea61c3056488f02fc1`.
- Independent review: `tasks/agent-loop/inbox/effect-permission-native-decode-r4-review.md`, 2,867 bytes, SHA-256 `3044722c01ee4888d3a74b7de3db85c4978d1f17185117ba848230ac0152960e`.
- Frozen input manifest: 45 entries, SHA-256 `b36ac6d4f1463a3e085c7aa11dea7b0c9fa39037213bfc2c4f7293811bf1af84`; all entries and all 12 isolated project copies were reverified.

The construction contains 13 declarations, including the injective Int/Unit tag encoding, full source inventory and four-port order, explicit `encodeSource` projection with `code_from_exact_source`, four allocation births, retained rows, exact expected observations, irrelevance from the other seven State coordinates and tags, and application of the unchanged extracted theorem to both paths with one output. These declarations remain **UNCHECKED**. The built imported modules and static review support the intended bounded model, but no Lean proof closure is claimed.

## Single audit receipt

Audit-input revision 3 was frozen at 4,202 bytes, SHA-256 `7a3118f686840ecf2858acf17d949eb79b869b95557b5bfa24d4cfa7bbade5d2`. The primary issued one exact checker release. It exited 1 after building eight imports because the target module has documentation comments immediately before `mutual` blocks; Lean 4.35.0 reported `unexpected token 'mutual'` at 42:81 and 66:82. The theorem-type and axiom-audit stage was not reached. No retry or source repair occurred.

Raw files in `/tmp/yulang-effect-permission-native-decode-20261029-r4/lean-project/`:

- `audit-stdout.txt`: 4,563 bytes, SHA-256 `ed2adf256bb2c445b4df2526b58086ff0945e37ab121ce04018619fdf6d6eba2`.
- `audit-stderr.txt`: 33 bytes, SHA-256 `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60`.
- `audit-status.txt`: 2 bytes (`1\n`), SHA-256 `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`.
- `audit-time.txt`: 2,495 bytes, SHA-256 `9398d3b56732b7787b02e05e5fdd717b9ab3325ef233c9f00f6a47027f9890a7`.

The invocation took 10.51 seconds wall time and peaked at 780,860 KiB RSS. It used Lake 5.0.0-src+eb6cafb and Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The one-audit allowance is spent.

## Review and disposition

Fresh `compiler_referee` review returned **BLOCKING for proof acceptance**. It found no additional concrete construction defect in the uncompiled artifact, independently checked all 45 manifest entries, 12 copies, artifact/handoff pins, and four raw receipt hashes, and confirmed the exact source/code projection. Its read-only dependency scan found no proof holes, project axioms, or checker bypasses; that scan does not replace the unavailable theorem axiom audit.

The minimum next work is a newly bounded packet that moves the two documentation comments or changes them to regular comments, freezes new source and audit inputs, and obtains a successful exact theorem/type/axiom audit. The raw audit evidence and failed construction remain preserved. No parent or production claim follows.

The original parent, source/native authenticity, effect hygiene, consumer residual, unequal transport, soundness, principality, termination and production gates remain **OPEN**. This outcome closes R4 incomplete only.
