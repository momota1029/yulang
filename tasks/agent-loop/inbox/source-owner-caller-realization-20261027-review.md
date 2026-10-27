# SOURCE-OWNER-CALLER-REALIZATION-20261027/r1 — independent review

Verdict: **accept the source-analysis obstruction report; classify the implementation as FAILED_INCOMPLETE.** No trace was emitted, no Lean theorem was checked, and every original parent gate remains OPEN.

Fresh non-author review by `/root/source_owner_caller_review`. I inspected the adapter, schema, direct owners and governing source definitions before using the handoff explanations. Review remained read-only.

| Artifact | Independently computed SHA-256 |
| --- | --- |
| Amended contract | `9c6bb17280250a83c68f42cc17dc32ccc331e60a7f5290af1d942b5e139432e6` |
| Final adapter | `4652e48fe3305d34c9d271f3a711cee97785a1d167ca19d4a4b01c147e775620` |
| Raw schema | `9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9` |
| Implementation handoff | `ef6f432176dfc18a98e53cd0a973bf7a8a5389f1e452a654db3393c1d8b15ed4` |
| Proof handoff | `c8753e755272225c278f02bc562ff284cff5ff3c32abd4b7dfef21b39f8e989b` |
| Call 1 receipt | `377869945801aa8a39c892fa0064d05daf9bdde153b03d63d65d0fe7e6b4d6bc` |
| Call 2 receipt | `0ccd23419fffeebdf042b28115e63fb486ba07006bae72ac4b2b50b7a84852fb` |
| Call 1 wrapper | `0ce1f3a621f877908ec7553b6468ff22260911f38727ee16d439ef0d3725c36c` |
| Call 2 wrapper | `343b07868e5c4bccb5ceb33996bc70f1ee1dead193523d08fc277e566aa6115d` |

All 56 inherited entries and ten source-map entries independently rehash unchanged. Their manifest hashes match the proof handoff. The intended trace, repository consumer and audit module are absent.

## Major finding: provider artifact compatibility was assumed

Location: `original_caller_reify.rs:107–111`, particularly line 110.

The adapter requires `ShadowArtifact::from_parsed` for every provider before constructing provider indexes or resolver joins. The existing exact-provider fixture at `module.rs:4817–4836` only constructs `SourceExportIndex`; it establishes no successful `ShadowArtifact` construction. `shadow.rs:1671–1680` rejects a failed/nonempty syntax-diagnostic projection, whereas an unsupported skeleton is retained separately rather than propagated by `from_parsed`. The saved call-2 stderr confirms this new precondition fails for the first provider. The `expect` also omits the provider label and actual parser diagnostics. Consequently the resolver joins, complete root inventory and foreign-owner assertions were never executed.

Minimum closure: in a separately admitted execution packet, preserve the exact provider diagnostics and establish an appropriate parse-owned locator path or demonstrated artifact compatibility. Any fixture change requires explicit scope adjudication. This failure supplies no compiler semantic counterexample.

## Minor findings

### Call-1 envelope evidence is incomplete

Location: `impl/run1.sh`, `cargo-call-1.receipt.txt`; contract lines 108–116. The receipt records argv, environment hash, UTC interval and Cargo status, but no observed affinity, inherited limits, explicit wall duration or wrapper-status field. Run2 remedies these omissions: observed CPU 0, inherited 120 CPU seconds/1 GiB address space, wall time 0.964 seconds and child/wrapper status 101 are retained. Qualify call-1 enforcement as unverified by its saved receipt; no actual limit violation is established.

### Cargo generated output outside the assigned scratch root

Location: both wrapper scripts’ Cargo commands; implementation handoff lines 104–106. Both preserved environments omit `CARGO_TARGET_DIR`; the handoff records generated `tools/inline-authentic-extraction/target/`. This exceeds the contract’s implementation scratch-root convention. Record Luna’s disposition for that known generated directory and set an explicit scratch target directory in future packets. No source-file damage is established.

### Stale final handoff instruction

Location: implementation handoff lines 115–116. It says final Cargo acknowledgement remains pending, although lines 76–111 record call 2 completed and the budget exhausted. Correct through a versioned addendum or outcome qualification.

## Scope and source correspondence

The bounded retry was explicitly authorized by the amended contract. The final source uses the existing diagnostic helper at the compiler-reported conversion sites and the owner-defined `SyntaxKind::UseDeclaration`. Call 2 compiled successfully, so those reported compilation causes were repaired. No third execution fits the authority. A complete byte comparison with call-1 source was unavailable because only its hash, rather than a preserved full source copy, is recorded in the inspected scratch set.

Static inspection supports the intended authentication design: root inventory compares CST/HIR cardinality, exact keys/ranges and order; resolver rows join aliases to exact `SourceExportId`; imported LocalSource occurrences join back to resolver identity; rejection checks precede the single write at line 588. These are **unexecuted candidate checks** in this packet. Both stdout files are empty, and call 2 fails in `owner_modules` before those checks.

The proof handoff accurately delivers a constructed, unchecked data schema and zero checker executions. The schema contains raw provenance and consistency definitions, without constructing an original Context or semantic certificate. There are no delivered theorem types or axiom audits to accept.

The interpretation boundary is supported by the actual definitions. `OriginalSourceSyntax.lean:188–198` requires every Binding field. The authoritative source §3.3 distinguishes external Mono/Published/Family evidence at their owning rule. `source_exports.rs:1–4` explicitly assigns no type-level meaning, and `with_caller_evidence` validates no opaque payload meaning. The required export-identity-to-Binding interpretation remains missing. The complete import-root elaboration follows separately: `Source` has no raw import constructor, and `moduleS` supplies no adopted import meaning. Actual root route, ambient scope and runtime `OwnedFrame` provenance remain OPEN.

Review stopped. No repository/scratch writes, Git operations, Cargo, Lean/Lake, tests, build, formatter or descendants were started. All read-only review commands completed.
