# Whole metatheory: independent narrow integration review

Date: 2026-10-26
Reviewer: `/root/termination`
Review scope: import surface, audit implementation, manifest delta, and frozen verification evidence
Outcome: **ACCEPT — narrow integration only; no blocking, major, or actionable minor findings**
Original whole-language soundness, effect hygiene, principality and inference termination: **not certified by this review**

## Independence and exclusions

The reviewer authored `OriginalInferenceTermination.lean`. Its mathematical
content, source correspondence, premises and parent-theorem status are expressly
excluded from this review. The primary assigned its independent theorem review
to `effect_hygiene`. Here the termination module is treated only as one of four
mechanically imported and inventoried modules; observing a kernel/audit receipt
is not independent certification of the reviewer's own theorem.

The other component theorems are also not re-reviewed here. This packet assesses
the three new integration files, their stated local scope, their preservation
of existing roots/settings, and the completeness of the actual verification
records. No original whole theorem or concrete `SourceProblem` instance is
promoted.

## Frozen review target

| Path under `notes/theory/lean/` | SHA-256 |
| --- | --- |
| `YulangClosure/WholeMetatheory.lean` | `a4f31fea2513b59bb27291cf96d39257b9a99b8fa13a48d329891f8d85591406` |
| `AuditWholeMetatheory.lean` | `005b57dad2e2b6659e89870972c5f4246446d2d4e7c51d439a7279b37096fdaa` |
| `lakefile.toml` | `e62c909702ea210955e7d4b1c5d19991a1997a96990f70eb398f3044a479b56d` |

All three hashes match the issued review packet and completed-check inventory.

## Import and manifest review

`WholeMetatheory.lean` imports exactly:

1. `YulangClosure.NativeScopeTransformer`
2. `YulangClosure.OriginalEffectHygiene`
3. `YulangClosure.OriginalPrincipality`
4. `YulangClosure.OriginalInferenceTermination`

It adds no theorem, instance, replacement `SourceProblem` definition or semantic
rule. Its comment accurately describes local algebra/provenance/quotient/control
components, explicitly leaves callback/global inference progress open, and
retains the original source domain, complete Call, shared scoped witnesses,
lawful future uses and native correspondences. The title's whole-metatheory
reference is identified as the original *obligation*, not as completed closure.

The TOML was parsed independently and compared with baseline
`a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`. Its only semantic delta is appending
`YulangClosure.WholeMetatheory` to the existing `lean_lib.globs` list.
`defaultTargets = ["YulangClosure"]`, all three prior globs, and
`moreLeanArgs = ["-j1", "-M1024"]` remain unchanged. The original
`YulangClosure.lean`, `ProofAdvancement.lean`, `InferenceProofs.lean`,
`Contracts.lean`, `lean-toolchain` and `lake-manifest.json` are byte-identical to
that baseline. There is no manifest dependency or toolchain change.

## Audit implementation review

The audit looks up each requested module's actual environment module index,
then selects constants using `env.getModuleIdxFor? name == some moduleIndex`.
It does not use namespace/name-prefix filtering. Consequently foreign namespace,
private and generated declarations are included; the differently namespaced
`YulangClosure.SimpleSub.OriginalPrincipality.*` declarations are one concrete
case covered by this mechanism.

Every selected declaration must be a genuine `.thmInfo`. Originating
`.axiomInfo` declarations cause an error; duplicate targets and empty module
inventories also cause errors. All 18 named required roots must occur in that
origin-based theorem inventory. Each theorem receives `#check @name`,
`#print axioms name`, and `Lean.collectAxioms` validation against exactly:

```text
propext, Classical.choice, Quot.sound
```

Every non-whitelisted indirect dependency causes an error. The audit therefore
does not mistake a named `Prop` definition for a theorem, or silently omit
private/generated theorems outside a preferred namespace.

The task's shorthand “complete types/proofs” was clarified by the primary:
required output is complete theorem **types**, including displayed proof-valued
indices, and complete axiom lists; full theorem proof bodies need not be printed.
`pp.fullNames`, `pp.privateNames`, and `pp.proofs` are enabled. `#check` prints
types, not proof bodies. Proof bodies are checked by the native kernel during
the build. The audit's comment already states this distinction accurately, so
no code change was needed. The completed log has no proof-elision marker `⋯`.

## Independently reconciled execution evidence

The primary ran the checks; this reviewer launched no redundant Lean/Cargo
process and did not write to the primary's build cache. The frozen receipt
identifies Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

- `lake --no-cache build`: exit **0**, **105 jobs**, owner-recorded 435.8 seconds.
  The raw log includes successful `YulangClosure.WholeMetatheory` compilation
  and the final 105-job success line.
- `lake --no-cache env lean -j1 -M1536 AuditWholeMetatheory.lean`: exit **0**,
  owner-recorded 7.4 seconds. The audit's local memory allowance changes no
  manifest proof-build limit.

The reviewer independently parsed the raw census, checked unique alternating
BEGIN/END records, required a full named type and exactly one complete axiom
report in every record, reconciled the final count, checked all 18 unique
required roots, and rejected every non-whitelisted axiom set. Results:

| Originating module | Theorem constants |
| --- | ---: |
| `NativeScopeTransformer` | 107 |
| `OriginalEffectHygiene` | 24 |
| `OriginalPrincipality` | 36 |
| `OriginalInferenceTermination` | 75 |
| **Total** | **242** |

| Exact axiom dependency set | Constants |
| --- | ---: |
| none | 74 |
| `propext` | 33 |
| `propext`, `Quot.sound` | 122 |
| `propext`, `Classical.choice`, `Quot.sound` | 13 |

There are zero audit warnings/errors and no missing, duplicated, unbalanced,
truncated, or elided theorem records in the inspected log. All 18 required
roots are present. These mechanical facts do not discharge theorem hypotheses
or omitted original source/native obligations.

The ordinary default build has **668 warnings in nine existing files**, and
zero error lines. The reviewer independently counted those warnings and
compared each warning-owning file byte-for-byte with the assigned baseline:
all nine are unchanged. No new integration/component file owns a warning.
The distribution is 23 `PaperExecutionSyntax`, 235 `PaperExecutionBinderLaws`,
3 `ControlComposition`, 96 `PaperTermSubstitution`, 4 `PaperCoreStep`,
276 `PaperTypeBetaExecution`, 22 `PaperTupleSplitExecution`,
2 `PaperPerformLetExecution`, and 7 `NativeIntegerComparison`.

The **164-input** inventory exactly equals all current nonignored Lean source
files plus `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`: no missing
or extra entries. All 164 current hashes match after the completed checks.

## Evidence hashes and exact copies

The following frozen files are under
`notes/progress/evidence/2026-10-26-whole-metatheory/`:

| Evidence | SHA-256 |
| --- | --- |
| `whole-default-build.log` | `8943f3a2ac04dbed0511db345124d417ef378c4db5d8358af63948214480552b` |
| `whole-audit.log` | `bae70a7f09b26cea1db092f75561546bb5fe085b8653c666f07a3d777a802ab4` |
| `integration-input-hashes.json` | `56badefc5d6ad94b1059762fb8810cdae647e2bef9d5501d39d592f3d133d391` |
| `verification.json` | `bd30db9eb83f971d7c040b1282e5cfb225eb18ea0ceb0cf1db14b9e01a2debf5` |

Each hash was independently recomputed. Available corresponding copies in
`/workspace/scratch/e3678bef96db/proof-checks/` are byte-identical. Raw logs,
not just `verification.json`'s summary, were independently reconciled.

## Conclusion and cessation

Accept the frozen import surface, originating-theorem audit and sole manifest
glob addition at the stated scope. No repair or broader recheck is requested.
This acceptance adds no whole-language theorem, compiler behavior change,
source-domain restriction, production authority or independent certification
of the reviewer's own termination content.

Only this review receipt was written in this packet. No source/configuration,
shared status, test expectation or Git mutation occurred. No children or new
verification subprocesses were launched. **Writes stopped at submission.**
