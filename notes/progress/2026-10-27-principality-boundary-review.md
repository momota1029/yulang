# Independent review: original principality formulation boundary

Date: 2026-10-27. Reviewer: `/root/soundness_hygiene`.
Task: independent read-only review of the frozen principality module and note.
Verdict: **PASS for the stated interface-countermodel scope; no blocking
findings. Original Yulang principality remains OPEN.**

## Frozen review objects

| Object | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalPrincipalityResolution.lean` | `006cf46593e608d73ff5618b35f85623d984f4401852864911e7b9443cb351c3` |
| `notes/theory/2026-10-27-original-principality-resolution.md` | `5b61e921758faa5d51cc87223e7cbe6d019d114fa190f0c835b8154441ffa674` |

Both hashes were checked before inspection and again after the independent
checker/audit. Neither target was modified. No imported source, original
instance order, compiler, shared status, root import or configuration was
changed by this review.

## Source and premise inspection

The review read the complete 216-line module, complete 271-line note, and
every declaration type/axiom report from an independently generated audit.
It also inspected the actual governing definitions and source owners:

- `SourcePrincipalTransport.hCall`, `hName`, `xName`, `bodyContext`, and
  `h_call_complete_rule`;
- `OriginalSourceGeneration.sourceRules`, the original Kernel fields,
  `Judgment.existsE`, local checking and Name child construction;
- `Contracts.SourceProblem`, `InferenceSoundness`, `SourceScopedCoverage`,
  and the unchanged `PrincipalCoverage` quantifiers;
- `2026-10-13-intrusion-source-preservation-proof.md` §§1, 3 and 5;
- `2026-10-06-source-call-generation-construction.md` §5;
- `2026-10-26-native-call-certificate-introduction.md` §§6 and 9.

The latter two sources explicitly retain the independent complete Call
certificate and authentic `Q_16` declaration/accessor obligation. The new
module does not turn either an unresolved declaration or an interface atom
into an original semantic law.

## 1. Site 16 retains its actual existential environment and view

`CallBoundary.h_call_requires_certificate` rewrites only by the already
proved `h_call_complete_rule`. It then inverts the actual outer
`Judgment.existsE` and the actual App `Judgment.rule`. The result retains the
same `candidate : ScopedValue Value` in both:

```text
kernel.admitted environment (16, viewLogic, 0) candidate
kernel.atom (environment.extend (16, viewLogic, 0) candidate) certificateAtom
```

The certificate is exactly `completeCallCertificate` at site 16, the existing
`bodyContext`, and operands `[17,18]`. There is no separately chosen view,
reconstructed earlier environment, per-port witness, or altered context.
The existing `Environment.extend` at `.viewLogic` also preserves its original
runtime event path and replay state; the proof does not manufacture a runtime
invocation by extracting a logical binder.

The positive half of `h_call_iff_certificate` constructs its witness from
the existing environment root and current parent path. This is legal in the
deliberately trivial interface admission. It constructs every original App
local premise, including both checks, and both actual Name children under
the same extended environment. It does not omit a failed source premise or
substitute a Call-only synthetic rule tree.

The two kernels agree on every other complete Kernel field function,
including the distinct source and checking admissions. `other_atoms_fixed`
establishes agreement for every non-certificate atom. The varying part is
the complete-certificate **atom family**, not a secretly modified descriptor,
Name lookup or body scope. The two Name derivations use the same genuine
original AST and binding context, but their trivial local meanings are
countermodel meanings, not authentic Yulang primitive laws.

## 2. Interface separation is not presented as original-semantic refutation

The source header, theorem comments, note's opening status, §1, and final
parent-application section consistently distinguish the interfaces from a
complete original semantic interpretation. The proof establishes opposite
source judgments only for its explicitly constructed artificial kernels.
It supplies neither an original complete Call interpretation nor a native
receiver/intrusion correspondence.

The source-shaped site-16 example therefore establishes that the inspected
interface and other field meanings do not determine that certificate atom.
It does not establish an original-language typing counterexample. The note
explicitly says that the result neither refutes original principality nor
source-qualifies a native direct-return rejection. It also avoids claiming
that no authentic declaration can exist elsewhere.

This distinction is material to acceptance: the theorem cannot be used as
the missing `TypedCallCert_Dec` construction, a proof of original source
membership, or an original source-qualified impossibility theorem.

## 3. The original principal instance order is not replaced

`OrderBoundary` fixes one artificial
`SourceProblem Unit Unit Unit Bool Unit Bool Unit` and one fixed `principal`
predicate. Its whole-witness/solution relation is actual Boolean equality.
Both Boolean witnesses retain exact solutions, so the failed discrete result
does not arise from deleting source witnesses or losing source-solution
coverage.

The two candidate instance relations are explicitly distinct test relations:
the indiscrete relation and equality. Both are proved reflexive/transitive.
The discrete contradiction obtains coverage for both `false` and `true`
from one purported principal solution. Its `sameScoped` equalities and
instance equalities imply `false = true`; there is no order reversal or
independent change of the principal predicate in that argument.

`Contracts.SourceProblem.PrincipalCoverage` itself is unchanged. Neither
test relation is installed as the Yulang instance relation, and the note
does not assert either to be that original relation. The final theorem has
the advertised limited force: exact solution coverage alone cannot choose
the missing original scheme carrier/order or prove principality in it.

## Independent pinned checks and complete audit

Both fresh checks used the resolved native executable:

```text
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake
```

The pin is Lean 4.35.0, native commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake is
`5.0.0-src+eb6cafb`. Invocations used `env lean -j1 -M1024`, without `-o`,
under the authorized escalated execution path. No imports were missing.

1. Direct check of the frozen repository source: exit 0, no diagnostics.
2. Independently generated audit containing the exact frozen source after
   the audit imports: exit 0, no diagnostics. It prints and checks every
   new declaration type and transitive axiom, including private/generated
   declarations, then explicitly runs `#check` and `#print axioms` for all
   ten public roots.

The independent census matches the producer's count: **32 declarations,
20 theorem constants**, comprising ten public authored theorems, two private
authored helpers, and their generated declarations. The audit independently
requires every public theorem and rejects any axiom outside `propext`,
`Classical.choice`, and `Quot.sound`.

| Authored roots | Actual axiom set |
| --- | --- |
| `h_call_requires_certificate`, `h_call_iff_certificate`, `opposite_h_call_judgments`, private `names_when_certificate` | `propext`, `Classical.choice`, `Quot.sound` |
| `other_atoms_fixed`, `other_kernel_fields_fixed`, private `local_when_certificate` | `propext` |
| All five OrderBoundary theorem roots | none |

The complete generated/private audit also has no project axiom, `sorryAx`,
native-evaluation assumption or checker bypass. All ten explicit public
`#print axioms` reports were produced.

## Evidence and review boundary

| Independent evidence | SHA-256 |
| --- | --- |
| `/tmp/yulang-principality-review-20261027/Audit.lean` | `0a431aec8906dcdbf47e1c58fb74460433ba23d7c9ed17fc72b507ed182da52c` |
| `/tmp/yulang-principality-review-20261027/audit.log` | `e57588cd4fc4c1038a435e9ed22c5a131843358054228019f9c42eb102c8fda6` |
| `/tmp/yulang-principality-review-20261027/complete-census.json` | `b576ecc54ae1f21e2df4306fffe30f6f2722bd24d98e7bc337984d3e803a45d3` |

The direct check output is retained in the same directory as
`source-check.log`; it is empty because the successful checker emitted no
diagnostics. `source-frozen.lean` retains the exact inspected module.

No revisions are required for the declared boundary result. Acceptance of
this interface result does not close original principality, prove a complete
source/native Call certificate, or authorize any change to the source domain
or principal ordering. The exact remaining owners recorded by the producer
are consistent with the checked source definitions and governing notes.

**Review writes and checkers stopped.** Only this leased review note and the
unique temporary review directory were written. No target edits, Git/shared
status mutations, Lake builds, `.olean` output or child agents occurred.
