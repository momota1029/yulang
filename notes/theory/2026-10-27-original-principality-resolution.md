# Original principality: checked formulation boundary

Date: 2026-10-27. Baseline: `6148fc868565617d7db6ef193a6ff164700d88f7`,
branch `yulang3`. Producer: `/root/principality`, bounded `lean_prover` leaf.
Status: **kernel-checked interface countermodels; original principality OPEN**.
Independent review: not yet performed. No compiler or semantic change.

## 1. Result and its exact force

The two missing inputs are independently necessary. The checked source rule
does not determine its complete Call certificate interpretation, and source
solution coverage does not determine the principal instance ordering. The new
[Lean module](lean/YulangClosure/OriginalPrincipalityResolution.lean) gives two
explicit countermodels at those existing formal interfaces.

These are **not two models of the complete original Yulang semantics**. The
Call models deliberately use trivial meanings for the other kernel fields;
the order model deliberately uses a two-element witness/solution set. Their
purpose is to refute two proposed logical shortcuts from the currently checked
interfaces. They do not establish that the original manuscript has two equally
authorized interpretations, that the original theorem is false, or that the
native direct-return rejection is source-qualified. There is no new empty-arm
assumption, W/Z grammar, source restriction, or replacement principal ordering.

In particular, this result cannot decide whether the missing authentic
declaration already exists outside the inspected sources or needs construction.
It identifies exactly what a purported completion must supply and proves that
the existing interface laws alone cannot supply it.

## 2. Original obligation and source ownership

The unchanged parent is
[source preservation §§1, 3, 5](2026-10-13-intrusion-source-preservation-proof.md),
with the immutable birth-level SCC correction. It quantifies over every
supported original source and lawful finite inference history, preserves one
joint scoped strategy through publication and all lawful uses, and requires the
original principal coverage, not arbitrary-model preservation.

The complete App obligation is
[G_call §5](../progress/2026-10-06-source-call-generation-construction.md#5-genuine-semantic-call-constraint-generation).
It retains `WF_Dec`, value inclusion, whole argument compatibility, the
structural callable-image computation check, `TypedCallCert_Dec`, and the
original role/incidence records at one joint telescope. `TypedCallCert_Dec`
explicitly retains supplied receipt/profile/operation/observation/correspondence
premises. The other conjuncts do not define that predicate.

The selected
[native introduction §§6, 9](../design/2026-10-26-native-call-certificate-introduction.md)
adds a genuine native constructor but still requires the authentic `Q_16`
declaration and its independent complete arm, root, result, target and future
accessors. It explicitly distinguishes receiver-local alternatives, which a
completed Function certificate can eliminate, from independently declared
whole-Call alternatives. `Strict`, `ReadInvoke`, and `EvalInvoke` formation
cannot be substituted for the latter fields. No executable declaration or Lean
implementation supplying the actual `Q_16` object was found in the inspected
source owners.

The checked source owner is `OriginalSourceGeneration.Kernel.atom`, consumed
by `Local.atom` and `Judgment.rule`. The exact existing source is
`SourcePrincipalTransport.hCall`: site 16, `h x`, at `bodyContext` containing
the genuine `y`, `x`, recursive monomorphic `f`, and captured `h` bindings.
This is also the first Call of the direct-return candidate. The new proof
reuses the existing raw source and `h_call_complete_rule`; it does not replace
the source by an invented Call-only tree.

The principal-order owner is `Contracts.SourceProblem.PrincipalCoverage`.
It still takes both `principal` and `instanceOf` as independent parameters.
The inspected original Simple-sub note §3 identifies source-derived
substitution coverage but explicitly excludes a proof of the leveled
let-polymorphic/intrusion extension. The source scheme acceptance criteria
fix required presentations and behavior; they do not instantiate this Lean
ordering. `OriginalPrincipality.joint_solution_coverage_iff` identifies an
exact algebraic solution relation and does not identify the original order.

## 3. Exact source certificate separation

All names below are under
`YulangClosure.OriginalPrincipalityResolution.CallBoundary`.

`certificateAtom` is exactly

```lean
atom .completeCallCertificate 16
  SourcePrincipalTransport.bodyContext [17, 18]
```

The original-rule inversion theorem has the following full quantifier shape:

```lean
h_call_requires_certificate
  {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
  (typed : SourceJudgment kernel environment bodyContext hCall) :
  ∃ candidate : ScopedValue Value,
    kernel.admitted environment ⟨16, .viewLogic, 0⟩ candidate ∧
    kernel.atom (environment.extend ⟨16, .viewLogic, 0⟩ candidate)
      certificateAtom
```

The witness is the actual existential view chosen by the source derivation.
Its environment is the original environment extended once at that same
telescope. The proof does not select another provider, earlier event, future,
or independent per-port witness.

For the countermodels, `kernel Value P` assigns `P` to complete certificate
atoms and `True` to every other atom. All seven other fields of `Kernel`,
including the distinct source and checking admissions, are the same complete
functions in both models. The full original `Environment Value` is unchanged.
`other_atoms_fixed` proves agreement at every non-certificate atom;
`other_kernel_fields_fixed` proves equality of all the other field functions.

The constructed positive source derivation and the original inversion give:

```lean
h_call_iff_certificate {Value : Type} (certificate : Prop)
  (environment : Environment Value) :
  SourceJudgment (kernel Value certificate) environment bodyContext hCall
    ↔ certificate

opposite_h_call_judgments {Value : Type}
  (environment : Environment Value) :
  SourceJudgment (kernel Value True) environment bodyContext hCall ∧
    ¬ SourceJudgment (kernel Value False) environment bodyContext hCall
```

The positive direction constructs the existential view, both actual Name
children, the full original App premise list and both checking derivations.
It does not erase any original premise. The countermodel's independently
chosen primitive-check relation makes those checking derivations available;
this is precisely why it is an interface countermodel rather than an original
semantic source witness.

## 4. Principal ordering separation

All names in this section are under
`YulangClosure.OriginalPrincipalityResolution.OrderBoundary`.

One `problem : SourceProblem Unit Unit Unit Bool Unit Bool Unit` is fixed
throughout. Every Boolean witness is a source judgment and every Boolean
solution solves the one generated constraint. `sameScoped` is equality of
that model's complete witness and solution. `principal` is the same fixed
predicate in both comparisons. The two instance relations are:

```lean
indiscrete : Unit → Bool → Bool → Prop := fun _ _ _ => True
discrete : Unit → Bool → Bool → Prop := fun _ first second => first = second
```

Both relations are reflexive and transitive. They are not asserted to be the
original Yulang instance relation.

The five authored theorems have these exact conclusions:

```lean
same_problem_sound_and_complete :
  problem.InferenceSoundness ∧ problem.SourceScopedCoverage

both_instance_relations_preorders :
  (∀ scope first, indiscrete scope first first) ∧
  (∀ scope first second third, indiscrete scope first second →
    indiscrete scope second third → indiscrete scope first third) ∧
  (∀ scope first, discrete scope first first) ∧
  (∀ scope first second third, discrete scope first second →
    discrete scope second third → discrete scope first third)

indiscrete_principal : problem.PrincipalCoverage principal indiscrete
not_discrete_principal : ¬ problem.PrincipalCoverage principal discrete

coverage_does_not_determine_principality :
  problem.SourceScopedCoverage ∧
    problem.PrincipalCoverage principal indiscrete ∧
    ¬ problem.PrincipalCoverage principal discrete
```

The discrete failure is not lack of a source solution: both source witnesses
have exact solutions. A single principal solution would have to equal both
`false` and `true`. This proves that choosing a relation from solution coverage
alone is substantive additional input, even after requiring a preorder.

## 5. Verification and full axiom audit

The parent owns all build/cache outputs. This worker ran only direct checking,
without `-o`, after the parent supplied the frozen import artifacts.

Observed toolchain:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean 4.35.0, x86_64-unknown-linux-gnu
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release
```

Commands used the absolute installed Lake at
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`,
`timeout 120`, `LEAN_NUM_THREADS=1`, `-j1 -M1024`:

```sh
lake env lean -j1 -M1024 YulangClosure/OriginalPrincipalityResolution.lean
lake env lean -j1 -M1024 --root=/tmp/yulang-principality-resolution \
  /tmp/yulang-principality-resolution/Audit.lean
```

The first direct check failed because case analysis on `value.kind` did not
rewrite that projection inside the kernel atom. The repair retained the
equation as `kind` and simplified it explicitly; no theorem statement changed.
The second direct check and complete audit both exited 0 without warnings.
There were three Lean proof/audit invocations in total, plus version queries.

The audit inlines the exact source bytes after the two audit imports, so no
new `.olean` is needed. It prints every new declaration's kind, complete type
and transitive axioms, including private and generated declarations produced
by elaborating source-rule equations. Total: **32 declarations, 20 theorem
constants, 10 public authored theorems and 2 private authored helpers**.
Its generated `_private.Audit` names belong to this direct audit; public names
are unchanged. Every transitive dependency is checked against the allowed set.

| Authored theorem | Complete axiom set |
| --- | --- |
| CallBoundary.h_call_requires_certificate | propext, Classical.choice, Quot.sound |
| CallBoundary.other_atoms_fixed | propext |
| CallBoundary.other_kernel_fields_fixed | propext |
| CallBoundary.local_when_certificate (private) | propext |
| CallBoundary.names_when_certificate (private) | propext, Classical.choice, Quot.sound |
| CallBoundary.h_call_iff_certificate | propext, Classical.choice, Quot.sound |
| CallBoundary.opposite_h_call_judgments | propext, Classical.choice, Quot.sound |
| OrderBoundary.same_problem_sound_and_complete | none |
| OrderBoundary.both_instance_relations_preorders | none |
| OrderBoundary.indiscrete_principal | none |
| OrderBoundary.not_discrete_principal | none |
| OrderBoundary.coverage_does_not_determine_principality | none |

There is no project axiom, `sorryAx`, unchecked native evaluation, or kernel
bypass. The changed source scan has only the ordinary `admitted` identifiers
among the broad `admit` substring matches.

## 6. Parent application, residual owners and frozen receipt

The original principality parent remains OPEN. The two countermodels block
closing it by treating a supplied certificate atom as constructed, or by
renaming joint solution coverage as principal coverage. They do not reduce
the original source domain, add a production guard, or resolve the native
signed-occurrence/receiver association. `FiniteCopyClosure` and the regular
two-use obstruction retain their existing source-qualification boundaries.

The exact next supplier is the source/complete-operation owner: the authentic
`Q_16` declaration at this actual App, including its typed arm-to-root,
result/target and future maps, followed by the same construction at the other
six direct-return Apps. A declaration-local validity proof may supply these
by projection if it already retains them. The principal theorem owner must
also instantiate the original scheme carrier and one whole-scheme instance
relation, then prove the coverage theorem in that relation. The independent
native owner still owes the actual source/retained-store/signed-occurrence
correspondence before a native rejection can refute the original claim.

Frozen files and evidence:

| Path | SHA-256 |
| --- | --- |
| `lean/YulangClosure/OriginalPrincipalityResolution.lean` | `006cf46593e608d73ff5618b35f85623d984f4401852864911e7b9443cb351c3` |
| `/tmp/yulang-principality-resolution/Audit.lean` | `03cf43af8088b2b573b0d1c17b908041a5fd6f8b6e5c4ec7449e7ab8ecaacf32` |
| `/tmp/yulang-principality-resolution/audit.log` | `cdeccb6230ed8d9f975d73aa8a1529aa0164585f9293037a22c016f5b6d64464` |
| `lean/YulangClosure/SourcePrincipalTransport.lean` | `ab86c4448dcddcb5e20ef1495e317c4d0fc04ad0ff52c4323779d12f5fde33ee` |
| `lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `../design/2026-10-26-native-call-certificate-introduction.md` | `4bc85d85d7db48ee4d17f18e299ba2a6ecb24747e0078717009201faaed0c632` |
| `../progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |

Only this note, the leased Lean module, and the two listed scratch audit files
were written. No Git, compiler, imports, configuration, dependency or shared
record mutation occurred. **Producer writes stopped** after freezing this
receipt. Parent owns integration, source-premise resolution, independent review
and any further assignment.
