# Independent review: guarded finite lattice certificates

Date: 2026-10-26. Reviewer: `/root/lattice_review`, fresh nonauthor reviewer.
Mode: M3, one assigned independent reviewer. Assigned current baseline:
`458f5e2`; originating packet baseline:
`eb3eef2f6a29d9c2a6132d648866c60900db276c`.

## Decision and frozen scope

**ACCEPT for the stated proof-side guarded graph fragment.** No blocking,
major, or minor findings. This accepts the certificate/independent-interpretation
theorems and their explicit finite-rule correspondence, not original whole-source
inference soundness, completeness/principality, native correspondence, ordinary
coalescing, or full Call/effect semantics.

The reviewed repository outputs are:

| Path | Reviewed SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |
| `tasks/agent-loop/inbox/20261026-inference-lattice-certificates.md` | `cc522bdeb4e67bc4c2ac8575b7cfa5586730e5db5bf7da07c947d58279edc732` |

Read all 821 lines of the proof and the complete handoff. The proof copy used
by the producer's isolated project is byte-identical to the reviewed repository
source. The five imported repository sources and isolated copies also match
the hashes recorded in the producer handoff: `Contracts`,
`SimpleSubConstraintSyntax`, `SimpleSubConstraintSoundness`,
`SimpleSubRegularSolutions`, and `SimpleSubRegularConstraintSoundness`.

No later consumer packet, root-import change, shared status update, compiler
change, or production integration is covered by this review. New consumers
require their own actual theorem/source assessment.

## Authority and source review

Applied `AGENTS.md`, `AGENTS.pre-sprint.md`, the repository
`yulang-lean-proofs` skill and its source/execution guides, design-authority
rules, the M3 review contract, and the relevant goal-driven sprint boundaries.
Read the original parent claim in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1 and 3,
the Authoritative top-level inference principles, and the immutable-birth
qualification correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6.

The original parent still quantifies over every supported original source
program and lawful finite construction history, retaining source/type/event
scopes, recursive sharing, generalization and lawful uses, full Call, hygiene,
and jointly chosen evidence. Nothing in this packet proves or narrows those
quantifiers.

Inspected the producer's actual primary-source copies, whose hashes match the
handoff: Parreaux's *The Simple Essence of Algebraic Subtyping* (2020),
Fig. 10 and §§5.1–5.3, printed pp. 124:24–27; and pinned
`LPTK/simple-sub` commit `9bae772624c23b52a93c1b226157e16898b4d9db`,
`Typer.scala` (`constrain`, `extrude`, `coalesceType`) and `syntax.scala`.
The paper explicitly permits unguarded recursive syntax while delaying
recursive hypotheses until a Function/record step. The new acceptance
interface checks a guarded graph fragment; the handoff correctly does not
identify that fragment with all Fig. 10 syntax or impose it on source programs.
The paper's non-let proof-sketch scope and its ordinary/unifying-coalescing
distinction also remain explicit.

The exact finite compatibility target is the existing
`SimpleSubConstraintSyntax.Sub`, whose constructors were read directly.
Record width, optional-field admission, contextual effects, and the paper's
entire recursive judgment are not silently imported into that local relation.

## Mathematical and implementation findings

### Recursive uses are structurally guarded

`Layer graph relation pair` is inductive. Its `structural` constructor is the
only constructor whose premises use `relation`. Those premises are exactly
the children returned by `structuralExpand`, which delegates to the unchanged
`Regular.expandNodes` after both endpoint lookups find structural nodes.
Every union/intersection rule and transitivity rule consumes smaller finite
`Layer` derivations at the same depth. Reflexivity requires an existing node;
there is no constructor admitting arbitrary table membership directly.

`Derivation` is a finite inductive witness tree. `checkDerivation` mirrors
these rules and consults the finite table only in its structural case. Its
transitivity witness explicitly carries the intermediate identity. The two
inductive proofs establish exactly:

```lean
(∃ proof, checkDerivation graph table proof pair = true) ↔
  Layer graph (fun child => child ∈ table) pair
```

This is finite witness completeness for the declared Layer rule language;
it is not source inference completeness or complete recursive subtyping.

### Soundness does not define meaning by acceptance

`Approx graph 0 pair := True` and
`Approx graph (n+1) pair := Layer graph (Approx graph n) pair` are defined
before the certificate interface. `RegularSub` requires all finite depths.
`Layer.mono` supports a direct induction on depth proving `coinduction` for
any postfixed relation. Thus the meaning is independent of checker acceptance.

`checkCertificate_postfixed` obtains a derivation for every member of the one
shared table. `certificate_sound` applies the general coinduction theorem to
that table relation. Its only substantive premise is successful checking of
the finite certificate. It requires no terminal model, source typing proof,
finite readback, assumed preservation law, or `LocalLaws` instance.

The printed accepted-demand theorem has exactly this shape:

```lean
accepts graph certificate demands = true →
  graph.Valid ∧ graph.Guarded ∧
    ∀ pair, pair ∈ demands → RegularSub graph pair
```

`accepted_joint_relation` additionally exhibits one relation over the complete
kind-indexed comparison set, containing every demand, postfixed under Layer,
and included in `RegularSub`. Its actual witness is membership in the same
checked table. No separately chosen relation per demand or per effect port
enters the proof.

Only `regular_fold` is proved for the new all-depth relation. The source and
handoff correctly avoid claiming a reverse unfolding theorem that would need
one common finite derivation across depth-specific witnesses. The new
transitivity theorem composes finite derivations at each shared depth.

### Guards and existing structural meaning

`FiniteLattice` is an independent inductive assertion that all lattice-only
branches end at structural nodes. `checkFinite_sound` follows the fuel
recursion, and `checkGuarded_sound` covers every in-range node of both kind
tables. `checkGraph_iff` separately enforces actual references and existing
label/tag uniqueness. A structural cycle remains permitted; a lattice-only
cycle cannot acquire a finite `FiniteLattice` witness. No guard-checker
completeness or production cost theorem is claimed.

The reused `expandNodes` preserves Function ports with variance `(-,-,+,+)`,
including both effect ports. Records keep exact labels and optional bits;
tuples keep ordered arity; variants keep exact tags and complete ordered
payload lists. No structural port or metadata is erased by the extension.

`ofRegular_lookup` preserves every original graph identity and structural
node. `ofRegular_expansion` is an equality with the old expansion;
`ofRegular_layer` and `ofRegular_sub` prove inclusion of the old relation.
Validity and guardedness are preserved. The claimed direction is one-way;
neither the source nor handoff asserts equality of the two relations.

### The finite Sub bridge remains conditional and honest

`structuralTerm_sub` derives the actual finite `Sub` rules through the
existing expansion/`NodeRel` equivalence. The tuple, record, and variant
lemmas preserve their full constructor metadata, and Function uses all four
properly directed child comparisons.

`ReadbackAgrees` contains exact constructor equations, not an assumed
subtyping or preservation law. The complete printed type of `Layer.toSub`
retains both necessary premises:

```lean
ReadbackAgrees graph read →
  (∀ pair, relation pair → ReadSub read pair) →
    Layer graph relation pair → ReadSub read pair
```

Its proof handles every Layer constructor using the corresponding existing
finite `Sub` constructor. A finite readback is not constructed for cyclic
graphs and need not exist. This lemma is not used by `certificate_sound`,
`accepts_sound`, or the cyclic example. Accordingly it does not smuggle a
recursive source-model theorem into certificate acceptance.

### Examples exercise the intended distinction

The accepted cyclic example traverses union and intersection result nodes
before returning through actual Function roots. The certificate contains
the argument and effect obligations, and deleting the effect comparison
causes rejection. Both actual effect ports are checked by the unchanged
expansion, even though this particular example uses the same comparison
for the two ports.

The unguarded example's attempted structural table discharge of a union
premise fails. Independently, its graph is rejected for every finite
certificate and demand list. These are appropriately scoped guarded-fragment
checks, not a claim that the original paper rejects all unguarded syntax.

## Verification evidence independently inspected

The assigned budget permitted zero checker reruns absent a concrete need.
No such need arose: this review ran no Lean/Lake invocation, build, Rust test,
benchmark, native inference experiment, or cache mutation. Verification here
is independent mathematical/source inspection plus validation of the frozen
producer receipts.

Read `project/AuditLattice.lean` in full and inspected every printed theorem
type and axiom result in `check07-audit.log`, including private and generated
declarations. The audit enumerates `.thmInfo` constants by originating module,
rejects project axioms in that module, checks its required theorem roots, and
checks transitive axioms against the standard whitelist. A separate read-only
log check confirmed 153 unique begins, 153 corresponding ends in the same
order, 153 corresponding axiom results, and final count 153.

| Actual reported axiom set | Theorem constants |
| --- | ---: |
| none | 63 |
| `propext` | 65 |
| `propext`, `Quot.sound` | 25 |

There is no `Classical.choice`, `sorryAx`, native-evaluation assumption, or
project axiom in these reported dependencies. A read-only scan of the exact
six-module source cone found no `sorry`, `admit`, `axiom`,
`debug.skipKernelTC`, or `native_decide` occurrence.

The project pin/configuration remain Lean 4.35.0, no external packages,
`-j1 -M1024`. The producer's native executable is
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
The preserved focused build command in `check06.log` is
`lake build +YulangClosure.SimpleSubLatticeCertificates`: exit 0, 3.320 seconds,
no warnings. The preserved complete audit command is
`lake env lean -j1 -M1024 AuditLattice.lean`: exit 0, 1.629 seconds.
The reviewed runner limits each invocation to 120 seconds and one Lean
thread, terminating its process group on timeout. Earlier failed logs remain
available and are not represented as successful checks.

Frozen evidence under `/workspace/scratch/f98087c7ac1a/inference-lattice/`:

| Evidence | SHA256 |
| --- | --- |
| `check06.log` | `1626148e1e081e3456bd1f58f6a2ade51c5916d53c4e77c80ba865022911aa56` |
| `check07-audit.log` | `caf09b51e47b4a992f60b38fd2a8e3dd543fa86e88c2e43b0fbd2a400ff89683` |
| `project/AuditLattice.lean` | `35ce8612a950285bf826a5e059efe29963f1edb8e0b60f48b24ec619fb48872e` |
| `reference-sections.txt` | `0b4fd637ac76ad1bc93ceecfed93f865afed86aeab0961b7a3ab5065854acea9` |

## Parent application, exclusions, and cessation

This closes the assigned proof-side addition of finite union/intersection
derivations between guarded recursive structural ports. The next actual
constructor/consumer bridge remains the decoder, graph completion, constraint
history, and scoped-publication path over the extended graph. The existing
`RegularPublication.decodeTerm` and `RegularCompletion.completeTerm` still
explicitly reject union/intersection; their later replacements/extensions
are outside this receipt.

Native successful inference must still supply faithful kind/polarity-sensitive
graphs and finite evidence while retaining actual bounds, copy/occurrence
identity, metadata, and all original source scopes. Ordinary/unifying
coalescing correspondence and the full contextual Call/effect/source witness
remain separate open obligations. Acceptance of this packet grants no new
source restriction, runtime checker requirement, or parent-theorem closure.

Only this leased review receipt was written. No proof, import, dependency,
shared status, configuration, Git state, producer scratch file, or cache was
modified; no children were spawned. No separate review scratch directory was
needed. **Review writes stopped after this receipt.** Primary adjudication,
integration verification, record synchronization, commit, and push remain
primary-owned.
