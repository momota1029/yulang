# Lattice decoding, completion, concrete histories, and scoped publication

Date: 2026-10-26. Producer: `/root/lattice_certificates`, continuing generic
`lean_prover` leaf. Assigned branch: `yulang3`; original packet baseline
`eb3eef2f6a29d9c2a6132d648866c60900db276c`. The primary reported later integration
through `df7b991`; all actual dependency inputs below byte-match their frozen
repository sources. No Git operation was performed by this leaf.

Status: constructed and kernel-checked, with a complete originating-module
axiom/type audit. Independent review and integration of this new consumer are
primary-owned. The separate frozen lattice-certificate dependency was not
changed. Original whole-source inference soundness and native correspondence
remain OPEN.

## Frozen outputs and leases

- `notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean`, 1,461 lines.
  SHA256 `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`.
- This handoff:
  `tasks/agent-loop/inbox/20261026-inference-lattice-inference.md`.
- Owned scratch/project/cache/logs:
  `/workspace/scratch/f98087c7ac1a/inference-lattice-inference/`.

The proof file is frozen at that hash. Only this handoff was written afterward;
all writes are stopped. No other repository source, root import, shared
status/index, compiler code, test expectation, configuration, manifest,
toolchain, or Git state changed. No children were launched.

Frozen dependency manifest:

| Source | SHA256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubRegularPublication.lean` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| `SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |

## Original obligation and source correspondence

This consumes the preceding lattice construction into the actual existing
`SimpleSub.Term`, `Constraint`, `Store`, and `ScopedPublication.Published`
syntax. It does not replace original source typing with another inductive
source grammar. The parent remains the all-supported-original-source A/B
obligation of `2026-10-13-intrusion-source-preservation-proof.md`, §§1 and 3,
under the authoritative top-level inference principles and birth-level
correction. Original scopes, shared witnesses, publication, principal coverage,
progress, termination, complete Call/effects and hygiene are not weakened.

The same leaf previously read root instructions, the Lean role/skill and
execution/source guidance, the authoritative inference principles, actual
`SimpleSubConstraintSyntax.Sub`, and the primary reference paper Fig. 10 and
§§5.1–5.3 together with the pinned reference implementation. Source URLs and
freshly retrieved hashes are recorded in
`20261026-inference-lattice-certificates.md`.

This continuation read actual `SimpleSubRegularPublication` decoder and
publication proofs, `SimpleSubScopedPublication` clause-image and metadata
guards, original graph `Extrusion`/`ConstraintStep`/`ConstraintHistory`, and
existing structural completion/extension/growing-inference constructions.
The latter were read as proof patterns; their graph-indexed theorems were not
cast to the incompatible extended graph type.

The original paper allows unguarded recursive syntax while withholding useful
immediate recursive assumptions. This packet retains the frozen guarded-graph
acceptance interface and makes no claim that its guard check characterizes the
whole paper's recursive syntax or restricts supported source programs.

## What changed mathematically

Namespace: `YulangClosure.SimpleSub.LatticeInference`; completion declarations
are in its `Completion` subnamespace.

### Executable original-Term decoder

`decodeTerm` has a real branch for every existing `Term` constructor, including
`union` and `intersection`. Those branches recursively decode their two
children and find the exact lattice node of the same kind. Function decoding
preserves argument, argument-effect, result-effect and result separately.
Record decoding retains the label, optional bit and exact finite structural
tail. Tuple decoding retains the complete ordered list. Variant decoding
retains tag and the complete tuple payload list before adjoining the finite
variant tail.

`findNode_sound` proves the returned node really exists at the returned index.
`decodeTerm_found`, `decode_union_exact`, `decode_intersection_exact`,
`decode_function_exact`, and the three `prepend..._exact` theorems expose the
actual child and metadata equations. A lattice expression is not treated as a
structural row tail or tuple payload spine. That finite-shape obligation remains
explicit; no open-row, optional-admission, cast, or constructor-distribution
semantics is introduced.

`decodeTerm_rename`, `decodeTerm_congr_bounded`, and
`decode_freshen_transport` prove actual decoder transport with one reference
assignment for all variables, kinds, lattice children, and Function ports.
The freshening theorem applies the existing
`Generalization.transport_freshen`; no new allocation or generalization law is
assumed.

`decodeConstraint` and `decodeStore` operate on the actual existing Constraint
and Store types. `ClauseSatisfied` means successful decoding to a comparison
satisfying the independently defined `Lattice.RegularSub`; `StoreSatisfied`
requires every original clause. Neither is defined as certificate acceptance.
`checkStore` computes the decoder and checks a finite `Lattice.Certificate`.
Its theorem is:

```lean
checkStore graph refs certificate store = true →
  graph.Valid ∧ graph.Guarded ∧ StoreSatisfied graph refs store
```

There is no supplied terminal valuation, model, preservation law, or decoder-
success equation in this theorem.

### Concrete graph-indexed histories

The new `Extrusion`, `ConstraintStep`, and `ConstraintHistory` are indexed by
`Lattice.Graph`. Only graph-free `Copy`, `Occurrence`, `Comparison`, and
`Regular.ConstraintState` data are reused. Their old graph-dependent semantic
predicates and history proofs are not reused by casting.

New `Extrusion` has actual copy cuts, present same-node leaves, exact structural
expansion, and lattice-monotone union/intersection traversal. The structural
rule uses precisely `Lattice.structuralExpand`, preserving the old four-port
variance and complete row metadata. Lattice traversal concatenates the actual
left/right copy lists. `Extrusion.sound` proves the directed regular relation
from the retained polar copy links; it contains no assumed extrusion-soundness
law.

New constraint steps include structural decomposition, left-union elimination,
right-intersection introduction, reflexive discharge, lower/upper insertion,
opposite-bound replay, both directed extrusion-demand forms, and intrusion.
Intrusion retains the actual event, unchanged origin/receiver identities,
selected actual copy coordinates, and the existing `Occurrence.Qualifies ref
birth` predicate. It does not redefine qualification using a type-bound graph.

`ConstraintStep.sound` and `ConstraintHistory.sound` prove backward reflection
of the actual obligations. `retains_occurrences` proves event retention.
`accepted_original_demands` constructs a regular solution of every original
pre-history demand from terminal acceptance alone.
`accepted_intrusion_equalities` reconstructs selected actual equalities along
the subsequent history, using the original retained-event/qualification facts.
This is a soundness/reflection result; it does not prove arbitrary satisfying
assignments survive added equalities or prove principal coverage.

`ofRegular_present`, `ofRegular_extrusion`, `ofRegular_step`, and
`ofRegular_history` prove an actual constructor-by-constructor translation of
old structural evidence through the frozen `Lattice.ofRegular` embedding. The
state and occurrence coordinates remain identical. Separately,
`decodeTerm_ofRegular` and `decodeStore_ofRegular` prove exact equality with the
old decoder on an embedded old graph, for every original Term/Store.
`old_store_solution_embeds` transfers the old semantic store result using those
proved equations and `Lattice.ofRegular_sub`.

### Original scoped publication and clients

`checked_publication_with_clients` applies the existing
`ScopedPublication.publication_clause_image` to the interpreted decoded
inventory. `publication_history_with_clients` additionally reflects the
terminal certificate through the new concrete history. All original guard
premises are retained unchanged:

- `BoundsBounded n bounds`;
- `InactiveImages n beforeUse afterUse q`;
- `StoppedClosed (bounds.map (Bound.rename q)) afterCap`;
- capture stopping implies allocation stopping;
- all supplied uses are below `count`;
- syntactic coverage of target published clauses by the inventory.

The conclusion uses one final graph and the single reference pullback
`fun k i => refs k (publicationTransport n count afterUse q k i)` for every
original base clause, every selected fresh use, and every client.

`metadata_checked_publication_with_clients` specializes those hypotheses using
actual pre/post capture and live metadata transport, bound-level closure,
non-generic dependency closure, and the existing guard lemmas. No numeric-only
substitute for non-generic/current/captured guards is introduced.

## Constructed completion: no assumed decoder success

`Completion.completeTerm`, `completeConstraint`, and `completeStore` allocate
missing exact constructors by append-only interning. They retain existing
indices and first-match decoding. Every Term constructor is implemented,
including both lattice constructors at either kind. Functions may contain
lattice expressions in any correctly kinded port; rows may contain them in
fields/payload elements while retaining finite structural spines.

`Completion.Lawful` is an independent sufficient formation judgment. Its only
requirements are actual variable-node lookups in the base graph, finite row
and tuple-payload shapes, and fresh record labels/variant tags. Union and
intersection accept arbitrary lawful children of the same kind and yield a
plain shape. There is no decoder equation, semantic interpretation, subtype
derivation, successful-completion execution, or preservation conclusion hidden
inside the legality constructors.

`Completion.completeTerm_correct` constructs successful execution from this
formation judgment:

```lean
Lawful base refs term shape →
∀ graph, Extends base graph →
  ∃ target identity,
    completeTerm graph refs term = some (target, identity) ∧
    Built graph refs term shape target identity
```

`Built` contains exactly:

1. literal prefix extension of the input graph;
2. the actual `decodeTerm` equation in the target;
3. an actual target lookup with the promised finite shape.

`Completion.completeStore_correct` extends this to the complete joint store.
`completedStore` is executable and its fallback is proved unreachable under
`LawfulStore`. `completedStore_correct` returns prefix extension and the actual
`decodeStore` equation for the computed result; no successful decoder equation
is supplied by the caller.

**Guard/validity boundary:** neither prefix extension nor `Built` asserts final
graph validity or guardedness. They are obtained from the terminal
`Lattice.accepts` premise. The theorem
`completion_alone_does_not_check_guard` makes this explicit: completing an
empty lawful inventory retains an unguarded base and the guard checker rejects
it. No guard preservation is inferred from appending nodes. A separate general
lawful-completion guard/validity preservation theorem is not supplied or needed
by the accepted-result theorem proved here.

## Strongest integrated theorem and its full premise inventory

`Completion.completed_publication_with_clients` combines construction,
new concrete histories, terminal finite lattice evidence, and the original
publication image theorem. It retains the publication premises above and adds:

- `LawfulStore graph refs` for the joint target inventory plus transported
  clients, based on lookup/shape/fresh-label facts;
- a concrete new `ConstraintHistory` from the **computed** comparison list in
  the computed graph, with the supplied retained occurrences, original `ref`
  and `birth`, to the terminal state;
- successful `Lattice.accepts` of one finite lattice certificate for that
  terminal state's obligations.

Writing `result` for the executable completion of the joint store, its
conclusion is:

```lean
Extends graph result.1 ∧
result.1.Valid ∧ result.1.Guarded ∧
PublishedSatisfied result.1 pulledRefs
  n bounds beforeCap beforeUse roots uses ∧
StoreSatisfied result.1 pulledRefs clients
```

Thus the prior supplied-decoder-success premise is removed even for finite
union/intersection expressions inside structural recursive graphs. A finite
certificate remains an input; this module neither invokes an exhaustive search
nor claims that the old structural decision procedure computes lattice proof
trees. Certificate production is a separate frozen-base packet.

## Meaningful checked instances

`lattice_publication_and_clients` instantiates the actual scoped-publication
and history theorem with a cyclic Function whose result contains both union
and intersection. The source `latticeBound` is an actual existing `Term`, not a
new source-language example. Its two fresh uses and cross-use client are all
interpreted under the same pulled reference assignment by
`lattice_two_uses_and_client`. Decoding and terminal acceptance are proved by
kernel reduction, and the history performs an actual four-port decomposition.

`Completion.sparseGraph` initially contains only a cyclic Function and one
effect atom. The existing decoder fails on `sparseTerm` because its required
constructors are absent. The term contains a union in a tuple payload, a finite
variant, an intersection, and an optional record field. Its independently
constructed `sparse_term_lawful` proof supplies no decoder equation.
Completion creates the lattice, nil/suffix/payload, variant and record nodes;
`sparse_completed_inventory` computes the final pair index, and
`sparse_completed_satisfied` derives validity, guardedness, prefix retention,
and original Store satisfaction from the computed construction and accepted
finite evidence. This demonstrates actual constructor creation, not merely a
conditional result for an already-complete graph.

Negative checks retain optional metadata, reject an effect reference absent
from its kind table, and reject a lattice expression used as a structural row
tail. These are representation checks, not claims about omitted source-level
row/coalescing semantics.

## Verification and audit receipt

Pinned executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
The actual session version checks identify Lake `5.0.0-src+eb6cafb`, Lean
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
No installation, dependency, manifest, or global-default change occurred.

All checks used the new owned isolated project and `run_check.py`: 120-second
limit per invocation, one Lean thread, `-j1 -M1024`, one invocation at a time,
and process-group termination on timeout. Native execution used the previously
authorized escalation needed for this environment's toolchain self-location.

| Check | Result |
| --- | --- |
| 01 | Failed on missing explicit lattice-node kind inference and row-branch simplification; dependent diagnostics were cascades from the unelaborated decoder. |
| 02 | Core decoder, concrete histories and publication passed, 3.172 seconds. |
| 03 | Failed on eliminated dependent-index binder names in old-history translation and a missing explicit selected-copy list type. |
| 04 | Core, exact old-history/decoder compatibility and publication example passed, 8.153 seconds. |
| 05 | Full independent-legality completion and completed publication application passed, 12.271 seconds. |
| 06 | Sparse missing-constructor example and explicit guard boundary passed, 7.776 seconds. |
| 07 | Exact final source build passed, exit 0, 9.920 seconds, no warnings. |
| 08 | Complete originating-module audit passed, exit 0, 1.457 seconds. |

Checks 01–07 used `lake build +YulangClosure.SimpleSubLatticeInference`.
Check 08 used `lake env lean -j1 -M1024 AuditLatticeInference.lean`.
The audit enumerates declarations by actual originating module, includes every
private/generated theorem, prints full theorem types and axiom lists, verifies
required roots, and rejects project axioms or dependencies beyond the standard
whitelist.

Exact result: **275 theorem constants**, 275 begins and 275 ends. Actual axiom
sets are: 109 empty; 124 `[propext]`; 42 `[propext, Quot.sound]`. There is no
`Classical.choice`, `sorryAx`, project axiom, or unchecked native-evaluation
dependency. Source scan found no `sorry`, `admit`, `axiom`, `debug.skipKernelTC`,
or `native_decide` tokens in the ten-module isolated source cone. The failed
first build's automatically generated placeholder diagnostics were not source
holes and do not occur in the accepted artifact or final audit.

Complete audit/types: `inference-lattice-inference/check08-audit.log`.
Audit program: `inference-lattice-inference/project/AuditLatticeInference.lean`.
All material failed and successful logs are retained. The 9 dependency files
and new output byte-match repository copies. Frozen lattice source hash remains
`55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`.

Budget consumed: **8 of 16** focused checks; no timeout, memory-limit increase,
concurrent compiler invocations, broad build, Rust tests, runtime changes, or
performance experiment. Default-target/root/audit import integration is
primary-owned and was not performed here.

## Parent application and remaining owners

The new finite lattice relation is now consumed by actual Term and Store
syntax, concrete histories, executable constructor completion, and the existing
scoped-publication/client theorem. The preceding standalone relation's missing
union/intersection consumer is therefore materially removed for the stated
finite-shape graph representation.

The original parent remains OPEN. Precise remaining obligations are:

1. **Native/source formation owner:** derive the actual graph/reference
   representation, `LawfulStore` row/payload/lookup/fresh-label facts, original
   publication inventory coverage, and unchanged guard invariants from actual
   supported source/native construction. None is assumed to follow from an
   inspected allocation or merge write site.
2. **Native/history owner:** connect real extrusion, retained occurrence
   equalities, replay, and all relevant graph growth to these concrete traces.
   The current new histories use one fixed completed graph. Old histories are
   translated by proof; interleaved lattice-graph growth and actual Rust trace
   extraction remain separate bridges.
3. **Certificate owner:** construct accepted finite lattice derivations from
   successful native inference. The old structural finite decision procedure
   is not silently used for lattice witnesses.
4. **Semantic/source owner:** identify this all-depth graph interpretation with
   ordinary/unifying coalescing as needed, preserve full native row/optional/
   cast semantics, and supply the original jointly scoped Call/effect/source
   witness with the original generalization, lawful-use and hygiene conditions.

No smaller supported source domain, altered inference behavior, independently
chosen per-use semantic witness, or production checker requirement is proposed.
A checked conditional publication theorem and its concrete examples do not
close the full native or original-source A/B gates.
