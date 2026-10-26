# Finite lattice certificates inside guarded regular graphs

Date: 2026-10-26. Producer: `/root/lattice_certificates`, generic `lean_prover`
leaf. Assigned branch/baseline: `yulang3`,
`eb3eef2f6a29d9c2a6132d648866c60900db276c`.

Status: constructed and checked by pinned Lean 4.35.0; complete originating-
module type/axiom audit passed. Independent review and integration remain
primary-owned. This packet closes the stated proof-side lattice-constructor
extension; it does **not** close original whole-source inference soundness,
principality, native correspondence, ordinary coalescing, or complete Call.

## Frozen outputs and ownership

- Leased proof: `notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean`.
  SHA256 `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`.
- Leased handoff: this file.
- Isolated project, original source copies, audit and logs:
  `/workspace/scratch/f98087c7ac1a/inference-lattice/`.
- No existing Lean module, root import, compiler, test expectation, shared
  task/status/index, configuration, toolchain, manifest, or Git state was
  changed. No children were launched. Proof writes stopped at the hash above;
  this handoff was the only subsequent repository write.

The five copied dependency sources match the assigned unchanged source cone:

| Source | SHA256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |

## Original obligation and consulted sources

The unchanged parent is the all-supported-original-source statement in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1 and 3,
with the approved birth-level correction: lawful finite construction histories
must preserve original source typing, principal coverage, soundness, natural
progress and termination, retaining all scopes, recursive sharing, publication,
Call/effects, hygiene and jointly chosen evidence. This packet neither proves
nor weakens those quantifiers.

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `.codex/agents/lean-prover.toml`,
the `yulang-lean-proofs` skill and its source/execution references, relevant
sprint/authority rules, and the Authoritative
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`.
Read actual `SimpleSubConstraintSyntax.Sub`, `Regular.expandNodes`, the regular
solution/history modules, existing completion's explicit lattice omission,
and the regular-solution/review history.

Primary original sources were freshly retrieved and read:

- Lionel Parreaux, *The Simple Essence of Algebraic Subtyping*, PACMPL 4,
  ICFP Article 124 (2020), DOI `10.1145/3409006`, official EPFL PDF:
  `https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content`.
  Read Fig. 10 and §§5.1–5.3, printed pp. 124:24–27.
  Scratch `reference-paper.pdf` SHA256
  `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`;
  extracted relevant text is `reference-sections.txt`.
- `LPTK/simple-sub` commit
  `9bae772624c23b52a93c1b226157e16898b4d9db`,
  `shared/src/main/scala/simplesub/Typer.scala`: actual `constrain` structural
  and cached-variable clauses, `extrude`, and polarity-indexed `coalesceType`.
  Scratch `Typer.scala` SHA256
  `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.
- The same commit's `syntax.scala`, including finite union/intersection,
  recursive and structural type syntax. Scratch SHA256
  `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f`.

Fig. 10/§5.1.2 distinguishes delayed recursive hypotheses from immediate
assumptions; crossing Function/record unlocks them. The paper explicitly
permits unguarded recursive syntax such as a self-unfolding variable while
withholding useful immediate hypotheses. Our `accepts` checks a guarded graph
fragment; **that check is not claimed to describe the entire paper's syntax or
to impose a new source restriction**. The original non-let proof sketches and
ordinary/unifying-coalescing distinction retain their stated limitations.

Initial web-tool retrieval failed on an EPFL signed redirect and disabled raw
GitHub retrieval; a direct read of the official/pinned URLs succeeded. These
were source-read failures, not theorem failures.

## Exact construction and rule correspondence

Namespace: `YulangClosure.SimpleSub.Lattice`.

`Node` is exactly `structural (Regular.Node k)`, `union left right`, or
`intersection left right`. `Graph` remains two finite kind-indexed node lists.
`Regular.Comparison` is reused unchanged: one kind and two node identities.
There is one graph and one relation over the whole comparison set, including
effect comparisons; no per-demand or per-kind semantic witness is substituted.

`structuralExpand` calls the existing `Regular.expandNodes` on the two actual
structural nodes. Consequently all native structural metadata is retained:
Function argument/argument-effect/result-effect/result ports have variance
`(-,-,+,+)`; records retain exact labels and optional bits; tuples retain order
and arity; variants retain tags and complete ordered payload lists. No width,
optional-row admission, tag coercion, cast, or effect-selection rule is added.

The independent inductive `Layer graph relation pair` has these constructors:

| Layer constructor | Actual finite `SimpleSub.Sub` rule |
| --- | --- |
| `refl`, `trans`, `bottom`, `top` | `Sub.refl`, `Sub.trans`, `Sub.bottom`, `Sub.top` |
| `unionLeft`, `unionRight`, `unionElim`, `unionMono` | The identically named `Sub` constructors |
| `intersectionLeft`, `intersectionRight`, `intersectionIntro`, `intersectionMono` | The identically named `Sub` constructors |
| `structural` | Exact `Regular.expandNodes`, then `Sub.function`, `Sub.recordCons`, `Sub.tupleCons`, `Sub.variantCons`, and the appropriate leaf rules |

Only `Layer.structural` has premises in the recursive `relation`, and those
premises are precisely the actual structural children returned by expansion.
All lattice and transitivity premises are smaller **finite Layer derivations**
at the same depth. There is no Layer constructor that directly admits a table
member. `Derivation` is a finite witness tree with the corresponding rule tags;
its transitivity tag includes the finite intermediate node identity.
`checkDerivation` consults the shared finite pair table only in `structural`.
It performs no search for a typing or derivation.

`Approx graph 0 pair` is true; `Approx graph (n+1) pair` is
`Layer graph (Approx graph n) pair`. The interpretation `RegularSub` requires
every finite depth and is defined before, independently of, certificate
acceptance. `Layer.mono` and `coinduction` construct it from any postfixed
relation. Finite checker soundness constructs the particular postfixed relation
of membership in the certificate's table.

Graph validity separately checks existing references and unchanged metadata.
`FiniteLattice` is an independent inductive witness that a lattice-only path
terminates at an actual structural node. `checkFinite_sound` and
`checkGuarded_sound` establish it for every graph index. Structural cycles remain
allowed. Guard-checker completeness or a production complexity claim is not
asserted; this is a bounded proof certificate checker, not a runtime proposal.

## Main theorem types and premises

All names below have prefix `YulangClosure.SimpleSub.Lattice.`. Complete printed
types of **all 153 originating theorem constants**, including generated/private
ones, are in `check07-audit.log`.

- `checkDerivation_sound`: for arbitrary graph, table, finite derivation, kind
  and endpoints, Boolean success yields `Layer graph (· ∈ table) pair`.
- `checkDerivation_complete`: a finite `Layer graph (· ∈ table) pair` derivation
  constructs a finite `Derivation` with successful checking.
- `checkDerivation_iff`: existence of a checked finite witness is equivalent to
  that independent Layer judgment. This is completeness for this finite rule
  language, not source inference or recursive-subtyping completeness.
- `certificate_sound`: successful checking of every finite certificate entry
  yields `RegularSub graph pair` for every pair in its shared table.
- `accepts_sound`:

  ```lean
  accepts graph certificate demands = true →
    graph.Valid ∧ graph.Guarded ∧
      ∀ pair, pair ∈ demands → RegularSub graph pair
  ```

- `accepted_joint_relation` strengthens the conclusion with one concrete
  relation containing every demand, postfixed under `Layer`, and included in
  `RegularSub`. The witness is exactly membership in the one checked table.
- `regular_fold`, `regular_refl`, `regular_trans`, `regular_structural` establish
  useful closure properties. Only the fold direction is asserted: no theorem
  silently selects a single finite Layer derivation from depth-specific
  witnesses. A reverse unfolding theorem is not supplied.
- `ofRegular_sub` embeds every old `Regular.RegularSub graph pair` into
  `Lattice.RegularSub (ofRegular graph) pair`. `ofRegular_lookup` preserves
  every original reference and node; `ofRegular_expansion` preserves exact
  structural expansion; `ofRegular_valid` and `ofRegular_guarded` preserve the
  represented graph properties. This is a proved inclusion, not an asserted
  bidirectional equivalence of all judgments.

No model, terminal valuation, source typing derivation, native-success law,
preservation law, or `LocalLaws` parameter occurs in the certificate-soundness
or accepted-demand theorem premises.

## Actual finite Sub bridge, with its exact limitation

`tupleTerm`, `recordTerm`, `variantTerm`, `structuralTerm`, and `nodeTerm` spell
out the finite constructor readback, preserving labels, optional bits, tags,
ordered payload lists, and all four Function ports. `structuralTerm_sub` proves
that the exact existing expansion corresponds to the existing finite `Sub`
constructors; it does not assume a structural preservation law.

`ReadbackAgrees graph read` requires only exact equations:

```lean
∀ k i node, graph.lookup k i = some node → read k i = nodeTerm read node
```

`ReadSub read pair` abbreviates the original finite
`Sub (read pair.kind pair.lower) (read pair.kind pair.upper)`.
The checked theorem is:

```lean
Layer.toSub :
  ReadbackAgrees graph read →
  (∀ pair, relation pair → ReadSub read pair) →
  Layer graph relation pair → ReadSub read pair
```

Its proof handles every Layer constructor using the actual `Sub` rules above.
The structural-port premise is explicit because this is a **one-layer** finite
correspondence theorem. A finite readback is not constructed for cyclic graphs
and need not exist. This theorem is not used by `certificate_sound`,
`accepts_sound`, or the recursive example, and is not advertised as a full
recursive-model or source-typing bridge.

## Concrete positive and negative evidence

`recursiveLatticeGraph` has two Function roots. The lower result is a union
containing its own Function root; the upper result is an intersection whose
first member is a union containing the upper Function root. The result proof
uses intersection introduction, union monotonicity, a structural Function step,
reflexivity, and top. Thus the cycle returns through real structural ports,
and contains both lattice constructors between structural steps.

`recursiveLattice_accepted` is proved by kernel reduction (`rfl`).
`recursiveLattice_regular`, `recursiveLattice_guarded`, and
`recursiveLattice_all_depths` derive the promised interpretation at every depth.
The table includes the separate argument and effect comparisons; deleting the
effect pair is rejected by `recursiveLattice_missing_effect_rejected`.

`unguardedGraph` has a union node referring to itself without a structural
step. `unguarded_table_assumption_rejected` shows that merely retaining its
comparison in the table cannot discharge the recursive union premise.
`unguarded_graph_rejected` proves rejection for **every** finite certificate
and demand list because the graph has no finite lattice-path guard.
This is a rejection by this guarded-fragment acceptance interface, not a claim
that original Simple-sub forbids the corresponding unguarded recursive syntax.

## Verification receipt and material repairs

Native executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb` with Lean `4.35.0`;
Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
No installation, global default, dependency, or manifest changes.

All checks ran in `inference-lattice/project` through the owned
`run_check.py`: timeout 120 seconds per invocation, one Lean thread,
project `-j1 -M1024`, a separate process group killed on timeout, one invocation
at a time. Native execution used the already-authorized escalation required by
this environment's native-toolchain self-location issue.

- Checks 01–06 ran `lake build +YulangClosure.SimpleSubLatticeCertificates`.
- Check 01 failed on the pinned spelling `Bool.and_eq_true_iff` and destructuring
  an equality inside a conjunction.
- Check 02 failed on Boolean-parenthesis parsing and two graph-embedding
  elaboration details.
- Check 03 retained only the embedding binder-name/metavariable issues.
- Check 04 passed after those repairs.
- Check 05, after adding finite witness completeness, failed because a final
  universally quantified closure goal needed `using closed` rather than a
  simplifier argument.
- Check 06 passed the complete frozen module, no warnings, exit 0,
  elapsed 3.320 seconds.
- Check 07 ran `lake env lean -j1 -M1024 AuditLattice.lean`, exit 0,
  elapsed 1.629 seconds. It enumerates every theorem by originating module,
  checks required roots, prints each full type and axiom list, and rejects any
  project axiom or dependency outside the standard whitelist.

Audit result: 153 begins, 153 ends, final count 153. Actual axiom distribution:
63 theorems have none; 65 use `[propext]`; 25 use `[propext, Quot.sound]`.
There is no `Classical.choice`, `sorryAx`, unchecked native-evaluation axiom, or
project axiom. A source scan for `sorry`, `admit`, `axiom`, `debug.skipKernelTC`,
and `native_decide` found no matches in the isolated six-module dependency cone.
All material failed-check logs are retained beside the successful logs.

Resource consumption: 7 focused checks of the assigned maximum 16; no timeout,
no memory-limit increase, no concurrent compiler processes, no broad build,
Rust tests, benchmarking, or runtime behavior changes. Full default-target
integration and root/audit imports are primary-owned and were not edited.

## Application to the parent and precise remaining bridges

The former regular interpretation could represent only structural graph nodes.
This packet removes that specific proof-side constructor omission: finite
union/intersection expressions can now sit between actual structural recursive
ports, and accepted finite evidence constructs their shared all-depth relation.
The old graph meaning embeds without altering any old port or metadata.

The original parent remains OPEN. First remaining integration work is to carry
this new graph representation through the **actual** decoder, graph completion,
constraint histories, and scoped-publication theorem. Existing
`RegularPublication.decodeTerm` and `RegularCompletion.completeTerm` explicitly
reject union/intersection and are unchanged; no theorem here automatically
changes those consumers. That is the proof integration owner's next precise
constructor bridge.

The native owner still must construct faithful kind/polarity-sensitive graphs
and finite derivations from actual successful inference, retaining all original
bounds, copied-row/occurrence identities, and accepted source metadata. This
packet does not show that Rust or reference `constrain` emits these certificates,
or that ordinary or unifying coalescing equals this interpretation.

The source proof owner still must connect the full original source construction
and contextual Call/effect witness to the interpretation, with original lexical
and event scopes, one shared strategy, generalization, lawful uses, and hygiene.
No independent marginal witnesses, narrowed source grammar, changed optional
record/cast semantics, production checker requirement, or claim of complete Call
has been introduced to bypass those obligations.
