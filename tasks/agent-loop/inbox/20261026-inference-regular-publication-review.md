# Independent review: executable regular publication bridge

Date: 2026-10-26. Reviewer: `/root/execution_frontier`, non-author of the target and its publication producer. Bounded fresh compiler-referee / Lean review. Sole write: this receipt. All earlier frozen artifacts remain unchanged.

## Verdict

**ACCEPT for the explicitly represented finite-syntax / regular-graph publication bridge. No BLOCKING, MAJOR, or MINOR finding requiring repair.**

The module actually connects the prior regular-history theorem to the existing scoped-publication constructor. The decoder is executable syntax processing; the semantic relation remains the independently defined all-depth `RegularSub`. The final theorem derives original clause images by applying `ScopedPublication.publication_clause_image`, then uses one reference transport for the original publication and all included clients. It does not take a satisfying valuation, a semantic model law, a solved original publication, or a replacement clause-image law as a premise.

The frozen producer handoff explicitly preserves the decoder's exact-existing-node and intermediate suffix requirements. No decoder completeness, graph completion/augmentation, native trace production, metadata invariant, source reconstruction, or original whole-language inference-soundness conclusion is claimed.

## Frozen inputs

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| Producer handoff `20261026-inference-regular-publication.md` | `c43420af30c46f42a7f84dd8ef5bcc28c1ff33c9ec33d4a72c04bc57b5f52279` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

The target and all seven listed dependencies are byte-identical between the shared checkout and the isolated checked project `/workspace/scratch/f98087c7ac1a/inference-regular-publication/`. The target and finalized handoff hashes were rechecked before this verdict. The project remains pinned to Lean 4.35.0 with `-j1 -M1024` and no external packages.

## Executable decoder and constructor fidelity

Reviewed the full 549-line target, beginning with the actual decoder rather than its receipt. `References := Kind -> Nat -> Nat` is reference data. It does not contain satisfaction or well-formedness proofs. The variable branch checks the actual kind-indexed lookup. Missing variables and an index present only in the other kind's table do not become valid references.

`findList` searches the finite table for exact derived `Node` equality and chooses the first exact match. `findList_sound` and `findNode_sound` connect its result to the actual graph lookup. No semantic equality oracle, subtype test, unchecked evaluator, or model predicate participates in the search.

The Function branch recursively decodes all four ports in their original order and kinds and searches exactly `.function a' ae' re' r'`. `decode_function_exact` exposes each recursive success and that exact lookup. Neither effect port is replaced by empty effects or erased.

Record, tuple, and variant construction retain complete finite lists. Record cons preserves the exact label, optional bit, and decoded child; it requires an actual record tail. Tuple cons requires an actual tuple tail. Variant cons requires a tuple payload node and a variant tail, then retains the exact tag, complete ordered payload list, and alternatives. The `prepend*_exact` theorems expose those original lookups and the exact output node. A wrong tail constructor, wrong payload constructor, missing exact result, or mismatched metadata returns `none` by the actual branch definitions. `decodeTerm_found` correctly proves existence of every returned node; full graph validity is obtained later from the regular certificate check.

Cycles are supported through the resulting references, not by recursively unfolding a cyclic row spine. The recursive decoder terminates structurally on finite `Term` syntax. Union and intersection branches explicitly return `none`; their operands are not silently interpreted through an available node.

### Exact partial-decoder boundary

The function is total into `Option`; it is not a complete serializer for every valid existing regular graph. Every literal subterm must decode successfully, including nil, intermediate finite row/tuple/variant suffixes, and tuple payload nodes. For example, a valid graph containing an atom and its complete one-field record but no empty-record node cannot decode the corresponding `recordCons ... recordNil` literal. The record is semantically representable, but the required recursive nil search fails. This follows directly from the decoder and is now explicitly stated in the frozen handoff.

Exact child-reference identity also matters: the search does not normalize structurally equivalent graph references or augment the graph to create a missing constructor. No completeness or graph-augmentation theorem is hidden in `findNode_sound`, `decodeTerm_found`, or the main theorem. Successful decoding is an explicit syntactic premise, separate from semantic certificate acceptance.

## Renaming and one shared interpretation

`decodeTerm_rename` is a structural induction proving equality of the actual `Option` results, including failures:

```text
decodeTerm graph refs (term.rename q)
  = decodeTerm graph (fun k i => refs k (q k i)) term.
```

The graph stays fixed. Both variable occurrences and every nested port use the same composed assignment. No injectivity or semantic-preservation property of q is assumed. `decodeConstraint_rename` and `clause_rename` lift that concrete equation rather than postulating interpretation naturality.

`decodeTerm_congr_bounded` proves dependence only on the actual term's bounded variables. `decode_freshen_transport` then uses the unchanged `Generalization.transport_freshen` equation with its original anchor-preservation, use-bound, and term-bound premises. I inspected the actual transport definition and commuting proof: original coordinates use q, allocated use blocks use the corresponding freshened image, and coordinates beyond the entire finite region remain fixed. No separate reference assignment is chosen for different uses or clients.

The explicit bound/anchor conditions are structural premises. They are not asserted to follow for every native allocation or merge history. The theorem also does not preserve every old solution after a quotient or establish principal independent-use coverage; it constructs the stated pulled-back interpretation from accepted target evidence.

## From decoded inventory to independent regular satisfaction

`decodeStore` fails if any clause fails to decode and retains the clause order and duplicates on success. `decodeStore_member` supplies the actual decoded pair for every input member. The derived pair is deterministic because the decoder is a function; witnesses are not independently chosen per clause to satisfy different constraints.

`ClauseSatisfied` means successful actual decoding plus the frozen all-depth `RegularSub` relation. It is not certificate acceptance in disguise. `checkStore` first executes decoding and then invokes the existing `Regular.accepts`; `checkStore_sound` derives graph validity and every clause's regular satisfaction.

`history_store_sound` applies `Regular.accepted_original_demands` to the concrete history beginning at the decoded pair list, then uses `decodeStore_member`. Its inputs are a decoder equation, a represented structural history, and terminal finite acceptance. It does not take a regular model, satisfying valuation, desired original comparison, or abstract step law. The prior accepted history proof supplies the missing original comparisons even when they were removed from the terminal demand list/certificate.

## Main publication/client application

The exact substantive premises of `publication_history_with_clients` are retained:

- bounded original bound owners and bodies;
- inactive allocation images remain inactive;
- dependency closure below stopped target capture owners;
- stopped capture implies stopped allocation;
- every actual use lies below the finite use count;
- target-published syntax is covered by an explicit finite inventory;
- successful decoding of that inventory together with the automatically transported clients;
- the concrete regular history and final finite certificate acceptance.

The coverage premise asserts only target clause membership in a list. It asserts no satisfaction, source typing, or semantic inclusion. The theorem calls the **proved** `ScopedPublication.publication_clause_image` to obtain each original transported clause. I inspected that imported derivation: retained base clauses commute; active target owners retain reachable copied clauses; stopped target owners reduce to their retained base clause using explicit dependency closure and stopped allocation. The main theorem does not re-assume that conclusion.

Both final conclusions use exactly:

```text
fun k i => refs k (publicationTransport n count afterUse q k i).
```

Clients are included by appending their mapped clauses to the same decoded inventory, so their evidence comes from the same accepted history and reference assignment. No additional client-image hypothesis or per-use interpretation is introduced. The statement covers the arbitrary finite client list included in that check; it does not claim unconditional satisfaction of unexamined future client constraints.

`checked_publication_with_clients` is genuinely the zero-step specialization: it extracts the decoder result from successful `checkStore`, builds the nil history, and invokes the main theorem. It does not strengthen the assumptions or add a supplied solution.

## Concrete examples checked by inspection and existing kernel evidence

The finite carrier examples decode actual record/tuple/variant cons syntax to specific nodes. The record includes a true optional bit; the variant contains the complete tuple payload. The combined store is checked by a finite regular certificate. The rejection examples cover optional metadata mismatch, wrong kind table, missing reference, and arbitrary union/intersection syntax. Wrong carrier-tail/payload constructors also fail directly in the inspected decoder definitions; the module does not pretend to provide a broader native rejection test suite.

The cyclic publication example is substantive. Its graph contains a Function whose argument and result refer to itself, with both effect ports present in the separate effect table. Original owner 1 generates distinct use coordinates 3 and 5 while anchor 0 remains shared. After quotient/lowering, the target owner is inactive and its target publication contains the base clause only. `cyclic_inventory_coverage` proves that exact inventory fact by cases on the original `Published` constructors.

The example then performs executable decoding, an actual four-port decomposition history, and finite certificate acceptance. The main theorem reconstructs both original copied publication clauses and the cross-use client at coordinates 3 and 5 under the same pulled-back references. The explicit transport example also preserves future coordinate 6. This is regular cyclic interpretation, not a finite-Term valuation masquerading as a recursive solution.

## Verification evidence consumed

The producer's finalized handoff and complete audit were both consumed before this verdict. Existing build log `check-04.log` records successful construction of the frozen module; the producer records exit 0 and 4.860 seconds. No check was rerun because no concrete mathematical gap required one.

| Evidence artifact | SHA-256 |
| --- | --- |
| `check-04.log` | `57c821ec5a00f599a841a9e0da0f7344195a2161bf465aacc3133902bd93a85a` |
| `audit-05.log` | `07142e459a90c18bcec796c224469da753ae415ca892210d028da81b08da2775` |
| `RegularPublicationAudit.lean` | `a2a0f8b0274d9e37635e38e4fad7e9f5e2844997eb7da955bbeb6e287a98dfcf` |

I inspected the audit program's originating-module enumeration, required-root checks, exact-type printing, and axiom whitelist. Independent parsing of the complete log yields **148 distinct matching begin/end records**, all **42 authored theorem names**, and 106 generated helpers. The normalized axiom totals are **89 empty**, **42 `{propext}`**, **17 `{propext, Quot.sound}`**; one printed axiom list wraps across lines and was counted with the latter group. No project axiom, `sorryAx`, `Classical.choice`, error, unchecked native proof, or kernel bypass was found. Source scans found no proof hole or unsafe/bypass token.

All authored theorem statements and proofs were read in source; printed exact types of decoder freshening, Function fidelity, accepted history, both publication/client roots, and the cyclic two-use/client result were inspected explicitly. Existing full enumeration was audited, but this review does not claim to have individually re-proved each generated helper.

## Boundaries and stop

Accepted scope includes finite exact-shape structural syntax and guarded regular graph cycles. It excludes lattice/alias cycles, native open row tails, width/presence weakening and complete variant admission, general native coalescing, original Call/context strategies, and source quantifier/provider/guard coverage. The reference interpretation is shared structurally; it is not the original source-scoped witness/world semantics.

The first native seam remains production of the faithful graph and reference assignment, exact existing constructor/suffix entries, finite inventory coverage, decoder equations, concrete history, and accepted final evidence from an actual no-error/admitted native path. The metadata closure/inactive-image hypotheses also need their native invariants. The separate original-source reconstruction seam remains open. No original `SourceProblem.InferenceSoundness` instance is supplied.

No source, compiler, Git, cache, root record, manifest, or prior receipt was changed. No children or build processes were started. Python read-only inspection used `PYTHONDONTWRITEBYTECODE=1`. This sole review receipt is frozen after hashing; writes stopped.
