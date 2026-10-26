# Independent review: exact finite lattice decision construction

Date: 2026-10-26. Reviewer: `/root/lattice_review`, independent nonauthor,
single-reviewer packet. Producer: `/root/lattice_decision`.

## Verdict and frozen target

**ACCEPT. No mathematical, semantic-boundary, source-correspondence, axiom,
or evidence findings in this frozen packet.** The result is an exact
proof-side certificate construction for the existing finite valid graph
interpretation. It does not close original source/native inference soundness
or introduce a production inference algorithm.

Reviewed source, in full: all 711 lines of
`notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean`, SHA256
`a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9`.

Reviewed producer handoff:
`tasks/agent-loop/inbox/20261026-inference-lattice-decision.md`, SHA256
`f29c307f30521d08b58597a6a30fc3219132b6a7e2a92b7d385af65364bac8e3`.

The parent supplied current HEAD
`6545873f7262e9c3f3b1ef588a3c2ebca74ea83a`; this reviewer performed no Git
operation. The separately developed growing-inference consumer and its
integration are outside this review. Earlier accepted lattice-certificate and
consumer review receipts are unchanged.

The governing repository instructions, Lean skill/source/execution guidance,
top-level inference principles, immutable-birth correction, and original
source-preservation obligation were read during this continuous review lane
and remain governing. The original A/B/source obligation retains all supported
constructors, lawful histories and uses, original scopes and shared witnesses,
full Call/effects, hygiene, principal coverage, progress and termination.
The previously inspected primary Fig. 10 and sections 5.1–5.3 allow unguarded
source syntax; the graph guard used here does not narrow that original domain.

## Mathematical review

### Actual finite universe and finite witness candidates

`kindPairs` and `allPairs` enumerate every pair of actual indices of the same
kind, with universe size `n_value^2 + n_effect^2`. The exact membership lemmas
retain the kind and both endpoint bounds. They do not enumerate proposed
source typings or replace a source quantifier by a bounded search.

`proofAt` retrieves an actual `Derivation` from a certificate. `combine`
combines those finite witnesses. `candidates` covers every constructor of the
unchanged finite `Lattice.Layer`: structural, reflexive, bottom, top, both
union injections, union elimination, both intersection projections,
intersection introduction, both monotonicity rules, and transitivity at every
in-range middle. Reusing an existing pair also retrieves its actual proof;
mere membership is not converted into a same-layer recursive hypothesis.

`derive` selects only candidates passing the original `checkDerivation`.
The only derivation constructor that can inspect the shared recursive
comparison table is the frozen structural rule. All lattice and transitivity
premises remain explicit finite derivations. The construction does not alter
that separation or define semantic subtyping by checker acceptance.

The structural branch retains the actual frozen `structuralExpand` and
`Regular.expandNodes`. Function variance and all four ports, including both
effect ports, are preserved. Record labels and optional bits, tuple order and
arity, and variant tags with complete payload lists are unchanged. One graph
and one shared comparison table cover both kinds throughout the construction.

### Inner saturation has a sufficient constructed bound

`close` tracks pending comparisons and accumulates checked witnesses against
one fixed recursive table. `remaining_strict` proves that a changed filtered
pending list has strictly smaller length. `close_correct` simultaneously
maintains checked witnesses and coverage of the whole finite universe by the
pending list or the existing witness table.

If a round changes, strict decrease makes the remaining fuel sufficient. If
it is stable, every still-pending comparison fails `derive`; universe coverage
then proves the required saturation property. At zero fuel, the length
invariant forces the pending list to be empty. Thus the initial universe
length is sufficient for `layerCertificate`; no supplied stabilization bound
or maximum derivation depth is assumed.

`Saturated` alone is only a local closure property, and the source correctly
proves the required stronger implication afterward. `saturated_complete`
inducts over the independent finite `Layer` derivation. For every binary rule
it obtains actual child witnesses from the induction hypotheses, verifies them
using `Witnesses`, and exhibits the corresponding candidate. The transitivity
case explicitly proves the middle index occurs in the enumerated range.

This endpoint argument is substantive: `union_exists` and
`intersection_exists` use actual graph validity to obtain the referenced
children; `layer_endpoints` then handles every Layer rule. `layer_bounded`
applies to child derivations as well as the requested conclusion. There is no
unproved assumption that every transitivity middle or lattice child was
enumerated. With checker soundness, these arguments establish
`layerCertificate_exact` for every recursive list on a valid graph.

### Outer pruning constructs a checked shared certificate

`pruneStep` only filters its current recursive table. `pruneStep_strict` proves
strict length decrease on every change; `prune_supported` proves that universe
length fuel leaves a table whose every member has an actual witness against
that same final table. Each outer round computes a fresh inner certificate
against its current recursive table. It does not retain witnesses checked
against a larger, obsolete table.

`extract_table` proves literal list equality between the extracted certificate
table and the supported recursive table. `extract_checked` rewrites by that
equality before applying each located witness's checker result. Consequently
`constructed_checked` has **only the graph as input** and establishes
`checkCertificate graph (constructCertificate graph) = true` for every graph.
`constructed_sound` then applies the frozen independent certificate soundness
theorem. Neither result assumes validity, guardedness, an external derivation
table, a model, a semantic solution, or reverse unfolding.

### Uniform finite-depth coverage establishes exactness

The completeness argument does not select a common derivation from arbitrary
depth-specific witnesses. `FiniteCover graph recursive` asserts the existence
of one depth whose entire approximant lies in the current table. This depth is
uniform across every comparison, including both kinds.

`universe_cover` constructs the initial depth from validity and the endpoint
lemma. `approx_down` is proved by depth induction and `Layer.mono`.
`pruneStep_cover` advances the coverage depth by one: approximation decrease
places the pair in the old table, while `Layer.mono` transports its children
into that table and exact inner saturation proves it survives the filter.
`prune_cover` constructs the invariant through every outer round, including
the stable and zero-fuel cases.

An all-depth `RegularSub` comparison satisfies the single resulting finite
depth, hence belongs to the constructed final table. The opposite direction
is `constructed_sound`. Therefore the actual theorem is

```lean
graph.Valid ->
  (pair ∈ table (constructCertificate graph) ↔ Lattice.RegularSub graph pair)
```

The validity premise is honest and remains in the full printed type. No
guardedness premise is required for this table exactness. The independent
`Approx` and `RegularSub` definitions are unchanged. Only **after** exactness
does `regular_unfold` obtain a common finite layer from the constructed shared
postfixed table. Its reverse direction uses the pre-existing `regular_fold`.
There is no circular use of reverse unfolding in saturation or completeness.

### Decision acceptance retains the exact guard interface

`decideDemands` is definitionally the original `Lattice.accepts` applied to
the graph-only constructed certificate. Its exact theorem is

```lean
decideDemands graph demands = true ↔
  graph.Valid ∧ Lattice.checkGuarded graph = true ∧
    ∀ pair, pair ∈ demands -> Lattice.RegularSub graph pair
```

The statement uses the actual Boolean `checkGuarded = true`, not an unproved
converse of `checkGuarded_sound`. `decideDemands_sound` may conclude the
semantic `Graph.Guarded` property through that established soundness theorem.
`decideDemands_rejects_iff` is exactly the negation of the displayed conjunction.
In particular, an invalid graph is rejected even for empty demands; there is
no empty-list shortcut around graph validation.

`decided_joint_relation` exposes one common postfixed relation containing all
requested comparisons. It does not choose separate semantic witnesses for
different demands or Function ports.

These bounds prove totality and exactness relative to the frozen finite graph
relation; this is not an incomplete search at an arbitrarily chosen unfolding
depth. The implementation still uses linear list lookup and potentially large
finite derivation trees. No polynomial runtime, production suitability,
coalescing equivalence, or completeness for all of the original Fig. 10/source
semantics is claimed.

## Examples and verification evidence

The two final `by decide` examples kernel-compute a valid lattice injection and
a failed union elimination. The recursive example theorem uses the proved
exactness interface; the separate evaluator also executes the constructor on
that recursive graph without receiving a hand-written certificate. The six
direct execution cases cover recursive acceptance, delayed recursive mismatch,
finite injection, failed elimination, an unguarded graph, and an invalid
dangling graph with empty demands. All recorded results agree with the source.
These examples supplement the proofs; they are not completeness premises.

I read the final build log, evaluation source/log, audit source/log, runner,
and pinned project configuration. The final focused build passed with exit 0
in 3.976 seconds, the six-case evaluation passed in 0.822 seconds, and the full
audit passed in 1.221 seconds. The copied toolchain is Lean 4.35.0; project
`moreLeanArgs` are `-j1 -M1024`; the runner sets one Lean thread and a
120-second timeout. There was no review risk requiring an additional compiler
invocation: **reviewer checker reruns were zero**.

| Evidence | SHA256 |
| --- | --- |
| `inference-lattice-decision/check07.log` | `120068b05d0512a1201e2774bdec2b748f946522d413dff33e7b4452cffe9eb7` |
| `inference-lattice-decision/check08-eval.log` | `fba340e8e484e2465b0721ba59f6f2dfc3ac272e3817cbab4a8693851670d89f` |
| `inference-lattice-decision/project/EvaluateDecision.lean` | `2881ae9429566974c5f9c6d83294dd18d22a1434b9a455a609289ca12dc5e094` |
| `inference-lattice-decision/check09-audit.log` | `2d5dff142edf1488573f81b1b39f592026ea6f1bc81bf9a8d596eb15302273c8` |
| `inference-lattice-decision/project/AuditDecision.lean` | `a40951abe62b0c1091b7ef2de692c7a367e39412eca05640db94d3a25241118d` |
| `inference-lattice-decision/declaration-inventory.json` | `8504a9d2c7e910e6bc2e4133acc371005f3914ab0ff69330b13cec04de8ced71` |

## Complete declaration audit and source identity

I inspected all **141 printed declaration types and axiom results**, including
all **95 theorem constants**. All 45 authored theorem roots are required by
the audit program and match the source; the remaining 50 theorem constants are
generated/private. The audit enumerates actual originating-module declarations,
rejects project axioms, uses full/private names, and checks transitive axiom
dependencies. It includes definitions as well as theorem constants.

I independently parsed the raw log: all 141 declaration begin/end/axiom names
and all 95 theorem begin/end names match in order, with no duplicate declaration
names. Every parsed name, theorem flag, full type, and axiom list exactly
matches `declaration-inventory.json`.

| Actual axiom set | All declarations | Theorem constants |
| --- | ---: | ---: |
| Empty | 47 | 25 |
| `propext` | 56 | 32 |
| `propext`, `Quot.sound` | 38 | 38 |

There is no `Classical.choice`, `sorryAx`, project axiom, or unchecked
native-evaluation assumption. The seven-source cone has no proof-hole,
axiom-declaration, `native_decide`, explicit unsafe/partial implementation, or
kernel-bypass token. Compiler-generated recursion support declarations are
included in the 141-declaration audit; their generated names do not add an
unproved theorem assumption.

Integration inventory detail: the isolated 95 includes four generated theorem
names in the older Lattice namespace: `table.eq_1` and
`Node.references.eq_1`, `.eq_2`, `.eq_3`. A larger integrated inventory should
use an exact name-set difference instead of assuming 95 wholly new names.
This does not change the accurate isolated originating-module count.

All seven copied source files byte-match the repository inputs. The new source
matches the target hash above, and all six imported dependencies remain:

| Dependency | SHA256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |

## Parent obligations, findings, and cessation

There are **no actionable findings for this frozen packet**. The original
parent remains OPEN. The graph-only construction removes the need to supply
an external finite terminal certificate; it does not prove that successful
native inference yields a faithful graph/history or accepted terminal demands.
Native/source graph formation, identities and metadata, lawful completion,
publication coverage and guards, concrete extrusion/replay/intrusion/growth
traces, ordinary/unifying coalescing, full width/open-row/optional/cast
semantics, and the original jointly scoped Call/effect/source witness remain
their owners' obligations. Unguarded original source syntax is not removed.

Only this newly leased review receipt was written. No source, producer handoff,
producer scratch/cache, shared status/import, Git state, or earlier review
receipt changed. No children were launched. **All review writes are stopped.**
The receipt's exact SHA256 is sent in the final handoff rather than inserted
into its own content.
