# Independent review: canonical finite structural row model

Date: 2026-10-26. Reviewer: generic independent leaf
`/root/native_model_review` (mathematical/specification audit).
Assigned baseline: `yulang3`, `bf81a1bd444b3bcbecca6b754ea6fb603262f368`.
Mode: M3, one fresh nonauthor review of the frozen component.

## Verdict

**ACCEPT for the stated finite structural model-construction component.**
No substantive mathematical, premise-hiding, or source-scope defect was found
in the frozen proof, paper, or handoff. No producer repair is required by this
review. This is not acceptance of a complete native correspondence theorem or
of the unchanged original `SourceProblem.InferenceSoundness`; both remain
OPEN exactly as the producer states.

The meaningful reduction is:

```text
finite row/head syntax + finite syntactic saturation
  -> computed graph and one shared reference map
  -> every retained all-depth structural/lattice inequality
  -> actual graph validity and guard-check success
  -> actual terminal decideDemands = true.
```

The result does not assume an existing semantic model, an independent model
for each polarity, a successful finite certificate, or terminal checker success.
The remaining native saturation and exact history/source alignment conditions
are substantial obligations; this review does not convert them into facts.

## Frozen scope and evidence identity

The following SHA-256 values were independently recomputed and match the
assigned review target:

| Frozen file | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRowModel.lean` | `16835744153d05150992175ddb866ccc202e0f31781ed1a5a26c3e55c54a26bb` |
| `notes/theory/2026-10-26-native-row-model-construction.md` | `7921ede9a0579696de3db4ce1625e55d493ccd0b3d237196876039d763173cd0` |
| `tasks/agent-loop/inbox/20261026-inference-native-row-model.md` | `d196b897f8c73e0e839fd7d2239afc738109aa1c8a8b8b826100e9d4849b1951` |

All 13 entries of the producer's frozen Lean manifest (the new module and 12
imports) were recomputed against both the repository and isolated project:
**zero mismatches**. All 18 entries in `evidence-hashes.json` also match.
The frozen dependency manifest SHA-256 is
`f8c89026b5787a7dfa20c343cb9a2b5338d04def12964baa4f90e778084b5a1a`.
This verifies the complete dependency table in the producer handoff rather
than assuming that the named imports still have the audited bytes.

Read inputs included root AGENTS/pre-sprint, the Lean skill and both reference
guides, design authority, the current top-level inference principles, the
birth-level SCC correction, the original source-preservation claim and its
shared-strategy boundary, the original whole-proof target, the continuation
record, all 600 lines of the new Lean file, its paper/handoff, and the actual
relevant imported definitions. The source check also inspected the original
record-boundary/variable-flow manuscript sections, current native Function and
record dispatch in `crates/yu-solver/src/lib.rs`, and the pinned Parreaux text
in `inference-lattice/reference-sections.txt` (§§5.1–5.3/Figs. 11–12).

## Original claim and scope comparison

The unchanged root in `YulangClosure/Contracts.lean` is a proposition
definition, not an established theorem instance:

```lean
def SourceProblem.InferenceSoundness : Prop :=
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The original source scope includes shared lexical/type/event resources,
generalization and lawful independent uses, qualifying intrusion/extrusion,
complete Call, contextual effects, optional/open records and method/cast
evidence. A single graph valuation does not by itself supply the original
joint source-scoped witness `e`. The new module neither changes this root nor
provides an instance of it. The paper's opening OPEN notice and §§5–6 retain
this distinction accurately.

The source-preservation claim's shared strategy must respect original
dependency scopes. Here the achieved shared object is the computed `s.graph`
and the one `s.names`; the later publication conclusion uses the same
`s.names ∘ publicationTransport` for every use and client. No claim equates
this constraint-level sharing with a completed source evidence strategy.
The imported histories retain the actual occurrence/copy and current
birth-level qualification premises; this component supplies no new
qualification rule.

The Parreaux comparison is also properly bounded. Unifying coalescing is
motivation for correlated occurrences, not an imported proof that this
lower-join construction equals either reference coalescing algorithm. The
paper's non-let restriction and footnote 15 do not discharge Yulang's
let/extrusion/intrusion, contextual-effect or complete-Call obligations.

## Premise audit and core mathematical argument

`System` consists only of `rows : Kind → Nat`, finite kind-indexed
`Regular.Node` head lists, and a finite `Comparison` list. Source rows and
heads use disjoint numeric ranges. No graph or semantic relation is stored in
this input. The construction enumerates finite lists, allocates slots by
`idxOf`, and renames original references; its data definitions are executable.

The five `Saturated s` premises have the following exact force:

| Premise | Required fact | What it does not assume |
| --- | --- | --- |
| `bounded` | Each retained clause endpoint is less than `rows kind + heads kind.length`. | Graph existence or semantic subtyping. |
| `formed` | Every head has unique labels/tags and each child reference is in its kind's source range. | An interpretation of those children. |
| `rowRow` | For a retained in-range row edge `x ≤ y`, each structural lower head of `x` is a structural lower head of `y`. | A semantic transitivity/valuation law. |
| `rowHead` | For `x ≤ head u`, each `head h ≤ x` yields a retained direct `head h ≤ head u` clause. | A successful endpoint comparison in a different source relation. |
| `headHead` | A retained head pair passes `Regular.NodeRel (fun p => p ∈ s.clauses)` after actual head lookups. | `RegularSub`, a certificate, checker acceptance, or a satisfying assignment. |

Inspection of `Regular.NodeRel`, `expandNodes`, `nodeRel_iff` and
`nodeRel_rename` confirms that the last field is a finite constructor/metadata
test plus literal membership of its demanded children. Atom mismatch and
incompatible constructor/record shapes fail syntactically. Function children
have variance `(-,-,+,+)`: upper argument to lower argument, upper argument
effect to lower argument effect, lower result effect to upper result effect,
and lower result to upper result. All children use the identical reference
renaming. Thus the hard recursive semantic conclusion has not been inserted
into `Saturated` under another name.

`System.lower` and `System.upper` filter the finite head range. The graph
contains every head and every suffix of each row's lower and upper lists.
`names` maps a row to its complete lower-join slot and a source head to its
head slot. `emit` uses this same map for all four Function ports, record
children, tuple elements and all variant payloads. A negative occurrence
does not switch to an independently selected upper model.

The relation used by `postfixed` is exactly the image of retained clauses
under that one map. The four endpoint cases are valid:

1. Head-to-row uses finite union injections from a retained lower head.
2. Row-to-row injects each source lower head into the target join using
   `rowRow`, then eliminates the source join.
3. Row-to-head uses `rowHead` to obtain each actual lower-head/upper-head
   clause and uses structural expansion on those heads.
4. Head-to-head uses the actual head lookups and the syntactic `headHead`
   closure, transported by `nodeRel_rename`.

An empty lower list is handled by bottom. In cases 3 and 4 the recursive
relation is used only beneath the existing structural rule. `Layer` has no
constructor that admits an arbitrary recursive pair directly; its lattice
and transitivity rules are finite same-depth derivations. The imported
coinduction theorem establishes every finite approximation by induction on
depth, so `canonical_bounds` proves the independently defined all-depth
`Lattice.RegularSub`. It does not appeal to a monotone fixed point of a
negative-port type operator, leastness, or arbitrary-assignment preservation.

`canonical_valid` separately handles head child references and suffix child
references. `canonical_guard_checked` proves the actual `checkGuarded`
Boolean using the real graph-size fuel and strictly shorter suffixes; it
does not replace it with an existential guard condition. Structural recursion
is allowed, while pure lattice traversal terminates at a structural head or
bottom/top. Guardedness alone does not imply validity for malformed input;
the proof correctly keeps `canonical_valid` and its `Saturated` premise
separate. `canonical_decided` supplies validity, this actual guard Boolean,
and `canonical_bounds` to the imported exact finite-decision equivalence.

The upper meet is independently allocated with `.upper` slots.
`canonical_interval` proves the lower-join meaning below that upper meet by
finite intersection introduction and the retained row-to-head clauses.
No equality between lower join and upper meet is used. The unconstrained-row
discriminator verifies bottom, top, and false reverse decision. The
alias-cycle example maps both rootless rows to actual bottom nodes; it does
not assert equivalence with all unguarded recursive source syntax such as
`mu a. a`.

## Exact theorem/application and axiom comparison

In the following table all new names have prefix
`YulangClosure.SimpleSub.NativeRowModel`. All free parameters are universally
quantified, with the implicit parameters exactly as in the frozen source and
the complete printed audit. `P,Q` means `[propext, Quot.sound]`; `P,C,Q` means
`[propext, Classical.choice, Quot.sound]`.

| Declaration | Full substantive premises and conclusion | Actual axioms |
| --- | --- | --- |
| `canonical_bounds` | `Saturated s → ∀ p, p ∈ s.clauses → Lattice.RegularSub s.graph (renamePair s.names p)` | P,Q |
| `canonical_valid` | `Saturated s → s.graph.Valid` | P,Q |
| `canonical_guard_checked` | `∀ s, Lattice.checkGuarded s.graph = true` | P,Q |
| `canonical_guarded` | `∀ s, s.graph.Guarded` | P,Q |
| `canonical_decided` | `Saturated s → LatticeDecision.decideDemands s.graph (s.clauses.map (renamePair s.names)) = true` | P,Q |
| `canonical_interval` | `Saturated s → r < s.rows k → Lattice.RegularSub s.graph ⟨k, s.names k r, s.index k (.upper r (s.upper k r))⟩` | P,Q |
| `canonical_original_history` | `Saturated s` and `ConstraintHistory s.graph ref birth first ⟨mappedClauses,events⟩` imply graph validity, guardedness and `Holds s.graph first.obligations`. No history is constructed by this theorem. | P,Q |
| `canonical_completed_publication` | `Saturated s` plus precisely the completion/publication/history premises enumerated below imply `Extends base s.graph`, validity, guardedness, original `PublishedSatisfied` and client `StoreSatisfied` under one shared pullback. | P,Q |
| `canonical_decoded_store` | `Saturated s` and the exact equation `decodeStore s.graph s.names store = some mappedClauses` imply `StoreSatisfied s.graph s.names store`. | P,Q |
| `empty_lower_bottom` | `r < s.rows k` and `s.lower k r = []` imply an actual structural-bottom lookup at `s.names k r`. No saturation premise. | P,Q |
| `recursive_member` | For every `Comparison p`, membership in the concrete recursive clause list iff `p.lower < 2 ∧ p.upper < 2`. | P,C,Q |
| `recursive_saturated` | `Saturated recursiveSystem`, without a supplied model. | P,C,Q |
| `recursive_decoded` | Exact original `decodeStore` equation for `recursiveSystem.graph`, `recursiveSystem.names` and `recursiveStore`. | P |
| `recursive_store_constructed` | Validity, guardedness and original `StoreSatisfied` for that concrete graph/map/store. | P,C,Q |
| `recursive_decision_constructed` | Actual `decideDemands` is true for its mapped clauses. | P,C,Q |
| `alias_saturated` | `Saturated aliasSystem`. | P,Q |
| `alias_cycle_constructed` | Both named value rows look up as bottom and the actual decision on the mapped alias clauses is true. | P,Q |
| `lower_join_upper_meet_need_not_equal` | The unconstrained lower root is bottom, its upper root is top, and actual upper-to-lower demand decision is false. | P |

For `canonical_completed_publication`, the complete substantive retained
premise list is:

- `LawfulStore base s.names (inventory ++ clients.map
  (Constraint.rename (publicationTransport n count afterUse q)))`;
- `BoundsBounded n bounds`;
- `InactiveImages n beforeUse afterUse q`;
- `StoppedClosed (bounds.map (Bound.rename q)) afterCap`;
- `∀ k i, afterCap k i = false → afterUse k i = false`;
- `∀ use ∈ uses, use < count`;
- every `Published n (bounds.map (Bound.rename q)) afterCap afterUse
  (roots.map (Row.rename q)) uses clause` lies in `inventory`;
- with `result` equal to the actual `completedStore` of that base/reference
  map/inventory-plus-renamed-clients, an actual
  `GrowingHistory ref birth result.1 ⟨result.2,events⟩ s.graph
  ⟨s.clauses.map (renamePair s.names),finalEvents⟩`.

The resulting publication and client interpretation is the same function
`fun k i => s.names k (publicationTransport n count afterUse q k i)`.
The original `n`, `bounds`, `beforeCap`, `beforeUse`, `roots` and `uses` appear
in the publication conclusion unchanged. Comparison with
`completed_decided_growing_publication_with_clients` confirms that only its
terminal graph/table are fixed to the computed construction and its terminal
decision-success premise is discharged. No lawful-inventory, metadata,
coverage or actual-history premise disappears.

`LawfulStore` is constructor/shape/variable-lookup evidence, not semantic
store satisfaction. `decodeStore` performs exact graph readback, not a
subtyping check. `GrowingHistory` is locally graph-indexed and permits only
literal-prefix growth. Consequently an arbitrary final graph reconstruction
does not establish the required history or `Extends base s.graph`. The
paper explicitly states this restriction and the need to construct the
history in the known interpretation or prove an exact transport. That
remaining obligation is not concealed by the wrapper.

The recursive example uses the existing `SimpleSub.Term` and `Store` grammar:
the same value row occurs in both value ports and the same effect row in both
effect ports, with inequalities in both directions. Its decoder equation is
proved by reflexivity. It is an actual constraint-store instance, not an
instance of every original source constructor or of source typing itself.

## Complete axiom and execution evidence

Reviewed the actual origin-audit program, not only its success receipt. It
selects by originating module index, includes private/generated declarations,
rejects project axioms and duplicate entries, checks all 18 required roots,
prints complete types and axiom dependencies, and rejects dependencies beyond
`propext`, `Classical.choice` and `Quot.sound`.

Independent recomputation of the saved records gives 209 unique begin/end
records: 137 theorem constants, 61 definitions, five constructors, three
inductive types and three recursors; 17 private names are included. The set of
137 theorem names exactly matches the separate theorem-only audit.

| Axiom set | Theorem constants | All originating declarations |
| --- | ---: | ---: |
| empty | 41 | 97 |
| `propext` | 35 | 51 |
| `propext, Quot.sound` | 55 | 55 |
| `propext, Classical.choice, Quot.sound` | 6 | 6 |

The six choice-dependent constants are exactly `recursive_member`,
`recursive_member._proof_1_3`, `recursive_saturated`,
`recursive_saturated._proof_1_5`, `recursive_store_constructed`, and
`recursive_decision_constructed`. Generic canonical construction and
application roots use only `propext, Quot.sound`. The report therefore does
not call the entire module choice-free or axiom-free.

No unapproved dependency appears in the complete records. Reviewed retained
source-scan and failed/successful-check evidence; no proof hole, project
axiom, unchecked native evaluation or kernel bypass was found in the new
source or inspected dependency evidence. The final build log records pinned
Lean 4.35.0, exit 0, 14 jobs; both complete audits record exit 0. Their hashes
match the handoff (`check07`: `4830768147f516e0556696c849478d0628a6088dc22711c16ecb5e157cd227c1`;
all-origin audit: `96c008de494caa3f9b129017ddfe5acad160fa748e6a90c3ca9ff669042da1c0`).
The project pin, manifest and bounded `-j1 -M1024` options were read.

This reviewer used **zero of two optional Lean calls**: the frozen source,
complete checked types/axioms, import hash agreement and direct proof reading
left no concrete checker question requiring a rerun. No broad build, native
test, Cargo invocation or Git command was used. This is independent
mathematical/specification review of the supplied checked artifacts, not a
newly claimed independent execution of the producer's nine checks.

## Native/source boundary and next required evidence

The exact structural relation is intentionally narrower than full native
record adaptation. `recordPairs` requires matching field order, labels and
optional bits, while native record dispatch looks up target fields by name,
permits absent optional target fields and checks presence obligations.
Native Function dispatch confirms the same four signed ports as the formal
structural rule. The manuscript's `{foo?:string} → {} → {foo?:int}` example
also confirms why intermediate model selection cannot replace the actual
direct producer/consumer boundary query.

The producer explicitly preserves the stronger original continuation:
unchanged-view routes and producer anchors, authentic consumer boundary IDs,
typed record/cast/method/Call plans, separate output ports for real adaptations,
optional absence/non-resurrection, and authentic effect context/scope/occurrence
identities. Nothing in this review permits widening the transitive
`Lattice.RegularSub` relation to stand in for nontransitive boundary evidence.

The next owners must establish, for actual successful native execution:

1. Complete physical-slot and structural readback correspondence, including
   both directions of all eight lanes and canonical/raw identity distinctions.
2. The five exact syntactic saturation fields, with original-clause coverage,
   replay, merges, extrusion and fresh-use transport.
3. Exact constructor-completion and actual history alignment with the computed
   graph/reference map, or a proved transport preserving its local operations.
4. Original publication metadata and the full source-scoped evidence
   reconstruction, including the optional/open-record, contextual-effect,
   method and complete-Call cases outside this structural relation.

These are retained parent obligations, not requested repairs to this accepted
component. Neither the inventory fixture nor restricted complete-block replay
evidence supplies them globally.

## Write boundary and cessation

The sole reviewer-created repository file is this review receipt. No producer
file, production Rust, imported proof, project configuration, shared status,
root import, question or Git state was changed. No scratch project or checker
cache was created. No child was spawned.

**Reviewer writes stopped after this receipt.** The frozen producer files
remain unchanged. Primary owns adjudication, integration, any subsequent
source/native work, and all commits/pushes. Acceptance is confined to the
specified component and exact frozen hashes above.

## Mechanical EOF-only integration delta

Date: 2026-10-26. The primary requested a narrow follow-up after removing
three surplus terminal newline bytes from `NativeRowModel.lean` for integration.
No other producer artifact was revised.

**ACCEPT this mechanical integration delta.** Independent byte comparison
against the retained frozen isolated copy establishes the exact equation
`frozenBytes = integratedBytes ++ [LF, LF, LF]`. The frozen file is 30,080 bytes;
the integrated file is 30,077 bytes and ends with the final namespace `end`
followed by one newline. No Lean token, proof, theorem type, premise or import
changed.

| Version | SHA-256 |
| --- | --- |
| Original reviewed source, retained under `inference-native-row-model/project/YulangClosure/NativeRowModel.lean` | `16835744153d05150992175ddb866ccc202e0f31781ed1a5a26c3e55c54a26bb` |
| Integrated repository source after EOF normalization | `30016f40295a803df2ed3d9b46efd256d1427400f55bda1810e22a00f89d7780` |

The paper and producer receipt were rehashed and remain exactly their historical
frozen versions recorded above. The original review and complete axiom/type
comparison therefore continue to apply to the integrated Lean tokens. This
follow-up does not claim a new checker run or review of the primary's broader
integration build/audit; final integration verification remains primary-owned.
No Lean invocation, Cargo invocation or Git command was used. The sole write
was this appended review section. **Reviewer writes stopped again after this
append.** Original native/source and whole-soundness obligations remain OPEN.
