# Simple-sub paper and `mlsub-compare` audit

Date: 2026-09-30
Status: completed source audit; classifications are research guidance, not design approval
Scope: full ICFP 2020 paper reading, corresponding `mlsub-compare` implementation, and classification of the current SCC-intrusion rule set
Paper: Lionel Parreaux, “The Simple Essence of Algebraic Subtyping,” PACMPL 4 (ICFP), Article 124 (2020), DOI [10.1145/3409006](https://doi.org/10.1145/3409006)
PDF: [EPFL Infoscience full text](https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content)
Implementation: [LPTK/simple-sub, `mlsub-compare`](https://github.com/LPTK/simple-sub/tree/mlsub-compare), audited commit `9bae772624c23b52a93c1b226157e16898b4d9db`

## Reading and audit method

The complete 30-page PDF was downloaded and read page by page, including the references. The paper's main coverage is: MLsub and polarity ( §§2.2–2.5); Simple-sub constraint inference and extrusion ( §§3.1–3.6); simplification ( §4); syntactic subtyping and soundness/completeness sketches ( §5); and randomized comparison with MLsub ( §6). The repository README identifies `mlsub-compare` as the branch corresponding to the ICFP 2020 paper. The audit inspected its typer, simplifier, comparison test driver, and README. It was a source audit; tests/builds were not run.

The PDF is also at `/tmp/simple-essence-algebraic-subtyping.pdf`; extracted full text is at `/tmp/simple-essence-algebraic-subtyping.txt` in the research environment. The branch tip is dated 2021-08-11. README says its line-count statement refers to submission commit `252908c452c9f48643ecb57b69cc2e41cd7483da`, with non-essential code added later.

## What the paper and implementation establish

Simple-sub stores mutable lower and upper bounds on type variables and propagates constraints when a new bound is installed (paper §§3.2.2, 3.6; `Typer.scala` `constrain`, lines 87–129). Function comparison reverses argument direction and preserves result direction; records use width/depth subtyping. A visited-pair cache prevents recursive constraint traversal from looping.

Level-based let generalization raises the right-hand-side level, then instantiates variables above the scheme level on each use. `freshenAbove` uses one memo table per instantiation and copies bounds as well as variables, preserving sharing and cyclic bound graphs (paper §3.5.1; `Typer.scala` `typeLetRhs`, `freshenAbove`, lines 65–84 and 166–189). This is ordinary per-binding level generalization, not generalization of a mutually recursive definition SCC as one generalized component.

Ordinary extrusion is explicitly polarity-sensitive and memoized by `(variable, polarity)`. It copies only variables above the requested level, reverses polarity at Function arguments, installs a link bound on the original variable, and copies the opposite bounds into the fresh variable. The paper explains that the copied representative conservatively approximates both sides as needed; strict one-sided occurrences can discard one bound (§3.5.1, Fig. 7; `Typer.scala` `extrude`, lines 131–159). This is the relevant Simple-sub precedent. It does not preallocate one shared parent per SCC vertex, prove positive/negative parent identity can be shared, or define a `GeneralizedComponent`.

The exact extrusion writes matter for the next proof. At positive polarity, the reference adds the fresh representative to the original variable's upper bounds and fills the representative's lower bounds from the recursively extruded original lower bounds. At negative polarity, it adds the representative to the original variable's lower bounds and fills the representative's upper bounds from recursively extruded original upper bounds. The opposite side is intentionally absent from the fresh representative. A graph-level preallocation proof therefore cannot show equivalence only by alpha-renaming vertices: it must preserve these polarity-specific source/parent constraints. The `extrude` early return at `ty.level <= lvl` also fixes which vertices are copied versus shared anchors.

This gives a small discriminator for any polarity-erasing parent map. Let a too-high-level variable `v` have lower bound `Int` and no upper bounds, whose empty upper-bound intersection denotes Top. Positive extrusion produces `p+` with `Int ≤ p+` and no upper bound; negative extrusion produces `p-` with `p- ≤ Top` and no lower bound. Installing both source-side links also gives `p- ≤ p+`. The choices `p+ = Top` and `p- = Bottom` satisfy these constraints independently. Identifying both representatives as one `p` adds the combined interval `Int ≤ p ≤ Top` and cannot represent that pair of independent choices. This demonstrates that one parent for both polarity-specific extrusion representatives does not preserve the reference extrusion's assignment interface. It does not rule out a Yulang-specific theorem that deliberately uses one quantified binder under a different observation relation; that theorem must not be described as ordinary Simple-sub extrusion equivalence.

The implementation's recursive type coalescing keys recursive occurrences by variable and polarity (`Typer.scala`, `coalesceType`). Its optional compact simplifier performs co-occurrence rewriting and hash-consing; `canonicalizeType` specifically documents possible exponential powerset-like growth (`TypeSimplifier.scala`, lines 86–101). That observation motivates a representation question but does not prove SCC intrusion avoids equivalent growth or preserves principality.

The comparison driver generates terms and checks mutual subsumption against the MLsub executable (`MLsubTests.scala`). The paper reports 1,313,832 generated expressions, with simplification disabled on the MLsub side because a known MLsub simplifier bug otherwise affects comparison (§6). This is evidence for the stated Simple-sub/MLsub subset and experiment, not evidence for Yulang SCC scheduling, effects, hygiene, runtime identity, or intrusion.

Independent spec-auditor review found one minor wording issue: the constraint cache covers subtype pairs involving a variable, not only variable-variable pairs. The row above was corrected to match the source. No material provenance misclassification was found in the reviewed table. Review scope: this artifact, the named Simple-sub sources, and the intrusion charter/sketch/effect draft; no tests were run.

## Rule classification

Labels are provenance categories, not approval. “Simple-sub original” means the paper/reference implementation directly contains the semantic or algorithmic ingredient. “Yulang extension” means required by Yulang's wider source behavior or existing Oracle lifecycle, but absent from the paper's language/algorithm. “New conjecture” means the intrusion/effect-hygiene proposal adds an unproved rule or representation claim not established by either source.

| Current rule or claim | Classification | Basis and limit |
|---|---|---|
| Mutable variable lower/upper bounds and propagation of new bounds across opposite bounds | Simple-sub original | Paper §3.2.2, Fig. 9; `Typer.scala` `constrain`. |
| Function argument contravariance and result covariance; record width/depth constraints | Simple-sub original | Paper §3.2.2 and Fig. 9. Yulang products/nominals/effects need additional rules. |
| Per-top-level-constraint cache of subtype pairs involving a variable, including recursive structural comparisons | Simple-sub original | Paper §3.2.2 and Fig. 9 describe caching comparisons to avoid repeated work/loops; `Typer.scala` creates a `(SimpleType, SimpleType)` cache per top-level call and shares it through recursive calls whenever either endpoint is a variable. |
| Level boundary, RHS at higher level, per-use freshening above scheme level | Simple-sub original | Paper §3.5.1, Figs. 6–9; implementation `typeLetRhs`/`freshenAbove`. |
| Freshening one identity consistently throughout a use, copying its cyclic bounds and preserving below-boundary identities | Simple-sub original | `freshenAbove` memoizes variables and leaves `level <= lim` untouched. The exact parent/child boundary-port discipline proposed by intrusion is not thereby established. |
| Extrusion through structural types with argument polarity reversal | Simple-sub original | Paper §3.5.1, Fig. 7; implementation `extrude`. |
| Distinct representatives keyed by `(VarId, polarity)` and opposite-bound approximation | Simple-sub original | Paper §3.5.1 says two new variables are needed for both bounds except strictly one-sided cases; `extrude` cache key and branches implement this. This weighs against assuming one polarity-erasing parent. |
| Cyclic bound-graph traversal with memoized extrusion representatives | Simple-sub original | Paper §3.5.1 describes copying cyclic subgraphs; implementation's polarity cache closes back-edges. It is not a theorem about definition-SCC generalization. |
| Union/intersection encoding of lower/upper bounds and polar recursive coalescing | Simple-sub original | Paper §§2.3, 2.4, 3.3; implementation `coalesceType`. The exact Oracle compact projection is Yulang-specific. |
| Simplification via co-occurrence analysis, polar-variable removal, variable merging, and hash-consing | Simple-sub original | Paper §4.3; `TypeSimplifier.scala`. Not a general license to drop arbitrary nontrivial constraints; equivalence is justified for its type semantics. |
| Removing a one-polarity variable that is itself recursive, then pruning its recursive row | Yulang extension as an Oracle operation; preservation is a new conjecture | In `mlsub-compare`, `TypeSimplifier.simplifyType` only applies its polar-only removal branch when `!recVars.contains(v)` (`TypeSimplifier.scala:230–236`); recursive variables are preserved there. The Oracle's root projection counts polarity through `CompactRoot.rec_vars`, rewrites root and recursive rows, then prunes unreachable rows (`compact/analysis/occurrence/mod.rs:68–80`, `analysis/mod.rs:41–56`, `occurrence/substitution.rs:69–85,110–125`, `generalize/core/prune.rs:90–121`). The captured `pub f x = x f` root has negative-only `q=TypeVar(2)`, which is removed and pruned. Simple-sub §4.3.1 alone does not prove that this Yulang operation preserves the Oracle source/use relation. |
| Whole mutually recursive definition SCC as the generalization/publication unit | Yulang extension | Paper's let-rec rule handles an individual binder; it does not specify Yulang's top-level SCC graph, member ordering, open internal uses, or all-member publication. Existing Yulang Oracle/charter supplies these requirements. |
| Dependency-sink-first scheduling, ordered per-member root preparation, epoch/restart and publication behavior | Yulang extension | Not in paper or reference implementation; sourced from Yulang Oracle/approved F4 scope where applicable and the current Yulang charter/ledger. |
| Function/evaluation/result effect identities, effect-row constraints, forced local effect quantification, handler visibility/hygiene | Yulang extension | Outside the paper's type and term languages. Paper's quantified type variables do not model effect binders or handlers. |
| Tuples, nominal constructors/variance, role constraints, delayed specialization outcomes and Yulang diagnostics | Yulang extension | Outside the paper's core type language (records/functions/primitives); must be specified from Yulang behavior. |
| Allocate parents for all relevant vertices before traversing a known SCC; rewrite boundary-facing uses through that fixed map | New conjecture | SCC sketch §§2,4. Paper allocates representatives on first recursive visit, memoized by polarity, rather than SCC-wide preallocation. Equivalence is unproved. |
| One parent identity per internal variable independent of polarity, or any stronger SCC-based polarity sharing | New conjecture; rejected as ordinary Simple-sub extrusion equivalence | Sketch §5 explicitly leaves polarity open. The `Int ≤ v ≤ Top` discriminator above shows that identifying Simple-sub's positive and negative extrusion representatives loses an independently admissible boundary assignment pair. A separate Yulang quotient needs its own observation relation and proof. |
| Intrude by transporting all bound edges through a parent map while preserving SCC topology | New conjecture | SCC sketch §§2,4 and abstract-semantics draft §§3–4. Paper supports edge propagation and graph-cycle memoization separately, not this construction's correctness. |
| Freeze a solved SCC, then intrude with no post-intrusion mutations | New conjecture | SCC sketch §6. Simple-sub's mutation algorithm does not state this SCC freeze protocol. Yulang root preparation may continue advancing state, so compatibility also remains open. |
| `GeneralizedComponent { roots, parents, graph }` as primary scheme authority | New conjecture | SCC sketch §7. Neither paper nor `mlsub-compare` has this representation. |
| Parent substitution as a shared interface for instantiation, monomorphization, specialization, and cache key | New conjecture | SCC sketch §8. `freshenAbove` provides per-use fresh variables, but does not pull substitutions back through an intruded component or define such a cache. |
| Only boundary-relevant inner variables need parents; purely internal variables may remain local | New conjecture | SCC sketch §9 explicitly leaves the criterion open. Levels establish which variables are generalized in Simple-sub, but not this SCC parent criterion. |
| Expected `O(V+E)` SCC parent allocation and edge transport | New conjecture | SCC sketch §3. The source's cached graph traversal gives a plausible comparison, but neither asymptotic bound nor no-expansion guarantee is established for proposed edge transport/projection. |
| Type parent `P` and hygiene binder map `Theta` are distinct identities | Yulang extension (separation requirement); transport law is new conjecture | Effect-hygiene note §§3,6. Separate type/effect namespaces are required by Yulang meaning; capture-avoiding joint transport and its preservation theorem are not in Simple-sub. |
| Keep path-sensitive handler boundary history on edge/evidence/binder, not as one parent-local state | Yulang extension (path-sensitive observation); representation invariant is new conjecture | Effect-hygiene note §§4–5. The paper has no handlers or path histories; the invariant is a proposed safeguard pending a Yulang hygiene semantics. |
| Apply type substitution to evidence payloads but preserve boundary identities; don't erase evidence merely because types coincide | New conjecture over Yulang extension | Effect-hygiene note §§5,7. This transport/composition behavior has no paper analogue and needs a hygiene algebra and proof. |
| Freshen local type and hygiene binders according to lexical/semantic ownership, independently for each incoming use, while preserving outer anchors | Type portion is Simple-sub original; hygiene ownership and combined SCC policy are Yulang extension/new conjecture | Paper §3.5.1 and `freshenAbove` justify ordinary local type freshening. Hygiene binders and SCC-owner mapping need separate definitions. |
| Intrude itself neither opens/closes boundaries nor invents unknown effect shape | Yulang extension as a required phase boundary; exact no-op rule is new conjecture | Effect-hygiene note §5. Paper has no effect boundary semantics from which to derive it. |
| Runtime dynamic guard identity remains fresh independently of compile-time binder ID | Yulang extension | The distinction is motivated by runtime handler behavior and absent from Simple-sub. Exact runtime rule needs Yulang evidence. |
| Two-stage proof: pure intrusion correctness, then hygiene transport | New conjecture (proof decomposition) | Effect-hygiene note §8; useful methodology, not a theorem from the paper. |
| Pure finite saturation, carrier-parametric satisfying-fiber preservation, and renaming commutation | New conjecture | Current abstract-semantics draft §§1 and 3–5. Paper gives soundness/completeness sketches for its own constraint algorithm (§5), not this closure operator/carrier or parent transport. |

## Audit conclusion and next gate

Simple-sub supplies a concrete baseline for level-based generalization, per-use freshening, polarity-sensitive extrusion, cyclic bound traversal, and bound propagation. It does **not** supply SCC-wide preallocation, parent sharing across polarity, an authoritative generalized SCC object, Yulang scheduling/effect behavior, or a proof that parent substitution gives principal independent specializations. The correspondence is therefore a source for one component algorithm and its proof obligations, not a ready-made intrusion implementation.

The next proof target is a finite graph characterization of the reference extrusion transition: represent each copied identity as `(v, polarity, boundary)`, include the source-side link and copied opposite bounds above, and compare on-demand memo allocation with preallocation under the same map. The simple two-bound discriminator rejects sharing positive and negative extrusion representatives under their ordinary assignment interface. Check preallocation on a cycle and a shared diamond while retaining distinct polarity ports, before considering any Yulang-specific quotient or component projection. Separately, the Yulang recursive interval projection trace remains unresolved: the prior `q ∪ K`/`Pred` explanation was withdrawn; the audited compact upper is an intersection (`q ∩ K`), so dropping the negative-only interval requires a new preservation argument. This paper audit does not discharge that Oracle adequacy obligation.

## Signed-query follow-up (2026-10-03)

The earlier complete-paper audit remains the reading record. Its named `/tmp`
PDF/text and checkout caches are absent in the current environment; this
follow-up does not claim another complete paper reading.

The primary re-read the pinned
[`Typer.scala`](https://raw.githubusercontent.com/LPTK/simple-sub/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala),
including `constrain`, `extrude`, `freshenAbove` and the internal type grammar.
The `constrain` entrypoint enforces a positive subtype pair by changing bounds;
its constructor cases are Function, Record, Primitive and flexible Variable.
That grammar contains no Boolean constraint or rigid operation-arm binder
node. This is an entrypoint audit, not a claim that no related extension
exists elsewhere. Negative polarity in extrusion is not logical negation of
an equality or subtype proposition. No tests/builds ran.

Consequently the successor's signed guard and scoped-arm queries cannot be
certified merely by citing this positive enforcement procedure. The current
M3 gate must preserve joint feasibility and quantifier scope; the follow-up
is provenance evidence, not a new language restriction or non-finiteness proof.
