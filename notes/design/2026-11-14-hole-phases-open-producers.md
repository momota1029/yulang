# Fixed-hole phases: open inspection and source producers

Date: 2026-11-14. Base: `ca75f9324`, branch `astra/hole-phases-2`.
Scope: termination of `GeneralNominalActualInspectionSteps.Step` only.
The boundary-agreement work belongs to the other worktree.

## 1. Status and exact claim

`ClassPHoleReadback` and `ClassPHolePhases` remain open. This work does **not**
prove unconditional Class P accessibility. It constructs the open-term local
engine, a simultaneous valuation of the entire initial frontier, direct source
replacement producers, and fixed-hole materialization producers. All are
standalone Lean theorems; none changes the operational relation or its guards.

The existing strongest general accessibility theorem remains
`GeneralNominalHolePhaseSimulation.class_p_accessible`: its extra hypothesis
is `ClassPHoleReadback roles`. The already closed ground-root theorem is
unchanged. No infinite actual execution or implementation defect was found;
there is no new semantic decision to ask the owner.

## 2. A hole is opaque, not algebraically free

Fix the initial frontier `H₀ = range (frontier initial.context.state).length`.
An indexed readback `Readback M origins H root e` asserts both:

* every model in `M` satisfies `Holds (interpret origins e) root`;
* every leaf of `e` belongs to the current `H ⊆ H₀`.

A leaf can denote a scalar, a compound, a recursive type, or a value with only
partial interval information. Its being a leaf says that the symbolic ledger
has not expanded it. It does not say that its denotation has no constructor.
Consequently, replacing the empty-leaf premise of the ground inversion proof
with mere finiteness of `H` is invalid.

The valid replacement is a dichotomy. If a successful inspection sees only
explicit nodes of the symbolic expression, the ground constructor proof works
with arbitrary valuations at its leaves. Otherwise it reaches an opaque leaf
at a successful constructor query. That event must be handled by the source
simulation; it is not already a hole-elimination certificate.

In particular, a leaf exposure is not enough to infer a uniform constructor
equation. Its optional actual origin may be absent, and a scalar query inspects
the lower endpoint. A value fitting that interval is not thereby equal to that
endpoint. Tests in the complete branch, retained origins, and the trusted
source/output explanation must supply the missing actual equation.

## 3. Closed pieces of the semantic invariant

### 3.1 One valuation for all fixed frontier positions

`GeneralNominalFrontierValuations.frontier_alias` proves that **every** entry of
the enumerated frontier represents an identity in the original source list.
This strengthens the old safe-walk-only result. The proof inducts on the
finite `explore` fuel. At a structural edge it uses the checked normalized
view; at a nominal edge it uses the point argument certificate. Composition
transports the projection along the preceding actual alias. Repeated cyclic
paths cause no problem: they are finite observations of the same identities,
not expansions into infinite terms.

`simultaneous_survives` chooses one identity function before quantifying over
future states and models. Both its initial-source membership and all its alias
certificates survive actual steps by model restriction. Thus one may evaluate
all current expressions with `vₘ(h) = (m (identities h)).1`.

`source_valuation` then proves, for **every already produced** indexed readback,
that a canonical expression at a unique actual origin denotes its actual
value under this same valuation. The proof is structural induction using
`FiniteMeaning.assemble` and canonical projection uniqueness. It neither
produces a new readback nor assumes leaf denotations are closed finite trees.
Its explicit remaining premises are the readback, canonicality, and uniqueness
of the represented origin.

### 3.2 Source syntax and counted labels with open leaves

`GeneralNominalOpenPatternLabels.Label context pattern term` records coverage,
the translation of the original source pattern to the quoted finite tree,
and canonicality. The source constructor key is retained in `pattern`.

`label_normal` proves this supported label is fixed by normalization.
`filled_label` proves simultaneous template substitution, record-tail hiding,
variant translation, canonical record sorting, and the emitter's subsequent
normalization preserve the filled tree and its original keys. Captures may
contain holes. Record-tail variables whose translation is deferred do not
satisfy this label interface; no unsupported tail is silently accepted.

Use the open weight

```
w(leaf h)                 = 1
w(scalar)                 = 1
w(nominal children)       = 1 + sum w(children)
w(structural children)    = constructorCost + sum w(children)
constructorCost(record L) = |L| + 1
constructorCost(other)    = 1
```

`label_mass` proves exact equality with the checker's normalized counted mass.
The ground weight, which assigns leaves zero, cannot be used here.
`matched_mass_eq` and `instantiated_bound` account for every constructor and
variable occurrence. Record sorting permutes the payload sum and preserves
the entire record spine cost. A shared capture bounded by each of its
presentations yields the required inequality instead of equality.

`GeneralNominalOpenReification.followed_source_label` reifies every explicit
subtree using an actual part of the parent source pattern. Variable children
of variants and sorted record payloads are included; no catalogue key is
chosen from its semantic name.

### 3.3 Actual recursive inspection, including open captures

`GeneralNominalOpenInspectionValues` proves scalar, structural, and nominal
inversion at explicit expression nodes with arbitrary hole valuations.
`OpenInspectionPositions` preserves canonicality, interval containment, and
the same retained actual value when descending to children. Nominal fallback
uses its endpoint's actual denotation when the inherited origin is absent.

`GeneralNominalOpenInspectionMatching.inspect_matched_or_exposed` and its
mutual list theorem recurse over the real `inspect`/`inspectMany`. Their
conclusion is either constructor-wise `Matches`, or an expression leaf with
an `Exposed` witness: a successful constructor query, its actual interval and
optional origin, its finite meaning, and inclusion of its captures and tests
in the supplied full report. Arity comes from `Finished`. Matching uses the
lower nominal traversal; successful completion of the original inspection
also requires the upper traversal when it is present. The theorem does not
assert that its `Subreport` relation preserves anchors or a path witness.

`GeneralNominalOpenCaptureLabels.inspect_labels_or_exposed` additionally
retains a source label and fixed-hole closure for every matched capture.
For a needed variable, `shared_capture_value` uses **actual** inherited-report
membership and `GenerationGuard`'s agreement with every repeated capture to
produce `CaptureValue`. It does not equate overlapping intervals, select
interval interiors, or equate different symbolic expressions merely because
they denote equivalent values.

### 3.4 Direct source observations really delete a hole

`GeneralNominalSourceHoleExposure.structural_readback` constructs the indexed
constructor readback from a recorded normalized structural head. Children use
the canonical first index of their source identity in the fixed frontier.
The head equation comes from the normalized source model; child equations
come from actual structural projections.

Assume the source snapshot is inhabited and K2 excludes a cycle at the parent
identity. If an immediate child had the same source index as the parent,
applying `origin` to that equality would give equality of their source
identities. The recorded structural edge would then be a self-edge in the
actual K2 graph, contradicting the premise. Every child index therefore
belongs to `H₀.erase parentIndex`. This proves `structural_replacement` without
assuming the replacement readback as a premise.

`structural_trace` packages the result as an actual `HoleElimination.Trace`
of length one, with replacement depth one. Its inventory holes are the **full
frontier of the supplied source snapshot**, and the structural test must
belong to the supplied vocabulary. It has no operational Step premise. It is
extraction from a recorded source observation, not a proof that every future
update has this form. Instantiating it with a fresh dynamic frontier at each
update would not establish a fixed initial budget.

`nominal_readback` and `nominal_replacement` prove the corresponding indexed
readback and hole deletion for a descriptor whose parameters are all point
type intervals. They use the descriptor's actual model and point-argument
readback. Reusing the parent index gives a semantic nominal self-cycle through
an argument, which actual-position K2 excludes. These lemmas do not inspect
nominal bodies and do not cover row parameters or strict intervals.

### 3.5 Real compound materialization and output binders

`GeneralNominalOpenChildProduction.child_argument` handles the actual emitter
request. Given one simultaneous capture-label function and its `CaptureValue`
evidence, it constructs a normalized source-key-preserving child label,
`ArgumentValue` for its denotation, and closure over the same remaining holes.
Compound templates use the emitter's request-completeness theorem; forwarded
variables use the real generation guard. Existing `argument_contained` and
`argument_retained` turn `ArgumentValue` into child-site semantics when supplied
the packet model and input coherence. `child_descent` proves instantiated
Paterson descent from head matching and per-name mass bounds. Constructing the
simultaneous minimum-mass substitution is still separate.

`GeneralNominalIndexedOutputProduction.materialized_output` proves fixed-hole
readback from an actual schema recipe. Actual input uses follow real captured
origins; output-only uses follow the reserved identity's supplied earlier
readback. Binding those trees introduces only their existing leaves. The same
substitution is used at every occurrence of a declaration variable.

`promoted_output` connects this indexed composition to the actual `Trusted`
settlement derivation, including its earlier-binder ordering. Its sole basis
premise is that the trusted explanation's actual input origins already have
indexed readbacks. This is still a producer premise, not a construction of the
whole history invariant. Canonical output trees additionally require canonical
schema tests and substituted trees (`recipe_canonical`, `canonical_bind`);
source-key-preserving output labels remain to be constructed.

## 4. The phase measure once the source simulation is constructed

The existing `HoleElimination.Trace` counts genuine substitutions exactly:
`count + after.holes.length = before.holes.length`. Hence there can be at most
`|H₀|` eliminations. A replacement must omit its consumed hole and be applied
to every expression, including captured variables, aliases, and historic
packet labels. `IndexedHoleReadback.actual_elimination` already proves the
semantic part once that replacement is produced.

Inside a phase, explicit input matching gives the counted head bound, checked
Paterson gives strict child descent, and the snapshot lineage theorem bounds
parents of recorded packets by the current root-label mass. The existing
snapshot enumeration then supplies a finite signature basis. Missing
installation facts decrease inside that basis; administrative steps use their
existing accessibility proof. A genuine elimination decreases the outer
hole-count measure and may reset the finite inner basis.

This is precisely what `HolePhaseSimulation.Simulation` and
`HolePhases.accessible` already consume. The qualitative phase proof permits
an arbitrary finite reset at each elimination; a uniform growth function is
only needed for the additional explicit iterated numeric budget. No numeric
bound, `InstalledDepthBound`, or termination certificate has been added to
these new local producer hypotheses.

## 5. Exact remaining source construction

The remaining named interface is still `ClassPHoleReadback roles`, with the
same quantifiers as before: every Checked registry and point InitialSource
must supply one `Simulation` on the actual relation. Its `next` field is not
constructed by this change.

The unresolved invariant must establish all of the following together:

1. Every relevant later capture and materialized actual origin has a uniform
   canonical, source-key-labelled expression over the **current subset of the
   initial holes**. Unsettled output-only identities that lack such an
   explanation cannot become head justifications.
2. Every relevant `Exposed` event is discharged from the actual trusted/source
   explanation. It must yield an already available explicit expression, a
   global replacement over surviving holes, or the existing K2/pending outcome.
   The direct initial-source lemmas above do not cover a later reduced ledger.
   Bare semantic `Holds` plus absence of recorded K2 edges is not a derivation
   of a syntactic occurs check.
3. A single simultaneous capture substitution and compatible labels for all
   historical packets survive each global replacement. Semantic equality of
   two capture presentations does not identify their syntax. Choosing a
   minimum-mass presentation before substitution does not prove it remains
   minimal after substitution. The normalized `PacketLabels` ledger and its
   source-key-compatible root decoding must be reconstructed or transported.

These are proof-extraction obligations. This work establishes neither a
counterexecution nor a need to strengthen the guard. No additional lazy guard
or owner decision was introduced.

## 6. Validation and provenance

All ten new modules are imported by appended lines in `lean/Yulang.lean`.
Only new modules, a new audit, this new note, and those appended imports are
changed. The existing relation, frozen files, prior-turn files, spec, plan,
configuration, and git refs are unchanged.

Final validation commands and exit codes:

* From repository root:
  `cd lean && lake build Yulang.GeneralNominalSourceHoleExposure Yulang.GeneralNominalOpenCaptureLabels`
  — exit 0. These two targets transitively build all ten new modules.
* From `lean/`: `lake build Yulang` — exit 0 (2307 jobs).
* From `lean/`: `lake env lean Audit/HolePhaseOpenProducers.lean` — exit 0.
  All 21 audited conclusions use only `propext`, `Classical.choice`, and
  `Quot.sound` (some use a subset).

Intermediate elaboration attempts failed while deriving the proofs; the
commands above are the final validation pass. The first generation script
also encountered the unavailable `python` command; subsequent generation used
`python3`. A prohibited-token scan of the new proof modules returned no matches.

The `yulang-proofs` skill was applied. No registered/callable `prover` role was
available; no prover agent ran. The primary constructed these bounded
extensions. A separate read-only reviewer checked their quantifiers and
producer boundaries; the review explicitly retains the open Simulation claim.

The separate reviewer also ran `cd lean && lake env lean Audit/HolePhaseOpenProducers.lean` independently: exit 0; all 21 dependency lists were permitted.
