# Ordinary cast resolution across infer and specialize

Date: 2026-07-21

Status: feasibility and implementation design for ordinary value-cast resolution. This document
does not cover role-impl conformance enforcement and does not authorize implementation. The
ambiguity-granularity decision in Section 5 was already made by Claude Sonnet 5 and the user; the
remaining staging and API details are proposed for review.

Current-code citations were re-verified against `main` at commit `4ca46d4a` on 2026-07-21.

The motivating open reports are:

- `notes/bugs/2026-07-12-struct-field-type-conformance-gap.md`;
- `notes/bugs/2026-07-13-implicit-cast-ambiguity-not-rejected.md`;
- the concrete nominal-cast-reducible part of
  `notes/bugs/2026-07-12-function-result-annotation-conformance-gap.md`.

## 1. Purpose and problem statement

Three apparently different bugs share one missing compiler contract.

### 1.1 Struct-field type soundness

Given:

```yu
struct S { x: bool }
S { x: 42 }
```

lowering and invariant constructor propagation do create the required `int <: bool` relation. The
constraint machine turns that relation into a nominal-cast request, but an empty cast candidate set
is treated as success by omission. Specialization repeats the permissive decision and emission can
leave a bare `Coerce` boundary. The program therefore passes `check` and reaches a runtime boundary
instead of failing at compile time.

### 1.2 Implicit-cast ambiguity

Given two visible value-cast declarations with the same source and target constructor paths,
ordinary cast resolution does not reject the ambiguity. Infer applies constraints from every
matching declaration. Specialize2 later chooses the first matching declaration during emission.
Changing declaration or import order can therefore change runtime behavior without changing the
source-level type request.

### 1.3 Concrete function-result annotation mismatch

Given:

```yu
my f(): bool = 42
f()
```

the body-to-result-annotation connection creates the same required `int <: bool` relation. Both
function-result diagnostic gates accept broad constructor shape, and the missing cast is again
treated as success by omission. The declared `bool` result can therefore carry an `int` value.

This project closes the concrete nominal-cast-reducible case by making the cast request itself
fail closed. It does not attempt to make the two function-result shape checkers a complete type
relation.

### 1.4 Shared root cause

There is no authoritative ordinary value-cast result with three explicit states:

```text
Missing | Unique(rule) | Ambiguous(rules)
```

Instead, each infer/specialize consumer performs an ad hoc emptiness, iteration, `.any(...)`, or
first-match test. Zero candidates and multiple candidates consequently acquire different accidental
meanings at different pipeline points. The repair is to share the cardinality classification and
make every ordinary value-cast consumer state its policy for all three results.

## 2. Verified current pipeline

### 2.1 The two current registry surfaces

Infer owns a mutable `CastTable` in `crates/infer/src/casts.rs:13-15`. Its value-cast bucket is keyed
by source and target constructor paths, and `CastTable::candidates` returns the complete slice for a
pair at `crates/infer/src/casts.rs:41-49`.

The durable downstream registry is `poly::expr::Arena::cast_rules` at
`crates/poly/src/expr.rs:43-47`. Each `poly::expr::CastRule` carries `def`, `source`, `target`,
`scheme`, and `kind` at `crates/poly/src/expr.rs:87-102`. Source cast lowering currently registers
the same declaration in both surfaces at `crates/infer/src/lowering/body/mod.rs:2382-2393`.

The inference-side value rule currently loses declaration identity: `CastTable::insert` stores
`def: None` at `crates/infer/src/casts.rs:22-38`. Seeding a session from an existing poly prefix also
discards the durable rule's `DefId` at `crates/infer/src/analysis/session/lifecycle.rs:114-127`.
That is sufficient for scheme instantiation but insufficient for candidate-related ambiguity
diagnostics without another provenance step.

Value casts and generated error-effect upcasts already occupy separate buckets/kinds. This project
classifies only `CastRuleKind::Value`; effect-up selection is out of scope.

### 2.2 Infer event and compact-generalization paths

When distinct nominal constructors meet, the constraint machine emits `NominalCastNeeded` at
`crates/infer/src/constraints/machine/propagate.rs:120-132`. The event carries `PosId`, `NegId`,
constructor paths, and weights, but no definition/expression source provenance
(`crates/infer/src/constraints/mod.rs:231-237`).

`AnalysisSession::route_constraint_events` forwards the event to `constrain_nominal_cast` at
`crates/infer/src/analysis/session/lifecycle.rs:402-410`. The latter clones all matching candidates,
returns silently when there are none, and instantiates every candidate otherwise at
`crates/infer/src/analysis/session/generalize.rs:892-921`.

Compact generalization is a second ingress. `find_next_compact_cast` scans constructor pairs and
tests only whether the pair has any candidate at `crates/infer/src/compact/casts.rs:31-48`.
`AnalysisSession::generalize` then constrains every application in the selected batch at
`crates/infer/src/analysis/session/generalize.rs:187-199`, eventually reaching the same
`constrain_nominal_cast` through `constrain_compact_cast` at
`crates/infer/src/analysis/session/generalize.rs:874-890`.

The compact scan is discovery, not by itself proof that every missing constructor pair is an
invalid subtype boundary. `Missing` must therefore mean “not a compact cast ingress” there, while a
`Missing` result for an actual `NominalCastNeeded` event is a failed required boundary.

### 2.3 Primary specialize2 paths

The public `specialize()` entry point delegates to specialize2 at
`crates/specialize/src/lib.rs:76-78` and `crates/specialize/src/specialize2/mod.rs:80-82`.

Its type graph reaches `TypeGraph::constrain_direct_cast` for different constructor paths at
`crates/specialize/src/specialize2/type_graph.rs:360-382`. That function filters every matching
poly value-cast rule, instantiates them all, and returns `Ok(())` even for an empty set at
`crates/specialize/src/specialize2/type_graph.rs:475-500`.

Emission performs an independent lookup. `direct_cast_rule` uses first-match `.find(...)` at
`crates/specialize/src/specialize2/candidate/surface.rs:608-631`.
`cast_boundary_instance` converts that first rule to an instance at
`crates/specialize/src/specialize2/emit.rs:1017-1028`; no match becomes `Ok(None)`, after which
ordinary boundary emission can produce a `Coerce` (`crates/specialize/src/specialize2/emit.rs:987-1014`).

Finally, specialize2's boolean `type_candidate_subtype` treats `.any(...)` matching cast declaration
as subtype evidence at `crates/specialize/src/specialize2/effect.rs:3-14`. It cannot currently
distinguish unique evidence from ambiguous evidence.

### 2.4 Function-result shape gates

Function-result lowering does connect the body computation to the annotation at
`crates/infer/src/lowering/expr/method_body.rs:1685-1721`. Before that connection,
`check_result_annotation_type` calls only `compact_type_matches_signature_shape` at
`crates/infer/src/lowering/expr/method_body.rs:1796-1809`. For builtin/named/applied expectations,
that helper accepts any compact constructor-shaped actual at
`crates/infer/src/lowering/signature_match.rs:35-58`.

After generalization, `deferred_result_annotation_errors` calls `poly_pos_matches_signature` at
`crates/infer/src/lowering/body/mod.rs:2416-2444`. Its builtin/named/applied branch accepts any
`Pos::Con` at `crates/infer/src/lowering/body/mod.rs:2482-2511`.

These shape helpers cover structural alternatives beyond direct nominal casts. They must not query
the new registry directly. The concrete `int`-as-`bool` case is rejected because its already-created
`NominalCastNeeded` request resolves to `Missing`, not because shape checking is redefined.

### 2.5 Legacy alternate specialization path

`specialize_roots` remains a public alternate entry at `crates/specialize/src/lib.rs:116-121` and
uses the older `solve`/`Specializer` path rather than specialize2. Its
`ConstraintGraph::constrain_direct_cast` repeats the all-candidates/empty-success behavior at
`crates/specialize/src/solve/constraint_graph.rs:339-365`. Its closed-candidate subtype helper uses
`.any(...)` at `crates/specialize/src/solve/constraint_graph.rs:412-427`, reached from
`crates/specialize/src/solve/candidate.rs:474-484`.

Whether this legacy API is included in the initial activation is an explicit decision point in
Section 15. It must not be accidentally claimed as covered merely because the primary
`specialize()` route is fixed.

### 2.6 Real-std compatibility evidence

`lib/std/core/convert.yu:5-8` contains all four current std value casts:

```text
path -> bytes
int  -> frac
int  -> float
frac -> float
```

No source/target pair is duplicated. The constructor-pair policy therefore has no known real-std
ambiguity, and nothing in this scan obviously depends on missing-cast success.

## 3. Prior art: Stage 5 role-impl conformance

Stage 5 already introduced the required three-way idea for a narrower, role-impl-only proof path.
`VisibleCastLookup` classifies `Missing`, `Unique`, and `Ambiguous` from the inference cast table at
`crates/infer/src/role_impl_conformance/view.rs:373-435`. The conformance outcome has a distinct
`AmbiguousCast` result at `crates/infer/src/role_impl_conformance.rs:906-915`, and the comparison
rejects that result at `crates/infer/src/role_impl_conformance.rs:1157-1173` and `1193-1201`.

That implementation is precedent, not the shared API:

- it lives under `infer`, so `specialize` cannot import it without reversing the dependency;
- `Unique` carries no selected rule;
- it is scoped to immutable role-impl conformance views rather than ordinary cast application;
- it does not solve ordinary missing-cast diagnostics or specialize emission.

The new neutral classifier may later replace its raw cardinality helper through a thin adapter, but
changing role-impl conformance semantics is not required by this project.

## 4. Required invariant and project scope

For an ordinary required nominal boundary from source constructor path `S` to target constructor
path `T`, the compiler must apply exactly one of these outcomes:

```text
0 matching visible value-cast declarations  => Missing; reject the required boundary
1 matching visible value-cast declaration   => Unique(rule); use that rule
2+ matching visible value-cast declarations => Ambiguous(rules); reject without choosing
```

Passing ordinary cast resolution must imply all of the following:

1. infer and specialize classify the same visible declaration set by the same cardinality rule;
2. zero candidates cannot discharge a required nominal subtype relation;
3. multiple candidates cannot be constrained together and cannot be reduced by declaration order;
4. only the `Unique` payload may contribute cast constraints, cast-based subtype evidence, or a
   runtime cast instance;
5. missing or ambiguous different-constructor boundaries cannot fall through to a bare runtime
   `Coerce` as though a cast had been resolved;
6. effect-up cast behavior is unchanged;
7. no path/module/function-name special case is introduced;
8. no additional inference/generalization fixed point is introduced.

The initial project does not include:

- role-impl conformance policy beyond optional reuse of the neutral classifier;
- generic-argument-aware candidate viability;
- a complete audit or rewrite of `compact_type_matches_signature_shape` and
  `poly_pos_matches_signature`;
- indirect or multi-hop cast search;
- cast precedence, declaration-order tie-breaking, or “most specific cast” rules;
- effect-up cast resolution;
- a new runtime coercion fallback.

## 5. Decided ambiguity granularity

The already-approved initial policy is:

> Ambiguity is defined by multiple visible declarations for the same
> `(source constructor path, target constructor path)` pair.

The classifier does not first instantiate each scheme and ask which candidates remain viable for
the concrete type arguments. A pair with two declarations is `Ambiguous` even if their generic
schemes would be applicable to disjoint argument sets.

Rationale:

- it matches the Stage 5 `VisibleCastLookup` policy already exercised against real std;
- both infer and specialize already possess the constructor pair at every relevant lookup seam;
- it makes resolution deterministic before mutation or emission;
- it avoids building a second speculative instantiation/constraint solver merely to decide
  cardinality;
- it fails closed when the compiler cannot prove one declaration is authoritative;
- the current std has no duplicate pair and therefore provides a low-risk compatibility baseline.

The deliberate tradeoff is conservative false ambiguity. For example, two generic declarations
with the same constructor pair but provably disjoint applicable type arguments will still be
rejected when that pair is requested, even if only one would survive full instantiation. This risk
is accepted for the initial implementation.

Generic-argument-aware viability is explicitly deferred as a future refinement. It must not be
smuggled into an initial slice, and it must not weaken the rule through declaration-order fallback.
Any future refinement needs its own applicability semantics, termination argument, ambiguity tests,
and cache/import visibility audit.

## 6. Shared classifier design

### 6.1 Neutral result type

Add a neutral module below both consumers, proposed as `poly::cast_resolution`, with a payload-generic
result:

```rust
pub enum OrdinaryCastResolution<R> {
    Missing,
    Unique(R),
    Ambiguous(Vec<R>),
}

pub fn classify_ordinary_cast_candidates<R>(
    candidates_for_exact_pair: impl IntoIterator<Item = R>,
) -> OrdinaryCastResolution<R>;
```

`Ambiguous` has the invariant that its vector contains at least two declarations. The helper must
consume only candidates already restricted to:

- `CastRuleKind::Value`;
- exact source constructor path equality;
- exact target constructor path equality.

Pair selection remains in thin registry adapters because infer stores a keyed `CastTable` while
specialize reads a flat `poly::Arena::cast_rules` vector. The cardinality semantics and result shape
live once in `poly`.

The generic payload lets each caller preserve what it needs without coupling layers:

- infer may classify cloned inference `CastRule` values so it can later mutate the solver and retain
  schemes, IDs, and weights;
- specialize may classify borrowed or cloned full `poly::expr::CastRule` values, retaining concrete
  `Type::Con` endpoints at its call site;
- diagnostics may project an ambiguous payload to stable declaration IDs after classification.

The result type contains no `PosId`, `NegId`, `Type`, weights, source range, or solver state. Those
belong to the caller's request context, not to cardinality classification.

### 6.2 Registry adapters

The intended adapters are conceptually:

```rust
CastTable::resolve_value(source_path, target_path)
    -> OrdinaryCastResolution<infer::casts::CastRule>

resolve_poly_value_cast(arena, source_path, target_path)
    -> OrdinaryCastResolution<&poly::expr::CastRule>
```

Exact names may follow existing module conventions, but callers must not regain direct access to
`.is_empty()`, `.any(...)`, `.find(...)`, or “iterate every candidate” as an alternative resolution
policy.

### 6.3 Declaration identity and deterministic payloads

Classification counts declarations, not successful instantiations. The registry contract should be
one entry per visible declaration. If cache/prefix merging can duplicate the same declaration entry,
that is registry hygiene rather than a language-level second declaration and must be characterized
before activation.

Ambiguous diagnostic candidates should be rendered in a stable identity order, preferably `DefId`
or stable source identity rather than registry/import order. This sorting is diagnostic-only; it
must never select a winner.

## 7. Policy at each current decision path

| Consumer | `Missing` | `Unique(rule)` | `Ambiguous(rules)` |
| --- | --- | --- | --- |
| infer `NominalCastNeeded` | record a missing-implicit-cast failure; add no cast constraint | instantiate exactly that scheme with the original endpoints/weights | record an ambiguous-implicit-cast failure; add no candidate constraints |
| infer compact discovery | skip: the scan alone does not prove a required cast | return/apply the batch through exactly that rule | terminate that pair as ambiguous; add no candidate constraints and do not normalize it as applied |
| specialize2 `constrain_direct_cast` | return an unsatisfied subtype/missing-cast error | instantiate exactly that rule and constrain it to the concrete pure-function boundary | return an ambiguous-implicit-cast error before instantiation |
| specialize2 emission | for different nominal paths, return the corresponding missing failure rather than a bare `Coerce` | instantiate exactly the classified rule | return the ambiguous error; never call `ensure_def_instance` for a winner |
| specialize2 boolean subtype evidence | `false` | `true` | `false`; ambiguity is not subtype evidence |

The boolean API loses the reason for `false`. Section 15 leaves open whether a richer internal
relation is needed so an ambiguity first observed through candidate comparison can retain its
specific diagnostic rather than later appearing as a generic conflict. The minimum semantic rule
is fixed: only `Unique` may yield `true`.

For compact generalization, a rejected/diagnosed ambiguous pair needs terminal bookkeeping separate
from `applied_casts`; otherwise a continuing diagnostic build could rediscover it on every restart.
It must not be inserted into `applied_casts`, because that would falsely certify cast normalization.

Infer and specialize need not share one mutable registry object. The infer table is working state
and `poly::Arena::cast_rules` is the durable downstream surface. Characterization must instead prove
that both contain the same visible value declarations and that both adapters produce the same
classification.

## 8. Missing and ambiguous diagnostics

### 8.1 Minimum semantic vocabulary

Infer/check needs distinct structured outcomes equivalent to:

```rust
AnalysisDiagnostic::MissingImplicitCast { source, target, /* origin */ }
AnalysisDiagnostic::AmbiguousImplicitCast {
    source,
    target,
    candidates,
    /* origin */
}
```

Specialize needs an explicit ambiguous variant, conceptually:

```rust
SpecializeError::AmbiguousImplicitCast {
    actual,
    expected,
    candidates: Vec<poly::expr::DefId>,
}
```

For specialize missing-cast failure, the smallest compatible design is
`SpecializeError::UnsatisfiedSubtype` with a new
`UnsatisfiedSubtypeOrigin::MissingImplicitCast` carrying the constructor pair. A separate top-level
missing-cast error remains possible if formatting or provenance requires it.

Current vocabulary has neither cast result: `AnalysisDiagnostic` contains only computed-fetch-cycle
and effect-filter failures at `crates/infer/src/analysis/work.rs:11-22`, while `SpecializeError` has
typeclass ambiguity but no cast ambiguity at `crates/specialize/src/lib.rs:123-194`.

### 8.2 Required content

A user-facing diagnostic should distinguish:

- actual/source constructor and expected/target constructor;
- no visible cast versus multiple visible casts;
- every ambiguous declaration, with related locations when available;
- the expected boundary site, not merely an internal slot or runtime `Coerce`;
- struct-field and function-result context when provenance can identify it.

Conceptual messages are:

```text
cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
```

```text
implicit cast from `int` to `frac` is ambiguous: 2 visible declarations match
```

Exact wording, stable codes, and hint text require review before the diagnostic slice is activated.

### 8.3 Provenance constraint

The current `NominalCastNeeded` event has no source site, and infer's value-cast rule has no `DefId`.
High-quality primary and related ranges therefore cannot be obtained from the classifier alone.
The implementation must make an explicit choice among:

- extending the originating constraint/event with an owner or `SourceSpan`;
- retaining a boundary-provenance table keyed by stable constraint/event identity;
- providing a definition-level primary range first, with a separately approved follow-up for exact
  field/result-expression ranges.

It must not recover a range by rescanning CST in diagnostics. Recent selection and role-impl
diagnostic work already preserves structured source provenance; ordinary casts should follow that
direction rather than introducing a display-only side channel.

## 9. Bounded repair of function-result annotations

This project's function-result claim is intentionally narrow:

```text
body result `int`
declared result `bool`
existing constraint produces required nominal cast `int -> bool`
shared resolution returns Missing
check rejects the function
```

Neither `compact_type_matches_signature_shape` nor `poly_pos_matches_signature` should call
`CastTable`, `poly::Arena::cast_rules`, or the new registry adapter. They handle variables,
functions, tuples, effects, unions, and other structural alternatives that do not reduce to one
constructor-pair lookup.

The following remain out of scope and separately tracked:

- completeness of constructor identity and type-argument comparison inside the shape gates;
- generic result annotations whose validity depends on binder correlation;
- structural result mismatches that never produce `NominalCastNeeded`;
- deciding whether either shape helper should eventually be replaced by a richer immutable relation.

Project completion must nevertheless include a regression proving that the concrete `int`-literal
as `bool` result is rejected. The separate general audit may remain open without weakening that
exit witness.

## 10. Emission and proof ownership

Inference/check should normally reject source programs before specialization. Specialize2 must still
enforce the same policy because it consumes durable poly arenas, can be tested or called directly,
and owns runtime cast emission.

The two stages have distinct responsibilities:

- infer proves that an ordinary source boundary has one visible cast scheme and applies its
  inference constraints;
- specialize proves that the durable arena still has one matching declaration for the concrete
  boundary and materializes that declaration's instance;
- emission does not trust a previous first-match side effect or infer-only table;
- neither stage treats the other's future failure as its own success case.

The initial design does not require serializing a selected cast application ID into poly IR. Under
the decided constructor-pair uniqueness rule, reclassification of the durable registry yields the
same unique declaration. If characterization finds infer/poly registry divergence, activation must
stop rather than add a fallback selection record to hide it.

## 11. Performance and fixed-point policy

Lookup should remain linear in the small candidate bucket or flat poly rule list. If the durable
rule list becomes a measurable hot path, an immutable pair index may be built once per arena or
specialization session; it must not be rebuilt per boundary.

The design forbids:

- instantiating every candidate before deciding ambiguity;
- a viability-search fixed point over generic arguments;
- repeating full registry scans after a result is known at the same boundary;
- applying all ambiguous schemes and hoping constraints eliminate all but one;
- declaration-order or import-order tie-breaking;
- CST rescans for diagnostic provenance;
- changing inference co-occurrence, polarity elimination, or residual simplification to protect a
  cast result;
- adding a runtime `Coerce` fallback for a missing or ambiguous nominal cast.

Ambiguity classification is `O(k)` in the number of declarations for one exact pair and may stop
counting after two if no diagnostic candidate list is required. If diagnostics list every candidate,
collecting the full bucket is appropriate and remains independent of type-scheme instantiation.

## 12. Implementation stages and slices

All source changes are deferred to follow-up tasks. The slices below preserve the established
pattern: characterize first, introduce inert structure, wire shadow observations, add inert
diagnostic vocabulary, then activate semantics in small independently reviewable steps.

### Slice OCAST-A: cross-pipeline characterization

Size: S-M. Risk: medium-high.

Add focused test-only witnesses without changing production behavior:

- struct field `bool` receiving `int`;
- function result `bool` returning an `int` literal;
- zero, one, and two declarations for one constructor pair;
- declaration-order reversal for the ambiguous pair;
- the decided conservative generic case: two same-pair schemes with disjoint-looking arguments are
  still classified as ambiguous by the oracle;
- direct `NominalCastNeeded` and compact-generalization ingress;
- specialize2 type-graph, emission, and boolean-subtype seams;
- infer `CastTable` versus durable `poly.cast_rules` parity, including cached-prefix seeding;
- repeated identical cast events and any repeated imported registry entry;
- the four real-std value casts and their unique pair count;
- the legacy `specialize_roots` route, recorded separately from primary specialize2.

Exit witness: one test report/table records current outcome and expected `Missing`/`Unique`/
`Ambiguous` oracle at every seam; production behavior and public diagnostics are unchanged.

### Slice OCAST-B: neutral classifier construction

Size: S. Risk: low.

Add `poly::cast_resolution::OrdinaryCastResolution<R>` and
`classify_ordinary_cast_candidates`, with unit tests for zero, one, two, and stable full ambiguous
payloads. Add no production caller.

Document and test the precondition that input candidates are value rules for one exact constructor
pair. Do not add generic scheme viability.

Exit witness: both infer-rule and poly-rule-shaped test payloads can be classified without `poly`
depending on infer or specialize; no compiler output changes.

### Slice OCAST-C: infer adapters and shadow observation

Size: M. Risk: medium-high.

Add an inference registry adapter returning the shared result. Observe, but do not enforce, the
result at:

- `constrain_nominal_cast` event handling;
- `find_next_compact_cast`/compact batch selection;
- prefix-seeded and source-local cast tables.

Retain current constraints and success behavior during this slice. Capture enough test-only or
inert structured evidence to compare old behavior with the new classification. If approved for
diagnostics, retain value-cast `DefId` through local registration and prefix seeding in this slice;
that identity change is structural and must not affect candidate schemes.

Exit witness: direct and compact paths report the expected three-way shadow result, local/prefix
registries agree with poly, owner scheduling observes no new mutable production dependency, and all
existing behavior remains unchanged.

### Slice OCAST-D: specialize2 adapters and shadow observation

Size: M. Risk: medium-high.

Add the poly registry adapter and shadow it at:

- `TypeGraph::constrain_direct_cast`;
- `direct_cast_rule`/`cast_boundary_instance`;
- `type_candidate_subtype`'s cast-evidence branch.

Keep the old permissive/first-match result as production behavior until activation. The shadow
surface must prove that constraint solving, emission, and boolean subtype comparison classify the
same exact candidate set.

Exit witness: constructed arenas produce identical three-way observations at all three specialize2
seams, including ambiguity under declaration-order reversal; emitted/runtime behavior is still
unchanged.

### Slice OCAST-E: inert diagnostic vocabulary and provenance seam

Size: M. Risk: medium.

Add the approved infer/check missing and ambiguous variants, specialize ambiguity variant, and the
chosen specialize missing-cast origin. Wire formatting, stable codes, structured expected/actual
fields, candidate lists, and source-related information behind constructors that are not yet
reached by production cast resolution.

Add diagnostic unit/golden tests for missing and ambiguous outcomes. Implement only the approved
provenance floor; do not rescan syntax to improve a range.

Exit witness: each new structured error renders deterministically in CLI/check diagnostic tests and
candidate ordering is stable, while existing source programs still follow pre-activation semantics.

### Slice OCAST-F: infer semantic activation

Size: S-M. Risk: high.

Switch direct infer resolution to:

- diagnose `Missing` once for a required `NominalCastNeeded` boundary;
- instantiate only `Unique(rule)`;
- diagnose `Ambiguous` once and instantiate no candidate.

Switch compact ingress to skip `Missing`, apply only `Unique`, and terminally record `Ambiguous`
without marking it successfully applied. Add the approved diagnostic deduplication key.

Exit witness:

- the struct-field and concrete function-result repros fail during check with missing-cast
  diagnostics;
- the duplicate-pair repro fails during check with an ambiguity diagnostic regardless of
  declaration order;
- a unique declared cast retains its inferred type and behavior;
- four real-std casts produce zero new diagnostics;
- no owner-level scheduling contract or generalization termination test regresses.

### Slice OCAST-G: primary specialize2 semantic activation

Size: M. Risk: high.

Switch specialize2 type-graph constraint, emission, and boolean subtype evidence to the shared
result. `Missing` and `Ambiguous` must error before a nominal boundary becomes a bare `Coerce`;
`Unique` must instantiate the same declaration at constraint and emission seams; the boolean helper
must return true only for `Unique`.

Exercise this slice with direct/constructed poly arenas so infer's earlier rejection cannot mask a
specialize regression.

Exit witness:

- direct specialize2 tests reject missing and ambiguous nominal boundaries with the intended
  structured errors;
- declaration order cannot change the selected runtime instance;
- the unique-cast positive fixture emits that cast instance;
- no invalid different-constructor boundary reaches runtime as a bare `Coerce`;
- repository std and primary runtime/diagnostic contract suites pass.

### Conditional Slice OCAST-H: legacy `specialize_roots` parity

Size: S-M. Risk: high.

This slice is required only if Claude and the user place the legacy path in initial scope. Replace
the old `solve::ConstraintGraph` all/empty and boolean `.any(...)` policies with the shared
classification, add direct legacy-route tests, and state any emission limitation explicitly.

If the path is declared out of scope, do not silently omit it: record that the ordinary-cast
soundness guarantee covers primary `specialize()`/specialize2 only, retain a regression that exposes
the legacy difference, and open a retirement/parity follow-up.

Exit witness if included: legacy and primary direct-cast outcomes agree for zero, one, and multiple
candidates. Exit witness if excluded: the approved scope boundary is explicit in tests/docs and no
primary-route acceptance gate invokes `specialize_roots` as proof of parity.

## 13. Slice dependencies and activation gates

The required order is:

```text
OCAST-A characterization
    -> OCAST-B shared inert type
    -> OCAST-C infer shadow
    -> OCAST-D specialize2 shadow
    -> OCAST-E inert diagnostics
    -> OCAST-F infer activation
    -> OCAST-G specialize2 activation
    -> OCAST-H only under the legacy-scope decision
```

OCAST-C and OCAST-D may be implemented as separate commits and reviewed independently after
OCAST-B, but semantic activation must not begin until both shadow classifications agree on all
OCAST-A pair-cardinality witnesses.

OCAST-F is the first source/check semantic change. OCAST-G is a separate enforcement boundary, not
cleanup that may be omitted because source programs now fail earlier.

Before either activation slice:

- diagnostic vocabulary and minimum provenance must be approved;
- repeated-event behavior must have a deterministic deduplication rule;
- local and prefix-imported infer registries must agree with durable poly rules;
- the four std casts must remain `Unique`;
- the generic-argument-aware refinement must remain out of scope.

## 14. Compatibility, rollback, and failure policy

OCAST-A through OCAST-E are characterization/structure/shadow slices and should be independently
removable without source-language behavior change. OCAST-F and OCAST-G are deliberate fail-closed
semantic changes.

If activation rejects an existing program:

1. classify whether it relied on a genuinely missing cast, a duplicate constructor pair, registry
   duplication of one declaration, or a classifier bug;
2. do not restore empty-success, all-candidates, `.any(...)`, or first-match behavior;
3. do not add a source/module/function-name exception;
4. if the case is two same-pair generic casts with disjoint applicability, record it as the known
   conservative-policy cost rather than implementing viability ad hoc;
5. roll back the activation slice while retaining shadow evidence if the shared registry invariant
   or diagnostic ownership is not ready.

No valid unique-cast program should change runtime semantics. Missing-cast and ambiguous-cast
programs are intentionally incompatible because their current acceptance is unsound or
order-dependent.

## 15. Unconfirmed and deferred points

The ambiguity granularity in Section 5 is resolved and must not be reopened during implementation.
The following points still require a Claude/user decision before or during the named slices:

1. **Legacy `specialize_roots` scope (before OCAST-G closeout).** Include it in the initial guarantee,
   explicitly exclude it with a follow-up/retirement plan, or retire the public alternate path.
2. **Exact diagnostic vocabulary (before OCAST-E).** Choose variant names, stable diagnostic codes,
   primary wording, hint text, and whether missing specialize resolution is a top-level error or an
   `UnsatisfiedSubtypeOrigin::MissingImplicitCast`.
3. **Source-range provenance floor (before OCAST-E/F).** Decide whether activation requires exact
   expression/field/result-annotation ranges, whether definition-level attachment is an acceptable
   first floor, and which constraint-origin representation carries that fact without CST rescans.
4. **Ambiguous candidate provenance (before OCAST-C/E).** Decide whether inference `CastRule` should
   retain a mandatory value-cast `DefId`, or whether diagnostics should map the result to durable
   poly rules through another stable identity. Current inference value rules carry `None`.
5. **Boolean subtype API shape (before OCAST-G).** A minimal adaptation maps only `Unique` to true.
   A richer enum can preserve `Ambiguous` for a more specific downstream diagnostic. Choose whether
   that restructuring belongs in this project or whether the minimal false result is sufficient.
6. **Repeated `NominalCastNeeded` deduplication (before OCAST-F).** Choose the user-facing key: exact
   solver endpoints plus pair, owner/site plus pair, or another stable boundary identity. Repeated
   propagation must not flood diagnostics, but distinct source boundaries must not be collapsed.
7. **Compact ambiguous terminal state (before OCAST-F).** Choose the exact non-success bookkeeping
   key that prevents rediscovery without inserting the pair into `applied_casts`.
8. **Duplicate registry representation (during OCAST-A/C).** Confirm that one declaration cannot be
   inserted twice through source/prefix/cache merging, or define stable-identity deduplication before
   counting declarations.
9. **Use-site versus declaration-time ambiguity (before OCAST-F).** The proposed project rejects
   ambiguity when an ordinary cast pair is requested. Decide whether duplicate visible pair
   declarations should also be rejected when unused; that would be a broader declaration-registry
   rule and should not be introduced accidentally.
10. **Stage 5 adapter reuse (after OCAST-B).** Decide whether role-impl `VisibleCastLookup` should
    delegate to the neutral classifier in this project. This is cleanup only; its established
    conformance semantics must not change.

The following point is deferred by explicit prior decision, not awaiting an implementation choice:

11. **Generic-argument-aware viability.** Same constructor-pair declarations are ambiguous before
    scheme instantiation, even when their applicable type arguments appear disjoint. A more precise
    policy is a future design project.

The following broader function-annotation work also remains separately tracked:

12. **Complete result-shape audit.** Structural alternatives in
    `compact_type_matches_signature_shape` and `poly_pos_matches_signature` are not certified by the
    concrete `int`-as-`bool` repair.

## 16. Overall project exit criteria

The ordinary-cast project is complete only when:

- the struct-field `S { x: 42 }` against `x: bool` repro produces a compile/check diagnostic rather
  than reaching a runtime boundary;
- the duplicate same-pair cast repro produces an ambiguity diagnostic and declaration order cannot
  choose runtime behavior;
- `my f(): bool = 42` is rejected even though the general function-result shape audit remains open;
- infer direct-event and compact ingress use the shared three-way classifier with their documented
  `Missing` policies;
- specialize2 type-graph constraint, emission lookup, and boolean subtype evidence use the same
  classifier, and only `Unique` is positive cast evidence;
- missing or ambiguous different-constructor boundaries cannot be emitted as bare `Coerce` nodes;
- unique value casts still infer, specialize, and execute through the same declaration;
- the four std value casts remain unique and real std passes with zero new cast diagnostics;
- local, cached-prefix, cold, and warm visible cast surfaces agree where those routes are supported;
- missing and ambiguous diagnostics are structured, deterministic, and satisfy the approved
  source-provenance floor;
- no generic-argument viability solver, inference simplification protection, extra fixed point, or
  name-based special case was added;
- the `specialize_roots` legacy scope decision is explicitly recorded and its corresponding exit
  witness is met.

Completion of this project does not declare the full function-result-annotation conformance report
closed. It closes only the concrete nominal-cast-reducible `int`-literal-as-`bool` case; the shape
checker audit remains an explicit separate concern.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-21 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.
