# Integer value inclusion at the actual common export: source bridge attempt

Date: 2026-10-08
Baseline: `2569c0182e2c562d176c837b4d60e0ee693d8c02`
Branch: `research/simple-sub-intrusion`
Status: compiler-referee reviewed bounded research attempt; gate remains open
Claim class: bounded producer characterization and conditional proof-cut localization
Exclusive lease: this note only
Semantic/implementation authority: none
Review: compiler_referee PASS on content SHA-256 `7cc45e74b559a830b10b6095c6695a60bc7bfeeb16981a56901b9f8e90de1242`; no correctness findings

## Objective, method and result

Attempt the preceding [actual-export note](2026-10-08-principal-actual-export-rule-attempt.md)'s
nonidentity `VIncl(A,B)` leaf on the smallest concrete source value with
explicit retained producer clauses: integer literal `1`, candidate endpoints
`Int` and `Top`. Inspect its producer, then try to carry the same decorated
value through a constant function's result to the actual ordinary
`B_common` query. This is manual rule extraction, not another abstract DAG
construction or F5 kernel experiment.

The ordinary integer producer is present. It emits exact value/effect facts
with original occurrence identity. It does not emit or interpret the complete
decorated `DescMem(Int,...)`/`DescMem(Top,...)` judgments required for current
`VIncl`. The attempt therefore stops at an explicit primitive interpretation
and decoration cut, before constructing current `VIncl(Int,Top)`. Even granting
that semantic inclusion leaves the preceding note's actual-root evidence cut:
the restricted §5.3 Function rule requires unchanged non-coverage interfaces.
No concrete current nonidentity inclusion, accepted `Direct`, counterexample,
`ALL_VIEW` or `PRINCIPAL` closure is established.

## Governing sections and retained decisions

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, 3.1–3.3, 3.7, 5.1, 5.3, 10: independently supplied primitive and
  descriptor interpretation, complete active membership/admission, source
  inventory, Option 2 alternatives and restricted candidate evidence rules.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6's literal/Lambda/Result synthesis, §7's decorated checking proposition,
  §9's complete invocation and domain/observation law.
- Authoritative [FVIEW](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–2, 5: source annotations, inferred schemes and internal views are
  distinct; original profiles/paths/ownership and joint dependencies come
  from source elaboration, whose detailed judgments remain open.
- [Compatibility](../design/2026-10-03-concrete-compatibility-boundary.md)
  §§1, 3, 5–5.1: one inequality, local concrete evidence, limited structural
  applicability; acceptance does not itself prove identity realization.
- Authoritative [F4](../design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md)
  §6 and retained [F5](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md)
  §§1–2, 21–22 provide the ordinary producer/kernel lead within their scopes.
  [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§1–2 keeps
  F4's Integer scope and withdraws F5 generalization as the successor target;
  §13 preserves typed-value transport. F5 kernel success is not current
  decorated membership or complete Function resolution authority.
- [Certified use](../design/2026-10-04-certified-callback-and-constrained-use.md)
  §2.1 carries independently supplied complete presentations;
  [safe preimage](../design/2026-10-04-common-allowance-context-preimage.md)
  §3.2 keeps admission separate from output inclusion.

The pinned committed Option A, Option 2, inlet-context and FVIEW answers were
checked against live bytes. They select independent complete membership,
permit independently licensed extras without source anchors, and quantify
over every independently typed compatible punctured context at original
`xi=(nu,K,D)`. They do not select concrete primitive membership or evidence
rules. The primary supplied the prior F5 finding: `Int <: Top` succeeds
without mutation, and its result-only Function lift is a kernel lead with
decorated-membership and actual-root correspondence still open. No separate
committed kernel-audit note was identified; no independent re-audit is claimed.
Frozen Oracle was not inspected or used as authority.

## Smallest concrete producer and first cut

For literal occurrence `o`, write its existing value/effect components as
`v_o,e_o`. Current `emit_integer` at `crates/yu-solver/src/lib.rs:1551`
emits the following original occurrence-local facts:

```text
slot 0: IntPositive <: v_o
slot 1: v_o <: IntNegative
slot 2: EffectBottomPositive <: e_o
slot 3: e_o <: EmptyEffectNegative
slot 4: v_o <: definition.root     [only for a direct definition body]
```

For a lambda's literal body, slot 4 is absent; F5 §21 routes the body value
into the Function result. This confirms the concrete producer described by
the [value-skeleton note](2026-10-04-production-f5-value-skeleton-selector.md).
It creates no source annotation or conversion. Typed-core §6 synthesizes
`Value(type of literal)` and normalizes it to `result(literal 1)`; choosing
`Int` for that ordinary literal agrees with the retained Integer contract.

Now let `delta_o=(profile_o,path_o,K,D,lineage_o)` denote the required
**original** decorations, at the source scope tree `T`. This is notation for
the proof's missing supplied data, not a constructed packet. Occurrence `o`
does not define `profile_o`, its typed result path or lineage. Pure evaluation
does not prove these predicates empty or erase ambient `K,D`. No per-port
assignment, new origin or fresh profile is selected.

The desired semantic premise is

```text
for every original xi and every same decorated value z:
  MemValue(Int,z;delta_o,xi,T)
    implies MemValue(Top,z;delta_o,xi,T).
```

`MemValue` abbreviates the complete independently interpreted value judgment;
it is not a proposed solver atom. For the actual produced literal one also
needs its introduction/descriptor typing judgment. Source-contracts §2.2
explicitly requires independent `DescMem`, and §3.2's Literal row requires
the original whole-tuple relation and declaration/contract identity. Neither
row defines `DescMem(Int,...)` or `DescMem(Top,...)`; §3.5 assumes the local
typing lemmas. Typed-core §7 names the semantic inclusion and assumes it at
checking. FVIEW supplies a source-generation direction, not its omitted rules.

Thus the first unresolved inference is precisely

```text
the displayed integer facts + original occurrence o
  -/-> complete literal introduction with delta_o
  -/-> same-decoration implication Int to Top.
```

The arrows mark missing correspondence, not logical refutation. F5 §22's
`any positive value <: Top` action proves a kernel outcome in its stated
algebra. It does not define the current decorated `Top` predicate, prove its
compatibility with the literal's original evidence, or emit current checking
evidence. Assuming a universal decorated Top would discharge this cut by
assumption; no inspected rule here supplies that premise. There is no
established strictness witness distinguishing the two current denotations.

## Connection to the actual ordinary Function root

The smallest enclosing current source shape with an explicit retained Lambda
producer is `my f x = 1`. In typed-core notation its constructive skeleton is

```text
lambda(P, result(literal 1)),    P = Value(alpha).
```

The source is unannotated. Its actual role remains Pure, with Value entry;
the candidate argument assignment `alpha=Int` is not an invented annotation
or a generic Value-entry-implies-Pure rule. Compare an independently supplied
target with the same entry, providers, consumers and parameter interface,
whose result value endpoint is `Top`. Keep the actual common export
`B_common(s,W)` and all its residuals; do not substitute a bare kernel Function
for that root. The outward allowance `W` is kept unchanged.

Even here the complete invocation is not merely the pure body return:

```text
Force(incoming whole carrier) >>= (a => Return(1,current_state)).
```

Entry can suspend or diverge and retains the original suffix and resumed
state. The empty body evaluation bound is not a proof that every admitted
incoming carrier has empty support. Checking only `f 1` would miss the
selected complete domain. A prospective certificate must prove

```text
D_target(xi) subseteq D_common(xi)
forall h in D_target(xi). P_common(h;xi) subseteq P_target(h;xi),
```

including arbitrary admitted initial contexts, future histories and Option 2
extras, with one original scoped assignment. Parameter spelling alone does
not establish either clause. We neither delete target challenges nor infer
admission from a lack of returned observations.

Conditionally granting complete same-decoration `Int`-to-`Top` membership,
one can retain the literal/Return witness at a positive result incidence
**if** the independent descriptor constructor typing has the corresponding
monotonicity. That is a semantic prefix, not §5.3 evidence. Its primitive
`Eq` rule requires matching relation identity and operands. `Guarantee` and
`Absorb` vary eligible allowance leaves within a fixed value envelope; the
result endpoint change is outside those rules. Congruence needs the missing
child proof. The parent `Function` rule explicitly requires the same
non-coverage interface, so granting a semantic child inclusion alone does
not make that rule applicable. Certified freshening/use preserves supplied
evidence and cannot introduce this missing case.

This identifies two separate conditional premises: a complete decorated
primitive introduction/inclusion law for the literal, then an applicable
ordinary actual-root resolution clause accepting the result-interface change
and its complete domain/membership evidence. If an existing clause supplies
them, use that clause; no new rule or rejection policy is adopted here.

## Coverage, independence, failure conditions and resources

Coverage is one literal producer and one constant-Lambda embedding, plus the
exact cited source/descriptor/checking clauses. This is a minimized attempted
derivation, not a counterexample or a repository-wide absence theorem. No
record inclusion, adapter, recursive value, unknown handler profile or other
primitive was searched. Larger abstract models would leave this same source
premise untouched, so no toy-model follow-up was run.

There is no executable oracle. Source-contract primitives and decorations are
shared supplied assumptions of the conditional packages; a checker accepting
those assumptions would establish consistency, not their source validity.
No seeds/ranges, enumeration or executed mutations apply. Symbolic failure
conditions are: missing primitive typing, changed/lost decorations, changed
admission or providers, omission of production extras, replacing the actual
root, or using kernel acceptance as identity/evidence. Any one prevents the
indicated bridge; unchanged printed ports do not repair it.

Checks: bounded `rg`, `sed`, `cat`; read-only HEAD/branch; baseline/live byte
comparison and SHA-256 of dependencies; final leased-note whitespace/scope
inspection. Zero builds, tests, executable probes, formatters, children or Git
mutations. Sequential lightweight reads and one Python dependency process;
no heavyweight process. No numeric CPU/RAM/wall-time limit was assigned.
Peak RSS, CPU and total reasoning wall time were not measured. Some broad
navigation captures were truncated; decisive sections were reread narrowly.
Review is pending; the producer does not independently certify this note.

Recommended next action: locate or derive the independently interpreted
Integer/Top value introduction and inclusion clauses on the original decorated
literal packet; only after that premise is available, assign the applicable
ordinary result-widening resolver clause at `B_common` with complete admission.

## Dependency pins and freeze

All direct dependencies listed below matched pinned baseline bytes at final
recheck. Navigation files were used only to locate sources. Writes stop at
submission; subsequent review repairs require return of this lease.

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29 rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0 rules/question-board.md
7ec6ae3b8ea4048d0407388b23665092a121a3720f8658055dfb5e1046a09c25 notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83 notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16 notes/design/2026-10-03-concrete-compatibility-boundary.md
887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80 notes/design/2026-10-04-certified-callback-and-constrained-use.md
e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e notes/design/2026-10-04-common-allowance-context-preimage.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
43c469aa1169016133f7c6092d1eec3470aac4dce9473ff26a4c85a2662050be notes/progress/2026-10-04-production-f5-value-skeleton-selector.md
9dbf397ec1ea5f9ce5ea8ed732e4c5c5c6bfdb5c9719010d5fc8b002a8f98487 notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md
b259389ec2312d101a3eb1be53dc343f3918fd863abed263b03d8cb9107c1939 notes/progress/2026-10-08-principal-actual-export-rule-attempt.md
7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a questions/2026-10-05-production-function-denotation/approved-answer.md
d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179 questions/2026-10-05-production-function-bound-membership/approved-answer.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3 questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536 questions/2026-10-05-function-call-view-formation/approved-answer.md
235ed5e36f9ad8da1491ed77509fca085de00244f0e0df494d15efb2137e6dfb crates/yu-solver/src/lib.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-principal-vincl-actual-root-bridge-attempt.md`.
- Baseline SHA: `2569c0182e2c562d176c837b4d60e0ee693d8c02`.
- Changed dependency hashes: none; all listed baseline/live comparisons match.
- Claim/review status: compiler-referee PASS on the content hash recorded in
  the header; bounded research only, no source rule or proof gate promoted.
- Checks already run: exact cited-section reads; narrow integer producer
  inspection; committed answer/baseline equality and SHA-256 checks; final
  leased-path/whitespace inspection. Zero builds/tests/probes.
- Proposed message: `research: localize decorated integer inclusion and actual export evidence cuts`.
- Shared-record deltas left for primary/curator: optionally link this concrete
  Integer/Top attempt under the existing `ALL_VIEW`/`PRINCIPAL` value-check
  boundary. Keep decorated primitive interpretation, complete admission,
  actual-root resolution conformance and all-view gates open; add no closed
  theorem or new semantic rule. No shared record, question bundle, compiler,
  manifest, lockfile or other worker artifact was modified.
