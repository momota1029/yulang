# R231 literal producer, admission and readback audit

Status: **MODEL-INCOMPLETE / NO_SAFE_CODE_SLICE**. Research source evidence;
unreviewed. Parent-premise delta **0**. No source-qualified counterexample,
new semantic choice, theorem, production conformance or implementation change
is claimed. Writer `/root/r231_literal_source`; no descendants or coauthors.

## Objective, baseline and authority

Trace actual independent literal generation, admission and readback against
the unchanged `SourceProblem.InferenceSoundness` literal edge, preserving the
same raw literal and original `(q,r,e₀,ξ,ω)`. Method: bounded source inspection
and a constructor-by-constructor correspondence derivation. No executable
experiment was authorized or run.

Primary-supplied baseline: `c5cc9682aa2f4cb90a64d595202adc28ec570887`.
R231 contract SHA-256:
`0d4b3cd7785c580a81b6bc79a69d9e8f4e6bcf13ee141f364d73e914765200c9`.
The baseline is supplied by the primary; this worker ran no Git command or
commit-to-working-file comparison. Dependency bytes below were hashed and the
three assigned Rust owners were rehashed unchanged before writing this note.

Governing sections: R231 “Original target and meaningful outcome,” “Governing
authorities and fixed semantics,” source lane and activation gate; L1
“Adopted introduction” and “Proof and implementation boundary”; R213 “Fixed
outcome”; top-level inference principles §§1, 1.1 and 3; design-authority
authority order and proof-obligation economy; research-lab source-evidence
and stopping rules; git-concurrency exact leases and frozen dependencies.
Root `AGENTS.md`, `AGENTS.pre-sprint.md`, current state and agent-loop README
were read. The yulang-proofs skill was applied only to this source bridge.
The proof lane remains inactive under R231's explicit model gate.

L1 already chooses all eight original payload forms, `Value(τ(l))`, the same
literal value and `Comp(empty,τ(l))`; it expressly supplies neither independent
Simple-sub generation nor solution readout. This audit does not reopen that
choice. R214 and R221's existing carrier obstruction are inherited boundaries;
their one-sided-bound, payload-collision and arbitrary-declaration attacks
were not rerun as new work.

## Bounded characterization of actual owners

The following is a mechanical source derivation. Its hypotheses are an
authentic `LocalSource`/HIR pair accepted by `emit_candidate_source`, successful
collection, a visited literal expression, execution of its queued source
actions, and successful fact admission. These hypotheses describe code paths;
they are not original mathematical satisfaction or a source judgment.

1. **Source formation owner:**
   `crates/yu-hir/src/module/local_source.rs:348–441,677–718,2123–2210`.
   `LocalSourceForm` has Unit, Integer textual spelling, Boolean value, String
   textual spelling and DecodedString text. Integer formation retains the one
   authentic Integer token. Plain string formation retains delimiter-bounded
   spelling, including bytes between delimiters; it is not a proved decoder
   to the original semantic String payload. Boolean introduction recognizes
   `true`/`false` only when not shadowed. Empty parentheses form Unit.
   DecodedString is specifically an authentic interpolation text piece; it is
   not a fifth original L1 literal constructor.
2. **Independent constraint producer:**
   `candidate_source.rs:1043–1082,1097–1100,1140–1147,1585–1606`.
   The entry authenticates the exact `LocalSource` pointer under its HIR and
   source root, verifies each HIR occurrence and records its owner. It allocates
   component positions before solving and chooses primitive leaves directly
   from the source form. The literal case consults neither solver output nor
   `LiteralAtom`, `SourceAssignment`, source judgment or a chosen typing.
3. **Admission owner:** `lib.rs:2185–2202,4007–4038,11546–11600`.
   `emit` retains the actual occurrence and local slot in a cause, with the
   original lower/upper terms. `append_source_facts` and `Action::Fact`
   (`candidate_source.rs:2143,2262–2264,2481`) connect these facts to sequential
   source admission. Admission validates branch-visible terms, ownership,
   matching cause and component kind, then deduplicates semantic term pairs
   while retaining provenance. It does not validate an original source typing
   declaration. `admit_collected_fact` dispatches actual Value/Effect pairs to
   the respective live constraint owners.
4. **Readback owner:** `shadow_apply.rs:2029–2055,2251–2296,2622–2638,
   2779–2810,2862–2884,3028–3050,3066–3090`.
   Export authenticates an owned definition root and a conflict-free completed
   candidate before returning a captured graph. Its root, leaf, row and bound
   APIs expose retained graph structure and session identity. Occurrence
   observation returns exact provenance causes and facts, with explicit
   completeness flags and a hard maximum of 256 rows. These are endogenous
   observations of one solve, not an interpretation of an arbitrary satisfying
   assignment. Graph exports explicitly retain `UNRESOLVED` premises.

## Eight raw payload forms and generated clauses

`OriginalSourceSyntax.lean:42–51` retains the following complete raw payloads;
`OriginalSourceGeneration.lean:85–89` emits the same literal in the local
`literalDeclaration` atom. It does not allocate independent Value/Effect graph
variables in that case.

| Original raw payload | L1 base type | Actual inspected Rust producer |
| --- | --- | --- |
| `unit` | Unit | `LocalSourceForm::Unit` → UnitPositive/UnitNegative |
| `bool b` | Bool | Boolean(b) → BoolPositive/BoolNegative; lexical-shadowing guard retained |
| `int n : Int` | Int | Integer(Box<str>) → IntPositive/IntNegative; textual-to-Int bridge absent here |
| `floatBits bits : Nat` | Float | No corresponding LocalSource literal variant or literal-case branch |
| `string s : String` | String | String(Box<str>) → StrPositive/StrNegative; spelling-to-original-payload decoding unproved |
| `bytes ns : List Nat` | Bytes | No corresponding LocalSource literal variant or literal-case branch |
| `path s : String` | Path | No corresponding LocalSource literal variant or literal-case branch |
| `character s : String` | Char | No corresponding LocalSource literal variant or literal-case branch |

For every supported literal branch above, let `h` be its actual
`HirOccurrenceId`, `Vh = component_term_at(positions[i].value)` and
`Eh = component_term_at(positions[i].effect)`. The exact newly emitted fragment
is:

```text
(h, slot 0): primitivePositive ≤ Vh       [Value]
(h, slot 1): Vh ≤ primitiveNegative       [Value]
(h, slot 2): EffectBottomPositive ≤ Eh    [Effect]
(h, slot 3): Eh ≤ EmptyEffectNegative     [Effect]
```

The facts carry source occurrence and kind, with no raw runtime payload in
the type leaves. That absence is not a defect by itself: syntax can supply the
runtime value, provided the original interpretation links that same syntax
and assignment. This audit does not infer value equality from primitive leaves.

`candidate_component` (`shadow_apply.rs:3873–3899`) allocates a Value and an
Effect component for each occurrence. When `candidate_graph_effects` is false,
it additionally emits provisional pure-effect facts at slots 1 and 2, explicitly
under `CandidatePureEffectModelUnresolved`. The main source solve inspected here
collects with graph effects enabled (`shadow_apply.rs:1819–1822`), so the four
literal facts above are the relevant source fragment; the alternate provisional
mode must not silently be treated as the same clean four-fact inventory.

This source path has both Value bounds, so R214's rejected one-sided candidate
does not describe this branch. Conversely, Rust's polar positive/negative
primitive leaves and EffectBottom/EmptyEffect are not definitionally R220's
single code atom and bottom. Their denotational correspondence is another
unproved bridge, not a consequence of similarly shaped constraints.

## Coordinates, annotations and effect boundary

Collection positions are recipe indices, not source roots or semantic graph
references. `lib.rs:10410–10450` assigns exactly one checked dense live ordinal
per collected component, with separate Value and Effect counters before fact
admission. `component_endpoint`, `value_endpoint` and `effect_endpoint`
(`lib.rs:11830–11923`) translate those positions to live rows and actual primitive
endpoint variants, applying current canonical representatives. No identification
with an original `Site` Nat, `Endpoint.port`, semantic `Root`, event or shared
witness follows from numeric equality.

`candidate_source.rs:1152–1170` aliases an ascription facade to its peeled
child positions/endpoints. Its finish action at `1925–1960` queues an
`Ascription` with the authentic annotation, occurrence, scope, child's endpoint
and computation effect. This is an implementation constraint path; it does not
justify identifying the original `.synthesis` and `.writtenTarget` ports.
`OriginalSourceGeneration.lean:35–43` explicitly keeps the boundary between
those two ports, and `OriginalSourceSyntax.lean:359–368` also distinguishes
`.finalRoot`. In particular `SourceAssignment.row` currently reads finalRoot,
not synthesis (`OriginalSourceInterpretation.lean:830–840`).

The four literal facts constrain that literal's intrinsic computation effect.
They do not discharge enclosing permission, inflow, residual, Call, guard,
future or annotation/conversion obligations. Parent composition emits its own
effect links, for example Sequence child-to-parent facts
(`candidate_source.rs:1702–1712`) and statement-prefix effect links
(`2116–2125`). No equation in these literal facts constructs the original
`TraceRow`, pure Return, event transition, or shared source witness.

## Exact first missing equation and result

The first missing equation at the original generator owner is an independent
allocation/embedding of the actual original source literal problem into its
Value/Effect store, preserving all eight payloads and original ports. In
schematic notation (these functions have not been constructed), it must supply:

```text
AllocOriginal(q, synthesis, ξ).value/effect = the coordinates in GenOriginal(l,q,ξ)
GenOriginal(l,q,ξ) contains the literal's independent structural Value/Effect clauses
```

The existing source-rule atom preserves the raw literal but supplies neither
side of this allocation equation. The Rust source fragment supplies concrete
HIR/live coordinates for four literal forms, without a map from original raw
syntax, original semantic carriers or all eight forms. A single original raw
term `.literal ⟨q, none⟩ (.floatBits 0)` witnesses the *coverage gap of this
inspected Rust bridge*: there is no Float literal variant in its source
inventory or its producer branch. This is not an executable rejection test,
a source-qualified counterexample, a restriction of the original domain, or
evidence that L1 is false.

Even for Unit, the next equation is absent: interpreting every solution of
those original clauses must yield an assignment at the same source coordinate
with intrinsic descriptor `Value(τ(l))`, syntax-fixed value `v(l)`, original
root/event `r/e₀`, retained `ξ/ω`, and empty intrinsic effect. Rust graph APIs
give one completed solver state; they quantify over no independently supplied
assignment and define no map into abstract `Sorts.Descriptor`, `Sorts.Value`,
`Sorts.Root`, or `SourceAssignment`. `LiteralAtom` at
`OriginalSourceInterpretation.lean:845–850` would assume declaration and
groundness; it cannot establish this equation. R220's theorem remains a graph
lemma at supplied references and cannot supply either original allocation or
this interpretation by itself.

Therefore there is **NO_SAFE_CODE_SLICE** that this packet can derive from a
complete authorized source-to-original-model path. The exact authority owner
is the primary's original source generator/solution model lane. No Rust patch
or theorem activation follows. The established result here is the bounded
mechanical producer/admission/readback characterization; the parent and all
original constructors remain present and open.

## Authentication, commands and limitations

| Dependency | SHA-256 |
| --- | --- |
| candidate_source.rs | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| lib.rs | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| shadow_apply.rs | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| yu-hir/src/module/local_source.rs | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration.lean | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceInterpretation.lean | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| AbstractGeneratorDenotationR220.lean | `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254` |
| R214 note | `9c19d9422b47408a6ee944d04b04ddb22d58047684144dfc276bfa6e5d01c6e9` |
| R221 falsifier | `f06751e46d07cd50b43df3605c93d716d725f1483a233777f8099563d26ae444` |

Commands used: read-only `pwd`, `cat`, bounded `sed`, `rg -n`, `rg --files`,
`sha256sum`, tool clock; one patch creating this exact leased note. Initial
combined outputs were truncated; decisive code blocks were reread narrowly.
Two initially guessed HIR paths did not locate the enum; `rg --files` located
the actual owner and the complete enum and relevant formation branches were
then read. No negative conclusion relies on those failed path guesses.

Coverage is the three assigned Rust owners, their necessary HIR literal
formation and original Lean syntax/interpretation fields, with R214/R220/R221
as pinned existing evidence. No whole-repository absence theorem or exhaustive
consumer audit is claimed. Oracle independence: the code was inspected at its
actual producers/consumers rather than simulated using assumed transitions;
it still shares the repository authorities and has no independent semantic
oracle. There was no checker, mutation suite, seed or numerical search range.
The discriminator is constructor inventory and API types. Failure conditions
for this report include a changed dependency, a hidden admitted original
allocation/readout not in the inspected envelope, or a different source owner
providing the absent payload cases; primary revalidation is required before use.

No Rust edits, builds, Cargo, tests, Lean/Lake, scratch/cache outputs, network,
Git commands or children ran. Only short read/hash processes ran; CPU/RAM and
total active seconds were not instrumented. Work stayed within the assigned
900-second envelope; no process remains running. Unverified: full original
carrier, every-solution interpretation, annotated conversion, pure Return,
sameScoped and native/production correspondence. This output is not independent
review of itself or of the primary's model note.

Recommended next action: the primary should classify the exact original
allocation and descriptor/effect decoding equations as OPEN at the R231 model
gate, or provide their derivation-backed owner before fresh model review;
keep theorem activation closed while either equation is missing.

**WRITES_STOPPED:** this exact note is frozen for primary adjudication/review.

## Commit packet

- Exact leased paths: `tasks/agent-loop/inbox/original-literal-realization-r231-source.md` only.
- Baseline SHA: `c5cc9682aa2f4cb90a64d595202adc28ec570887` (primary-supplied).
- Changed dependency hashes: none observed; authenticated bytes listed above.
- Review status: research source audit awaiting fresh review; no self-certification.
- Checks already run: focused source reads/searches and dependency SHA-256 checks; no tests or builds.
- Proposed checkpoint message: `research: map R231 literal producer and original readout gap`.
- Shared-record deltas intentionally left to primary/curator: record MODEL-INCOMPLETE / NO_SAFE_CODE_SLICE, exact allocation/readout owner, inactive proof gate and parent delta 0; no semantic, theorem or production status change.
