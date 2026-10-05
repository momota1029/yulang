# Generalization/member-use source-origin correspondence map

Date: 2026-10-06
Baseline: `bd441cc922e5bd244990f7c687fe42a245e04176`
Status: bounded static characterization and conditional representation lemma;
unreviewed research-only checkpoint, frozen on submission
Lease: this file only; no production, test, build, probe or Git authority

## Objective, authority and result

Locate actual producers of recursive member generalization, scheme creation,
use instantiation and origin metadata. Distinguish selected successor source
judgments, current Yulang3 production and frozen Oracle/F5 mechanisms. The
expected falsifier was an existing selected derivation that already supplies
the source origin and scope map missing from the two assigned prior notes.

No such full derivation was found in the inspected sources. Current production
does implement a source-identified F5 producer/consumer pipeline; its allocation
origin is `Collected | Fresh`, not a source introduction classification.
Frozen Oracle has a more substantial generalized-witness-to-use pipeline, but
its own producer explicitly marks whole-scheme and recursive-bound witness
coverage **Incomplete**. That is concrete retained evidence against treating
its provenance API as the missing complete source-origin certificate. Neither
finding decides successor classification of Q, R or fresh scheme instances.

Governing sections and accepted decisions:

- Redesign charter §§1–2: replace F5 generalization/scheme architecture; the
  Oracle target is final well-typed-program acceptance capability. F5 Q/R
  shape/equivalence is historical comparison, not successor authority.
- Charter §20: operation universal instantiation, packet witness retention
  and request opening are distinct events; dependent fields remain jointly
  scoped. Hidden request binders differ from solvable inference existentials.
- Charter §§22–23: source-introduced existentials trigger the repeated guard;
  levels belong to variables. Full origin/comparison/extrusion coverage remains
  open; fresh allocation does not itself select the introduction judgment.
- Authoritative result-synthesis §4: `Gamma(x)=I` supplies `Synth(name x)=I`;
  lambda synthesis preserves the supplied body's source interface. This rule
  consumes an environment and supplies no recursive generalization rule.
- Authoritative call-view §§1–2,5 and committed q1/a2: generalization/use must
  preserve static slot identity, annotation presence, lexical scope, typed
  paths, owner/receiver relations and original joint `nu,K,D`; exact creation
  and preservation judgments remain proof gates. Receipt commit:
  `61a3651376166346a5baa03ec6679c310b0edbdb`.

The prior generalized-alias bridge and universal-use origin audit remain
prerequisites with their own conditional claims. This audit supplies code
owners and an explicit historical coverage limit; it does not repeat their
alias algebra or identity specialization discriminator. Repository policy
authorizes the method/lease only and supplies no language premise.

## Current Yulang3 producer map

Paths and line locators refer to the pinned baseline. Static inspection proves
the listed declarations and branches exist; these paths were not executed.

| Responsibility | Actual owner and inspected locus | Supplied correspondence and boundary |
|---|---|---|
| Source identity, lexical parameter/name resolution | `crates/yu-hir/src/module.rs:426` `ResolvedExpr`; `:545–571` `HirBinding`/`EvaluationClass` | Lambda, Integer, Name, Error carry artifact occurrence/range and parameter/definition identities. Private `FetchValue` classification covers admitted forms. There is no production Apply/request node in this enum. |
| Name/lambda constraint generation | `crates/yu-solver/src/lib.rs:1513–1618` `emit_resolved_binding_name`/`emit_lambda` | Exact occurrence value/effect components, alias occurrence-to-root fact, lexical parameter recipe and Function-to-root recipe. This is the current pure fragment; these facts do not construct successor origin-bearing interfaces. |
| Definition-use recipe | `lib.rs:570–605,1095–1137` `DefinitionUseCause`/`DefinitionUse` | Exact parent, target, occurrence, artifact-owned use ID, component positions and frozen `use_level=1`. The cause is explicitly provenance rather than a type fact/component. |
| Live allocation and eligibility metadata | `lib.rs:749–759,9480–9530,9550–9604` | Startup rows are `Collected`; incoming rows are `Fresh`, with separate level and `non_generic`. `fresh_value_at_level` has no input specifying source introduction kind. |
| Recursive member drafting | `lib.rs:13088–13105,15162–15185`; `f5c_generalization.rs:10676–10720,10900–11027,11547–11557` | A member's definition-root recipe selects a live row. `F5cGeneralizer` expands bounds, retains recursive owners, chooses disjoint Q/R ordinals and uses level/non-generic eligibility. R ownership is a graph/binder result, not a proved §22 origin. |
| Scheme finalization/publication | `lib.rs:13260–13328,13881–13969,15187–15350`; `crates/yu-types/src/lib.rs:630–649` | Production takes `boxed_component!()` under `cfg(not(test))`. All member candidates precede installs; incoming uses follow the install loop. `ClosedValueScheme` stores arena, counts, bounds and predicate. The indexed flat alternative seen here is test gated. The older helper named `generalize` at `lib.rs:15353` is also test gated and is not the production Function producer. |
| Internal recursive use | `lib.rs:13985–14007` `route_internal_inner` | Connects current target live root below exact occurrence row without Q/R freshening. |
| Incoming use and recursive-bound restoration | `lib.rs:14527–14660,14881–14963,15011–15085` | Reads the target's installed scheme, uses one fresh substitution map, allocates Q and R through the same allocator at the use level, restores R lower/upper bounds, and admits the predicate below the occurrence value. |
| Durable route provenance | `lib.rs:3925–3941,15011–15085` | Exact `use_id`, optional public fact and route kind remain. Restoration comparisons use the occurrence/cause. These fields identify a route; they do not attest its source binder/introduction interpretation. |

Historical F5 §§5,7–9,12,23 explicitly specify this live/closed split, source
causes, Q/R preservation and freshening. Section 7 deliberately excludes
live/source identities from the closed scheme. A separate proof or sidecar
could still relate such an erased representation to source; absence of source
fields does **not** prove correspondence impossible. The missing result is
that relation and its preservation, rather than a requirement to add fields.

Current source test `lib.rs:20476–20548`, inspected but not run, asserts the
F5 recursive shape for `my f x = g; my g y = f` under boxed and test-flat
paths. This is a legacy implementation contract, not the selected successor
source-origin theorem. Existing test assertions do not independently certify
the code that generates their result.

## Frozen Oracle producer and partial provenance map

All paths in this section are read with `git show` at
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; none is a live successor owner.

| Responsibility | Frozen owner/locus | Observed limit |
|---|---|---|
| Component generalization and publication | `crates/infer/src/analysis/session/instantiate.rs:14–103` `quantify_component` | Generalizes each root, records role prerequisites, stores component schemes, captures witnesses, finalizes with ancestor simplifications, records generalized provenance and writes final definition scheme. |
| Generalization policy | `analysis/session/generalize.rs:32,506–571,767–779`; `generalize/mod.rs:48–148` | Binding fetch chooses the boundary; alias/stack cleanup and compact simplification feed quantifiers, recursive structure, roles and substitution/sandwich records. These are historical procedures, not successor judgments. |
| Final interface creation | `generalize/finalize.rs:3–27`; `crates/poly/src/types.rs:17–33` | Creates a `Scheme` with quantifiers, role predicates, recursive bounds, stack quantifiers and positive predicate. Recursive bounds are a side table restored on use. |
| Generalized source witnesses | `generalize/provenance.rs:23–82` `capture_generalized_witnesses` | Follows selected canonical structural paths, marks failed survival/sandwiches incomplete, emits RecursiveLowerBound/RecursiveUpperBound witnesses with no incoming parents and **Incomplete**, and unconditionally reports whole-scheme completeness **Incomplete**. Limits are 128 witnesses, 256 incoming edges and depth 16. These are storage/coverage limits in this historical capture, not language limits adopted here. |
| Generalized witness to use | `analysis/session/instantiate.rs:343–524` `prepare_instantiated_use` | Retrieves generalized witness IDs/paths/completeness, instantiates with provenance, interns source/parent/target/use correspondence, and routes available projected derivations. Imported/finalized templates use a separate path with default provenance. Its local completeness calculation over projected function-argument witnesses does not override producer whole-scheme incompleteness. |
| Instantiation mapping and allocation | `instantiate.rs:158–186,620–651,732–739` | Maps generalized witness/path to positive/negative/neutral target positions, separates shipped argument mappings from inert structural mappings, freshens quantifiers and recursive variables through one source-to-target map, and allocates at the provided level. |
| Name use and effect occurrence | `lowering/name_ref.rs:146–186` | Stores source span, parent, reference and instantiated local value; uses local effect/effect view. These records are usable historical locators; their presence supplies no successor existential-opening theorem. |

This is a stronger historical bridge than a bare freshness map: exact partial
source-derived witnesses can travel to a use. Its explicit incomplete recursive
records are the smallest inspected **artifact witness** of the unresolved
whole-scheme provenance claim: one `RecursiveLowerBound` record has
`incoming=[]` and `completeness=Incomplete` (`provenance.rs:48–57`), with the
dual record immediately following. Removing the record loses the concrete
recursive case. This is not a source-language counterexample, an assertion that
every unrelated Oracle proof is incomplete, or a globally minimal witness.

## Other derivations checked against the expected falsifier

`notes/design/2026-10-04-source-indexed-callback-realization.md` §§1–2,3.2–3.3
retains original scopes, dependent roots, rigid quantifier positions and
future interactions. Its input is an already decorated finite graph with
**monomorphic recursive references** and independently supplied valid local
relations/paths. It constructs a reference endpoint interpretation; production
conformance remains open. It does not construct polymorphic recursive-member
generalization or allocate ordinary scheme-use coordinates from raw source.

`notes/progress/2026-10-05-inference-lifecycle-interface-conditional.md` §§1–3
requires complete generalized interface factorization, scope-preserving
equality and valid fresh-use transport as hypotheses. Its boundary-substitution
theorem therefore does not prove the origin transport premise sought here.
These reviewed results are genuine within their envelopes; the exact omitted
bridge is not supplied by their scope-preservation wording.

## Conditional representation lemma and residual premise

Let `M(v)=(origin(v),level(v),non_generic(v))` be exactly the current live
allocation metadata. Consider a Q allocation and an R allocation at the same
use level, both through the inspected `fresh_value_at_level` branch. Hypotheses:

1. Both allocations succeed and no later update is included in the observation.
2. A proposed origin classifier is a function of `M(v)` alone.

Then `M(v_Q)=M(v_R)=(Fresh,l,false)`, hence that classifier gives the same
answer for Q and R. Proof: direct substitution of the allocator writes followed
by function congruence. Dense variable IDs may differ; they are excluded by
hypothesis 2. Distinguishing Q/R via the scheme table, source ledger or another
proof falls outside this restricted classifier and can be investigated.

This establishes only insufficiency of a metadata-only discriminator whenever
a proposed derivation needs different source-origin classifications. It chooses
neither classification and does not assert a source needing different answers.
Replacing `Fresh` with `Intro22` would insert the unproved source premise.

The precise residual gate is a source-derived recursive formation,
generalization and member-use judgment whose certificate relates every relevant
source introduction/scope/constraint to the representation and exact use. It
must specify what each newly allocated coordinate represents, preserve outer
sharing and original dependent fields, and account for derived comparisons.
The known Name rule then consumes the resulting environment; it cannot supply
that certificate. F5 scheduling/identity maps, the historical partial witnesses,
and conditional scope theorems leave this premise untouched. No additional toy
probe is proposed.

## Independence, coverage, resources and failure conditions

No executable oracle/checker was used. Selected source clauses independently
constrain the implementation target, but current code/tests and historical
code/provenance share their respective implementation and language assumptions.
They are not independent mathematical reviews or source-adequacy oracles.
A checker supplied the missing transition rules would test consequences of
those assumptions, not prove them. The representation lemma has only the two
explicit hypotheses above.

Static coverage consists of the governing sections, listed code passages,
two prior notes and two scoped derivation comparisons. Initial broad locator
output was sometimes truncated; only subsequent explicit passages support the
claims. The repository has no live `spec/` directory; no exhaustive search of
historical specs, all annotations, request generation, imported evidence,
generalized diagnostics or alternate provenance consumers was completed.
There are no seeds/ranges, generated cases, mutation executions, performance
samples, tests or builds. Source acceptance of the alias example, full guard
coverage, source soundness/principality, effect generalization and production
Option 2 conformance remain unverified.

Commands: `git rev-parse HEAD`, `git status --short`, bounded `rg`, `sed`,
`cat`, `git ls-tree`, `git grep`, `git show`, and read-only Python SHA-256/
baseline byte comparisons. All 19 direct live dependencies equaled the pinned
revision at fingerprinting; the lease path was absent. At most two lightweight
shell calls ran concurrently, with no heavyweight process, no children and one
output note. CPU time, peak memory and elapsed wall time were not instrumented;
no numerical wall-time/CPU/RAM budget was supplied. No Git mutation or shared
record write occurred.

Failure/delta-review conditions: a governing dependency changes; an established
in-scope selected derivation constructs the missing full source map; another
Oracle path proves complete recursive origin transport; the production branch
configuration differs from the inspected `cfg(not(test))` route; or partial
witness completeness is promoted to whole-scheme scope. The latter two would
invalidate specific characterization claims, not select successor semantics.

Recommended next action: construct one source-derived recursive
`Form/Generalize/MemberUse` certificate, using the current producer seams and
the Oracle recursive incomplete-witness locus as concrete coverage targets;
independently review its origin/scope map before assuming a §22 classification.

## Dependency fingerprints

SHA-256 of direct dependencies at the baseline, checked equal to live bytes:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
f6e81f2036f038d6bc3aacfac505afc32ff671a99815dbf94ba9f918fc1eee3c  tasks/current.md
d8794543008221be430c3b676929b8601fb4534799fc67856e99ad140da0975d  tasks/research-lab.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536  questions/2026-10-05-function-call-view-formation/approved-answer.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0  questions/2026-10-05-function-call-view-formation/receipt.md
d9911dc127a684c9a2a471d02e2513958de428cd1de5589d88bc3fb9ac85fc53  notes/progress/2026-10-06-rec-name-return-generalized-alias-source-bridge.md
8963987e193efe9c4778a457a163df0076391b4056734def0087164b4795e300  notes/progress/2026-10-06-universal-scheme-use-origin-audit.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671  notes/design/2026-10-04-source-indexed-callback-realization.md
2683d7460de7137f747b63aa771c5873c795a6f9fad300f61328d58c98fe781f  notes/progress/2026-10-05-inference-lifecycle-interface-conditional.md
ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5  crates/yu-hir/src/module.rs
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
3d3aed964081996034fbb22a757c36a5da2c46c64b7f74ae51e86c14ee5bd5cd  crates/yu-solver/src/f5c_generalization.rs
a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5  crates/yu-types/src/lib.rs
```

Frozen Oracle SHA-256 at `a58eefc31e22141574b6f20c6a5748151c6d79f1`:

```text
ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a  crates/infer/src/analysis/session/generalize.rs
bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19  crates/infer/src/analysis/session/instantiate.rs
03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef  crates/infer/src/generalize/mod.rs
a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492  crates/infer/src/generalize/finalize.rs
83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0  crates/infer/src/generalize/provenance.rs
876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c  crates/infer/src/instantiate.rs
699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede  crates/infer/src/lowering/name_ref.rs
9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c  crates/poly/src/types.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-generalize-memberuse-source-origin-map.md`.
- Baseline SHA: `bd441cc922e5bd244990f7c687fe42a245e04176`.
- Changed dependency hashes: none at producer fingerprint recheck; hashes above.
- Claim/review: bounded static characterization and conditional representation
  lemma; frozen unreviewed research-only artifact, independent review pending;
  no source theorem closure or production authority.
- Checks already run: static source/branch/provenance inspection, direct
  baseline byte/hash equality and lease-path integrity; no executable checks.
- Proposed one-line research-checkpoint commit message:
  `research: map generalization producers and incomplete origin transport`.
- Shared-record deltas intentionally left for primary/curator: link current
  producer seams; record frozen Oracle's explicit incomplete whole-scheme and
  recursive-bound witness capture as partial historical evidence; retain the
  missing source-derived Form/Generalize/MemberUse origin/scope gate. Do not
  promote F5 freshness, local projected completeness or reviewed conditional
  lifecycle transport to established successor provenance.

Writes stop before submission for frozen review.
