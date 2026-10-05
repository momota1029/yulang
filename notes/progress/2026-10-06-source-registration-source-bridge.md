# Source registration: source/HIR/solver correspondence

Date: 2026-10-06
Status: Frozen research-only correspondence audit; independently reviewed with no findings in its bounded documentary scope; no implementation authority
Baseline: `621d24b77453799e01ce46615ccabf5b30af183b`
Exclusive lease: this file only
Method: bounded source-to-artifact trace; no executable experiment
Implementation authority: none

## Objective and bounded result

Trace the approved `apply f x = f x` skeleton through source rules, current
production HIR and solver collection. Identify the usable source identity
bridge and the earliest missing premise for forming its shared callback view.

**Result class: bounded characterization and conditional derivation.** Current
HIR supplies artifact-scoped definition, parameter and expression identities;
current collection relates admitted definition-name occurrences to dependency
SCCs. These are positive identity/graph bridges. They do not supply typed
callback registration. For the approved two-parameter skeleton, production
header lowering rejects the shape before either formal or the body call reaches
resolved HIR. Even granting expanded structural lowering, the inspected rules
still require a comparison-independent judgment relating those source identities
to one role-indexed interface, slot/profile, typed incidences and joint `nu,K,D`.
No language rejection rule, source counterexample, impossibility theorem,
complete-view theorem or production conformance is inferred.

This extends the [preceding premise inversion](2026-10-06-call-view-source-rule-derivation-attempt.md)
with concrete identity and collector correspondence. It does not rerun the
seed-eligibility or use-aggregation attacks, and selects no discharge rule.

## Governing scope and retained decisions

- [Authoritative inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–3: written annotations, inferred public schemes and internal views are
  distinct; the relevant source component forms a shared contract; source
  position, annotation presence and scope survive transport; typed paths and
  owner/receiver relations require source resolution and typed elaboration;
  admission is independent of pending comparison `Q`. The approved `apply`
  formal receives a fully protected provisional Handler view and is determined
  non-Handler from ordinary-value evidence on that shared inferred interface.
  This preserves actual supplied callable roles and entries.
- [Callback context delivery](../design/2026-10-03-callback-context-delivery.md)
  §§1–2.1,3–4,6: literal B remains normative; it starts from an already
  instantiated callback contract. Static slot identity differs from dynamic
  receiver activation. Existing Pure values retain actual role and entry.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.2,3.1–3.4,10: **reviewed conditional package, concrete clauses Draft**.
  The decorated graph supplies actual roles, typed paths, receipts and shared
  coordinates; active membership/admission and transport are hypotheses.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6: structural synthesis relative to lexical/declaration interfaces and
  existing complete invocation obligations; no raw recursive inference claim.
- Integrated [approved formation answer a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md),
  items 1–6, and [receipt](../../questions/2026-10-05-function-call-view-formation/receipt.md)
  at `61a3651376166346a5baa03ec6679c310b0edbdb`.

The annotation's `[io]` permission remains scoped permission rather than
performed subtraction. Absence of annotation is protection input rather than
an empty-row assertion. Option A and production membership Option 2 stay fixed.
No pending question draft was consumed. Live task/index changes were locator
context only, not proof premises.

## Explicit hypotheses and one source trace

Use repository declaration spelling `my apply f x = f x` solely to trace the
approved skeleton. This prefix does not select new grammar or semantics.

H1: the parser supplies the same recovery-free header/body structure as the
existing `my call f x = f x` fixture after ordinary identifier renaming of
`call` to `apply`. No parsing command was run here: the renamed concrete case
is conditional on H1. The retained fixture and test-only mapper are inspected
at [HIR source](../../crates/yu-hir/src/lib.rs), lines 1362–1408 and 1970–2019.
The mapper's bounded preconditions require distinct plain binders and bound
names; it is inside `cfg(test)` beginning at line 691.

H2: when using typed-core §6, lexical resolution supplies `b_f,b_x` in the same
scope, and the callable/whole-argument invocation obligations remain unsolved
constraints rather than assumed successes.

Under H1, source locations identify the header occurrences `f` at `9..10`
and `x` at `11..12`, plus body name occurrences `f` at `15..16` and `x` at
`17..18` for this exact spelling. The existing candidate mapper would associate
its body as one ML application and resolve the scoped shape `lambda0.lambda1.(v0 v1)`.
These are static source coordinates and candidate lexical indices, not typed
paths, receiver identities or public type syntax. No run of the renamed case
or assertion of its acceptance is claimed.

Production follows a different trace:

1. [plain_binding_header](../../crates/yu-hir/src/module.rs), lines 1471–1516,
   accepts only a plain identifier, optionally followed by exactly one
   plain ML parameter. H1's two parameters therefore fail that match.
2. `plan_root`, lines 1052–1066, records
   `Unsupported(UnsupportedTarget)`. Such plans enter neither `namespace`
   (lines 1088–1110) nor the definition-root allocation arm (lines 819–824).
3. `lower_plan`, lines 1127–1148, emits `HirItem::Error`; there is no admitted
   `HirBinding`, `HirParameterId` for either formal, or resolved call/name
   occurrences for this definition. A root occurrence may be allocated during
   lowering, but `HirItem::Error` does not expose it as a callable.
4. [ConstraintBatch::collect](../../crates/yu-solver/src/lib.rs), line 1001,
   skips that error item. This definition contributes no definition-use/SCC
   record, lambda recipe or callable constraints.

This is a conditional derivation from the actual match arms, not an executable
counterexample to the selected language meaning. A changed header structure or
lowering implementation invalidates this production trace.

Granting only multi-parameter header support would not finish the bridge.
`ResolvedExpr` has only Lambda/Integer/Name/Error (module.rs lines 426–449).
`lower_simple_chain`, lines 1419–1423, accepts only an associated leaf Value;
non-leaf application structure becomes `UnsupportedExpression` through
`lower_body`, lines 1374–1387. The collector also marks nested Lambda bodies
incomplete (solver lib.rs lines 939–962), and `emit_lambda` only handles leaf
body cases (lines 1564–1596). These are successive structural seams, not
proposals to bypass errors or authority to edit them.

Under H2, independently of these production limits, typed-core §6 gives
`Gamma(f)=Value(A_f)`, `Gamma(x)=Value(A_x)` and hence
`I_x=Value(A_x)`, `Result(I_x)=Comp(empty,A_x)`. Its application row gives
`Computation(E_c,A_c)` with inert `reify(call(n_f,n_x))`, retaining the whole
argument and complete invocation obligations. This proves available static
Value evidence under the core hypotheses. It does not establish the callable
`f`'s actual entry or solve its provisional-role discharge. Runtime receipt,
Force and receiver activation are not needed to identify this source tag.

## Positive correspondence and exact limits

| Required object | Existing positive bridge | Missing correspondence / owning responsibility |
| --- | --- | --- |
| Source binding identity | `DefId` carries module, spelling and same-name ordinal; `DefinitionRootId` adds immutable-HIR brand; `HirParameterId` adds owner root and parameter ordinal. `NameResolution::Parameter` retains that ID for admitted leaf uses. | The exact `apply` form is not admitted. Relating each formal and all its uses to one internal role-indexed contract is a source/typed-elaboration rule, not a property of the ID. |
| Occurrences and recursive component | `HirOccurrenceId` has artifact brand plus lowering ordinal. Collected resolved definition-name leaves retain `DefinitionUse(parent,target,occurrence)`; `SccPlan` retains members/internal/incoming uses. | Body calls and captures are not represented by this production traversal. A definition dependency graph is not the callback occurrence/profile inventory of every relevant source use. |
| Annotation occurrences and profiles | CST distinguishes `PatternTypeAnnotation`; expression association retains `TypeAnnotationTail` as a structural barrier. Source ranges can identify those syntactic nodes. | Admitted `HirParameter` has ID/name/range only; plain-header matching does not elaborate annotated formals. No inspected rule maps an annotation occurrence and its permitted contribution to `Slots(beta)`. Source annotation elaboration owns this relation. |
| Typed paths, owner/receiver | Parameter ID retains lexical owner root; name resolution establishes binder links within admitted leaf scope. | Lexical ownership is not typed provider ownership, receipt or receiver incidence. Typed call/capture/receipt elaboration must generate and justify these; dynamic activation remains a runtime object. |
| One joint `nu,K,D` | Solver keeps one batch, component/root maps and source occurrence causes; ordinary Function terms share terms in an arena. | The inspected constructor/collector path has no source-generated joint registration for `nu,K,D` with profiles/incidences. Shared allocation or four ports alone does not supply a joint assignment or its transport theorem. |

Direct references: [HIR identities and nodes](../../crates/yu-hir/src/module.rs),
lines 114–120,170–215,254–324,361–449,545–553; leaf resolution at 1443–1463.
Structural HIR equality intentionally omits artifact identity (lines 471–474);
`NameResolution` structural equality compares parameter ordinals (lines 404–415).
Use the actual branded IDs for identity arguments, not structural equality of
whole HIR trees. Fresh lowering mints a new token (line 813); no cross-edit
identity theorem is claimed.

[SCC bridge](../../crates/yu-solver/src/lib.rs), lines 591–605,
1008–1075,1088–1145,1309–1376, and [SCC plan](../../crates/yu-solver/src/scc.rs),
lines 77–90,212–250. The collector queues definition references only at the
root leaf or immediate lambda-body leaf in the inspected traversal. The SCC
plan consumes those supplied edges; its graph computation cannot recover
source calls discarded earlier.

[Function term view](../../crates/yu-solver/src/term.rs), lines 170–214,
contains four term ports. [admit_lambda_fact](../../crates/yu-solver/src/lib.rs),
lines 10539–10566, constructs an ordinary Function with the negative parameter
endpoint, empty argument effect, positive body effect and result endpoint.
For the admitted identity-body case it reuses the parameter variable as result.
That is a positive endpoint-sharing bridge for its leaf-lambda fragment. It
constructs neither the approved provisional Handler view for inferred formal
`f` nor a callback slot/profile. This audit does not identify the stored
Function ports with written annotation syntax or assert that the entire solver
has no additional state elsewhere.

## Reduced premise and failure conditions

The earliest semantic premise is a judgment with the following obligation,
independent of `Q`:

```text
resolved component + binder b_f + all relevant use occurrences
+ source annotation-presence/occurrence information
  => one original formal interface and provisional view
     with beta, Slots(beta), typed incidences, joint xi=(nu,K,D)
```

This is an interface obligation, not selected inference syntax, a carrier or
an implemented transition rule. Source resolution/HIR must retain the static
inputs; typed elaboration must prove the formation relation and preservation.
The solver may consume the generated joint constraints after those rules are
specified. The separate ordinary-value discharge premise consumes the
registered interface together with `I_x=Value(A_x)` and remains open.

The missing premise is smaller than a blanket request for a new resolver:
the existing IDs and SCC grouping can supply portions of its inputs within
the admitted fragment. It is larger than adding Apply or a profile field:
those structural changes alone prove neither registration nor its semantics.

A completion fails this gate if it equates expression ordinal with static
slot/profile, equates SCC edge with typed Flow, equates lexical owner with
receiver/receipt, equates an opaque fiber number with joint `nu,K,D`, derives
annotations from inferred type shape, creates incidence from `Q` success, or
mistakes retained occurrence metadata for active admission/membership clauses.
The source-contract package explicitly assumes decorated source inputs in
§3.1 and active clauses in §2.2; using its realization theorem to construct
those same hypotheses would be circular.

## Evidence, coverage, resources and freeze

No checker/oracle, seed/range enumeration, mutation test, build or compiler test
was run. Existing candidate tests were read as code, not rerun or independently
certified. Their fixture supplies structural syntax while their candidate
supplies lexical indices and §6 transitions; they do not independently validate
formation semantics. A future checker assuming registration/discharge
transitions would establish consequences of those transitions only.

Authority documents and production source are independent inputs to this
correspondence audit, but the conditional core trace shares H2 with the earlier
note. This is no independent review of that note or of this output. Two
previous premise-oriented attempts did not construct registration; this lane
changes method to concrete source/artifact correspondence and returns the
precise owning-layer premise instead of another toy probe.

Commands: sequential lightweight `cat`/`sed`/`nl`/bounded `rg` reads;
read-only `git rev-parse`, `git status` and exact-dependency
`git diff --exit-code BASELINE -- PATHS`; Python SHA-256 capture and leased
note creation; final dependency/lease check. Eleven top-level command
invocations total; the dependency checker invokes one additional read-only
Git process sequentially. No concurrent local commands, heavyweight process,
Git mutation, formatter, compiler/test edit, child or interactive question.
Initial oversized task/locator captures were truncated; all cited code and
governing sections were subsequently read narrowly. This is not a complete
repository absence search. CPU time, peak RSS and elapsed wall time were not
measured; no numeric resource claim is made beyond process/invocation counts.

Unverified: the renamed source's parse result; exact annotated example parse;
general pattern/capture/import resolution; recursive call occurrence coverage;
source registration/role discharge; full annotation-to-profile mapping;
generalization/use preservation of complete views; active production admission,
including Option 2 extras; source adequacy, uniqueness/principality and runtime
execution. No production patch or new source support boundary is proposed.

Recommended next action: have the primary specify and independently review
one Q-independent registration judgment for the approved `apply` component,
using explicit binder/use/annotation inputs and joint outputs; retain this
production trace as its conformance checklist before authorizing implementation.

## Frozen direct dependencies

All listed live bytes matched the pinned baseline in an exact-path read-only
Git diff (exit 0); final hashes were rechecked before handoff. Shared task,
index, theory and hygiene edits observed in status were excluded and untouched.
Compared with the preceding note's historical freeze, inferred-call-views
changed from `2b04b178b08e8f4fbb74988c528eb1c324d89242c9e060e52cbbe2f14c8fd2f8`
to the hash below, incorporating authoritative §1.1. Its new source/annotation
separation is used here. No direct dependency changed during this audit.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-call-view-source-rule-derivation-attempt.md` | `0009795b060e3bac47d17437f7350f0e45f0bc1eee4131706e04bd4d44624c4d` |
| `crates/yu-hir/src/lib.rs` | `56aafd7d958acdfa3362ffcc7bf3e815d795f455597cf4f8e471194addb04c1b` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `crates/yu-solver/src/term.rs` | `12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611` |
| `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03` |
| `crates/yu-syntax/src/syntax_kind.rs` | `f3c7632b8e5c975ed917de56355030d90106b8710fe6cd89020e8394a73a09c0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-registration-source-bridge.md`.
- Baseline SHA: `621d24b77453799e01ce46615ccabf5b30af183b`.
- Dependency hashes changed during audit: none; frozen hashes above. Historical
  inferred-call-views change from the preceding note is explicitly recorded.
- Review status: frozen unreviewed research-only characterization/conditional
  derivation; no independent review, gate closure or implementation authority.
- Checks already run: exact baseline dependency diff exit 0; narrow source/HIR/
  collector/term/SCC audit; final hash/lease-content check. No tests/builds/probes.
- Proposed checkpoint message: `research: trace source registration through HIR and solver`.
- Shared-record deltas left for primary/curator: record the existing branded-ID
  and leaf-definition/SCC bridge; separate structural admission/Apply/nested-body
  seams from typed registration, annotation/profile and joint-coordinate rules.
  Link this note without closing source formation or production conformance.
  No task/index/theory/authority/question-board edit was made by this worker.
