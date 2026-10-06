# Frozen Oracle original producer: pattern-boundary follow-up

Date: 2026-10-08
Status: frozen research-only bounded historical characterization; independent review pending
Yulang3 baseline: `5809cd94c346c6095189e0e0664a13457dea4a68`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Authority: historical implementation evidence only; no semantic or implementation authority

## Objective, method and result

Find an untraced historical producer corresponding to the missing original
owner/view formation, without repeating ordinary application, formal/frame,
cast activation or explanation-query archaeology. Method: bounded static
constructor and identity tracing, followed by a local dataflow derivation.

**No additional mechanism satisfying ORIGINAL_ASSOC was found.** A distinct
adjacent seam is a case arm's Pattern boundary: it connects the scrutinee and
pattern endpoints, then records newly present upper-bound IDs under a
PatternInput occurrence. This refines the historical provenance crosswalk;
it does not construct an ordinary Call's original slot/contribution witness.
The fixed `call(result(name f),result(name x))` cut contains no case arm.

The prior [ordinary-call trace](2026-10-07-frozen-oracle-ordinary-call-source-producer-archaeology.md)
and [bounded novelty stop](2026-10-08-frozen-oracle-original-call-association-mechanism.md)
already cover App construction, name resolution, frame/formal subtraction,
source spans, call uppers, scheme use, occurrence roots and cast activation.
The [unannotated producer stop](2026-10-06-frozen-oracle-missing-source-producer-continuation.md),
[annotation declaration trace](2026-10-06-frozen-oracle-remaining-licensing-producer-archaeology.md)
and [boundary eligibility trace](2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md)
also prevent treating their solver/projection paths as new source production.
The annotation trace mentions shared pattern occurrence registration, but
does not trace the case arm's PatternInput before/after bound-ID collection.
Novelty here is limited to that local seam, not a new ordinary-Call producer.

## Governing premise and claim classes

The assigned frontier in [current task](../../tasks/current.md) is
`CALL_REL -> CALL_TYPE -> ORIGINAL_ASSOC -> ATTACH -> LIC_FORWARD/LIC_INVERT -> PROFILE -> ROWS -> independent admission`.
At one original `X/xi`, ORIGINAL_ASSOC needs an inhabited original fiber
`(beta,p0,j_call;s,c)` with exact original slot/contribution ownership,
independently typed complete receiver invocation, source arm, scope and
providers. It may not choose `c=j_call`, `s=p0` or a slot count by decree.

[FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1.1–2 and 5
retain source/public/internal separation, static source positions, joint
`xi=(nu,K,D)` and comparison-independent formation/admission. Its §§3–4 retain
the selected unannotated formal refinement and scoped annotation permission;
this pass assigns no historical meaning to either.
[Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2.1 takes independently typed primitive and owner/view-kernel contracts as
inputs; §3.5 transports those supplied contracts rather than introducing them.
Approved Option 2 remains in force.
[Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6 and 9
retains the source role/entry skeleton and complete invocation, including
argument entry, rebind, body and designated result consumer. A historical
four-port demand or a live type variable is not that whole interpretation.

Hypotheses for the local derivation:

1. H-bytes: the cited historical files and direct current dependencies equal
   their pinned commit blobs; checked byte-for-byte below.
2. H-arm: successful ordinary `lower_case_arm` lowering reaches its occurrence
   registration with valid pattern/body nodes. Rule-case dispatch, catch arms
   and early errors are outside this trace.
3. H-name: for the binder discriminator, the pattern is one ordinary bare
   identifier, not a constructor, boolean, rewritten `var` binding or compound
   pattern; its shared pattern lowerer succeeds.
4. H-read: bounds queried before/after the two subtype submissions are the
   actual snapshots at those points. The calls may drain solver work; no
   deferred-analysis or solver-completeness premise is supplied.

Established here: blob equality and the cited field assignments/call order.
Bounded characterization: the concrete producer below. Conditional local
derivation: the exact root selection and binder-tag distinction under these
hypotheses. H-arm/H-name/H-read describe trace premises, not established
accepted-source coverage. No current semantic theorem, source counterexample,
exhaustive inventory, absence theorem or independently reviewed result is
claimed. Equating a PatternInput root with `s`, `c` or `p0` would be an
unsupported candidate assumption.

## Constructors, input identities and stop

All Oracle paths below are relative to the frozen checkout.

1. `crates/infer/src/lowering/control.rs:300–327` receives the arm CST and
   `scrutinee_value/result_value/result_effect`; allocates `pattern_value`;
   lowers the pattern to `pat`; then snapshots that endpoint's upper bound
   record IDs as `B_before`. It does not receive a Call identity or Function
   frame. `lowering/expr/block_local.rs:703–716` supplies temporary name
   rewrites to the common match-pattern lowerer and restores them afterward.
2. The shared lowerer `lowering/pattern.rs:8–50` serves lambda and match
   patterns. Its PatternRequirement registration uses `Pattern(pat)`, empty
   structural path and the endpoint's **lower** bound IDs. For H-name,
   `:155–179,203–209,221–281` allocates a `DefId`, writes `Def::Arg`, adds
   `Pat::Var(def)`, and stores the same `value` in the local definition/binding.
   Initially `LocalDefRole::Value`, `call_predicate_frame=None` and
   `unannotated_call_frame=None` are explicit assignments.
3. Only after that lowering and `B_before` read,
   `control.rs:328–355` allocates a Pattern source boundary/origin pair and
   submits both `scrutinee_value <: pattern_value` and the reverse using
   that origin. The optional source span is stored under the boundary ID;
   it contains no `DefId`, frame or typed contribution
   (`lowering/source_boundary_provenance.rs:41–57,85–89`).
4. The boundary allocator is delegated by `arena.rs:79–80` to
   `constraints/machine/entry.rs:433–451`. The two records cross-reference
   origin and boundary IDs and initially record no location. Their identity
   is allocated from session record counts, not from a typed static slot.
   The endpoint comparison helper (`lowering/expr/constraints.rs:99–107`)
   allocates a negative Var and submits the supplied origin. Arena submission
   delegates to the machine (`arena.rs:90–93`); its entry can immediately
   drain work (`constraints/machine/entry.rs:493–499`).
5. `control.rs:356–376` reads upper bound IDs again, discards IDs already in
   `B_before`, wraps the remainder as `OccurrenceProvenanceRoot::Bound`, and
   registers them under `(Pattern(pat), PatternInput, empty path)`, with a
   fresh-source-parent option. The caller supplies `Complete`.
   `analysis/session/occurrence_provenance.rs:38–67` collects/deduplicates
   roots and changes that status to `Incomplete` when the supplied list is
   empty. This is a concrete occurrence-to-generated-bound association;
   the status label does not certify complete source invocation or licensing.
6. Defined lambda parameters use the same binder producer but separately
   mark the parameter as Input, attach annotation metadata and push a Defined
   FunctionPredicateFrame (`lowering/expr/lambda.rs:664–736,887–894`).
   Predicate-frame assignment requires nonempty predicate subtracts
   (`:938–943`); unannotated frame assignment requires Unannotated metadata
   (`lowering/expr/tail.rs:832–841`). Therefore `Def::Arg` alone does not
   establish function-formal, frame or receiver ownership. The case prefix
   through PatternInput registration has no such frame-marking call.

The dependency chain is therefore:

```text
arm CST + scrutinee endpoint
  -> pattern endpoint + PatId + shared local binder
  -> Pattern boundary/origin
  -> two endpoint constraints, possibly drained
  -> upper-bound IDs newly present since pattern lowering
  -> PatternInput occurrence roots
```

This route produces root provenance during source lowering. Its last step
reads solver state; it is neither a pre-analysis semantic contribution
constructor nor the later explanation-eligibility query. No claim is made
that each newly present ID corresponds only to one direct constraint rather
than work drained during those submissions.

## Local derivation and discriminator

Under H-arm/H-read, define `B_after` as the upper IDs read at step 5. Direct
substitution into its filter gives the root-ID set

```text
R = { Bound(r) | r in B_after and r not in B_before }.
```

If `R` is empty, registration downgrades the supplied Complete status to
Incomplete. This implication follows from the actual consumer, even with an
allocated boundary and available span. Reachability of `R=empty` for any
accepted source is unverified. Thus allocation/locations alone cannot serve
as a certificate that this route supplies nonempty complete source evidence.

For the binder discriminator, one H-name identifier is enough: the shared
producer returns `Pat::Var(d)` with `Def::Arg`, Value use metadata and absent
frame fields. A Defined-lambda caller adds Input and eligible frame metadata
after that return; the case prefix instead adds its boundary and PatternInput
roots. Dropping caller identity and retaining only `Def::Arg` conflates these
different introductions. This is a local constructor distinction, not two
executed/admitted source programs or a cardinal-minimal language witness.
The analytical mutation is to infer formal/frame ownership from `Def::Arg`;
the discriminator shows the missing caller premise. No mutation was applied.

## Correspondence, independence and next action

The strongest historical correspondence remains retention of live source
endpoint/definition/use identities, with caller-specific metadata, origins
and generated constraint roots. This adjacent pattern seam supplies no
ordinary App identity, original `beta/Slots(beta)`, typed `p0`, complete
contribution, owner/receiver judgment or joint original `xi`. A case source
arm and historical metadata role also cannot be identified with the current
whole-tuple semantic source arm or callable role by name.

The independently typed original owner/view-kernel introduction remains the
precise blocker. Existing transport/realization theorems assume that input.
Both the original ordinary-Call route and this adjacent route leave it
untouched, so another equivalent registry/ID probe would add no gate evidence.
Recommended next action: stop this archaeology lane until a genuinely distinct
producer is named, and derive the current independently typed original
slot/contribution introduction for the fixed ordinary Call.

Frozen source is independent of current stipulated-transition checkers, but
its producers, bounds and provenance consumers share one historical compiler's
assumptions. Blob equality establishes provenance only. Neither a checker
assuming these transitions nor two implementations of them proves their
current source meaning. No Oracle execution or successful query is used as
semantic authority.

Failure conditions: changed cited bytes; another dispatch path; pattern/body
errors before registration; constructor/rewrite patterns invalidating H-name;
missing source-span context; absence of newly present roots; or terminal
solver failure before the after-read. External effects during subtype/drain
can change which IDs are present, so no exclusive source-causation claim is
made. Full solver correctness, all pattern variants, source acceptance,
runtime behavior, imports/recursive use, exhaustive licensing, source adequacy,
production membership and repository-wide absence remain unverified.

## Checks, resources and frozen inputs

Commands: read-only revision reads; bounded `rg -n`, `sed -n`, `nl -ba` and
`cat`; Python SHA-256 plus byte comparison with `git show <pin>:<path>`;
artifact whitespace/link checks. One exploratory search named two nonexistent
session files and returned exit 2; subsequent locators used actual files.
Some combined context/search captures truncated and one exploratory search
used `head`; decisive windows were reread, and no completeness claim uses
those captures. The novelty search was limited to the named Frozen Oracle
notes; it did not exhaust all historical research notes.

One exclusive output path; no builds, tests, Oracle/checker execution, applied
mutation, formatters, Git mutations or children. Heavyweight process count:
zero. Initial context reads batched up to four lightweight shell processes;
source tracing and validation used sequential lightweight jobs. No numeric
assignment budget was supplied. CPU time, peak RSS and total wall time were
not instrumented. No seeds, ranges or runtime samples apply to this static
method. The producer freezes writes on submission and claims no independent
review.

All ten cited Oracle files equal pinned blobs byte-for-byte:

| Oracle path under `crates/infer/src/` | SHA-256 |
| --- | --- |
| `lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| `lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| `lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `lowering/source_boundary_provenance.rs` | `9d9f1694d4848be9daddea986b80be833f081d1e78a31ce1a0e540b740d74412` |
| `analysis/session/occurrence_provenance.rs` | `90613e12e904c74d40894e6f395162c358cc632a8aecb9ddc55db542dd897268` |
| `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |

The thirteen direct current dependencies equal the Yulang3 pinned blobs: the
three required rules, task/index, three governing designs and five linked
predecessor notes. Decisive semantic and predecessor hashes:

| Current dependency | SHA-256 |
| --- | --- |
| FVIEW | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Source contracts | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Ordinary-call trace | `acd3769b77ceb64b8bb0830bdaaf4a9365d416d85eda097c366ed787db957c6b` |
| Bounded novelty stop | `2697c8e2db5d67be0cfdc1bfdb5b4cdea9f5ae9ee456afc55b6402a2979419ba` |
| Unannotated producer stop | `7b31b95460725948b32f41a3f792c6efc125ade48d83389122f5f3145d36d552` |
| Annotation declaration trace | `03adcceed74bb8a08290e748989fd0af1e8eb417a19a7a7ba6303c29191d70d7` |
| Boundary eligibility trace | `bfb7ed9b54fca51d64ae934df7c501b0322384f116e92c4f2144413e2572b223` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-frozen-oracle-original-producer-mechanism-followup.md`.
- Baseline SHA: `5809cd94c346c6095189e0e0664a13457dea4a68`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; ten Oracle and thirteen direct current
  dependencies matched pinned blobs. Freeze checks recheck these inputs.
- Review status: frozen research-only bounded characterization and conditional
  local derivation; independent review pending; no gate closure.
- Checks already run: revision identity, scoped novelty/constructor reads,
  pinned-blob equality and SHA-256, local Markdown target existence and
  trailing-whitespace checks. No tests/builds/Oracle execution.
- Proposed one-line research-checkpoint message:
  `research: bound Oracle pattern-boundary producer correspondence`.
- Shared-record deltas intentionally left for primary/curator: optionally
  append the PatternInput bound-ID association and caller-dependent Def::Arg
  distinction to the historical crosswalk; record no additional ordinary-Call
  original producer and retain ORIGINAL_ASSOC/all dependent gates as open.
  No task/index/authority/theory/question-board record was edited.
