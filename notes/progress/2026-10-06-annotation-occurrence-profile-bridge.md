# Annotation occurrence to original effect profile: source audit

Date: 2026-10-06
Status: reviewed research checkpoint; bounded source correspondence and conditional obligation
Reviewed-by: `spec_auditor` (bounded source-conformance review; no findings)
Baseline: `ea7146a5a5ef6edffe56fe258576ec4f15bbc862`
Lease: this file only
Method: one bounded textual pass through authority, typed declarations and CST/HIR
Implementation authority: none

## Objective and result class

Determine whether the pinned sources already derive an exact relation from
the annotation occurrence in `apply(f: _ -> [io] _, x) = f x` to the original
typed effect-profile position whose protection permission it affects.

**Bounded audit result:** they preserve the distinctions this relation needs,
but do not construct the relation. The strongest source-established bridge
is syntactic occurrence containment followed by a supplied admitted annotation
derivation. The next step, from that derivation to an original effect position
in the completed role-indexed Function profile, is explicitly open. This is
an identified missing premise within the inspected source chain, not a proof
that no other repository document could supply a rule.

Accepted decisions are retained without reinterpretation: absence of annotation
causes full protection; the specified `[io]` annotation permits only its `io`
removal; permission does not enact removal. The approved direction retains
original position/scope and one shared `(nu,K,D)`. No claim identifies `[io]`
with `'e?`, concrete capture admission, an event attribution rule, or a row
subtraction action.

## Exact source chain

Locators are at the baseline. The assignment's shorthand
`2026-10-02-typed-computation-core.md` is absent; the index and approved answer
identify `2026-10-02-typed-computation-core-elaboration.md` as the intended file.

| Link | Source locator | Established fact / limit |
| --- | --- | --- |
| Selected direction | `notes/design/2026-10-05-inferred-function-call-views.md` §§2,4,5; `questions/2026-10-05-function-call-view-formation/approved-answer.md`, decisions 3–5 | Source position, annotation presence and scope survive formation/use; original joint assignment is retained. §4 explicitly leaves the annotation-to-contribution rule open, and §5.3 requires its construction. |
| Actual source boundary | `questions/2026-10-05-source-annotation-boundaries/approved-answer.md`, decisions 1–4 | Compare the current endpoint directly to the target at the actual binding/argument/`as` boundary; export target plus local realization evidence and retain predecessor evidence. Query success alone does not define which profile position the row occurrence names. |
| Known callback context | `notes/design/2026-10-03-callback-context-delivery.md` §§1–4, especially §2 step 1 and its exclusions | B receives an already instantiated `F_cb`, `beta`, `Slots(beta)`; preserves static identity separately from dynamic receiver activation. Explicit annotation/callback overlap is excluded from this bounded judgment. It cannot construct the present mapping. |
| Parameter and result formation | `notes/design/2026-10-02-typed-computation-core-elaboration.md`: §6 lines 303–350, 387–440; §7 lines 537–560 | Annotated endpoints use an *admitted annotation derivation*. Outer Value/Computation role does not solve nested paths. Normalize uses a corresponding *known* source computation port with its profile. Checking preserves supplied decorations and cannot manufacture a receipt or boundary. |
| Complete Function observation | Same file, §9 lines 904–996 | `J_arg`, closure `J_body` and complete `J_call` are distinct. Value-entry force can expose a request even for a pure body. The §6 lambda result skeleton is not a solved complete-call scheme. Thus reading an arrow RHS in the CST does not by itself identify its complete-view observation position. |
| Profile substrate | `notes/design/2026-10-02-typed-boundary-realization-draft.md`, §6 lines 665–699 | Views include signature position and evidence root; signature paths distinguish call/result/thunk/structural positions. Decorated recursive graphs retain explicit annotation occurrences. Profiles are supplied by source elaboration; deriving them from arbitrary syntax is expressly open. |
| Transport after formation | Same §6, lines 704–781, 819–831 | Indexed typed correspondences carry original profile evidence and `D`, retaining shared `K` under one `nu`. Call effects are not copied into latent result effects. Matching `Flow`, receipt and event-specific `Observe` are separate premises for a later path witness. |

The prior audit is
`notes/progress/2026-10-05-annotation-scoped-effect-protection-boundary.md`,
sections “Smallest evidence obligation” and “Frame obligations”. This pass
reduces its requested correspondence to the seam below; it does not re-run
its U/A/O/J symbolic attack or promote its conditional conclusion to a source
theorem. Its file header remains an unreviewed checkpoint; independent review
status is owned by the primary's supplied review record, not certified here.

## What syntax and HIR actually preserve

The parameter's `:` is owned by `PatternTypeAnnotation`
(`crates/yu-syntax/src/pattern/mod.rs`:1077–1099), whose RHS requests a complete
`TypeExpression` (1300–1337). Ordinary arrow parsing creates `TypeArrowTail`
and parses its RHS ( `crates/yu-syntax/src/type_expr/mod.rs`:2198–2245);
leading computation brackets create `BracketRow` before their following
type head (1355–1444, 1595–1625). These owners preserve syntactic containment
and source extent. They do not allocate `beta`, `Slots(beta)`, a typed
effect path, a protection permission, or a local comparison certificate.
No parser run was performed for the example, so this is inspection of the
owner rules, not a newly established acceptance/CST snapshot for that source.

An expression `as` independently owns `TypeAnnotationTail` and its complete
Type (`crates/yu-syntax/src/expression/tails/type_annotation.rs`:1–48).
It is a different source boundary from this parameter `:`; a shared target
spelling does not identify the two occurrences.

Current production association retains an annotation wrapper and range but
does not retain arbitrary ordinary type nodes as typed descriptors:
`crates/yu-hir/src/lib.rs`:50–72, 305–315, 458–523. Its
`collect_nested_items` recursively selects operator chains and recovery nodes;
it supplies no annotation-to-profile lowering. Production `ResolvedExpr`
contains Lambda/Integer/Name/Error only
(`crates/yu-hir/src/module.rs`:426–450); the admitted plain header forms are
identifier-only (`plain_binding_header`:1471–1517). `crates/yu-core/src/lib.rs`
contains only its boundary module comment. These inspected seams do not
implement the missing judgment. Test-only research structures elsewhere in
`yu-hir` were not used as production evidence.

Consequently a syntax address such as
`(source occurrence, enclosing parameter annotation, arrow RHS, bracket row)`
is a candidate identity input. Its equality with an original typed profile
position is not established. Reconstructing a row from inferred support, or
equating family/type-variable identities, would discard distinctions the
typed-boundary declarations expressly retain.

## Minimum additional judgment and conditional derivation

The missing *local* evidence can be stated as the following proof interface,
without selecting its algorithm, representation, or semantic rule:

```text
AdmittedAnnotation(Gamma, omega, source_scope, current_endpoint, target,
                   local_realization, predecessor_evidence; nu,K,D)
CompletedOriginalContract(source_component, beta, F_cb, Slots(beta); nu,K,D)
    -- still missing source derivation -->
Corresponds(omega, source_scope, beta, original_effect_position,
            original_profile_entry, concrete_io_permission,
            local_realization, predecessor_evidence; nu,K,D)
```

`Corresponds` is a name for the missing evidence, not a new language judgment
being adopted. Its derivation must explain which original effect position
the syntactic row governs in the role-indexed completed contract, retain the
occurrence and lexical scope, preserve the same joint assignment and original
predicate identities, and attach precisely the approved `io` permission.
It must also retain local boundary realization; replacing the incoming
endpoint with the exported target does not equate their evidence roots.
Generalization and instantiation must preserve this relationship; those
preservation proofs remain outside this local audit.

Neither premise alone supplies the conclusion. An admitted target comparison
provides the target/evidence boundary, while a completed contract supplies
positions; a typed source derivation linking these objects is still needed.
In particular, the known-port premise in Normalize and the supplied-profile
premise in typed-boundary §6 cannot prove their own source construction.

**Conditional consequence:** if that missing derivation provides a profile
at position `p`, the existing indexed transport can carry it along a separately
supplied matching typed correspondence, retaining `(nu,K,D)` and its evidence.
A later matched receipt/`Observe` can then identify an applicable observation.
This is instantiation of the Draft transport package's premises. It establishes
neither source acceptance nor removal. A source handler/removal witness remains
an additional obligation even when permission and observation are both known.

## Smallest position discriminator

One original effect position cannot distinguish a mapper that erases effect
depth. The smallest structural discriminator has two distinct original effect
positions, an immediate Function call and a returned Function call:

```text
P = {p0 = call.effect, p1 = result.function.call.effect}; p0 != p1
A: annotation omega0 contains io at depth 0
B: annotation omega1 contains io at depth 1

Illustrative type spellings:
A: _ -> [io] (_ -> [] _)
B: _ -> [] (_ -> [io] _)
```

These are symbolic annotation-position witnesses. Their use assumes an admitted
two-level signature and a candidate syntactic-to-typed depth correspondence;
neither raw-source acceptance nor complete membership is asserted. `[]` marks
the other syntactic row in the illustration; it does not stand for absence of
the enclosing annotation or establish a new protection rule.

Both witnesses contain exactly one `io` row occurrence. A candidate that keys
permission only by family, closure identity or the enclosing annotation's
presence loses their different occurrence depths. A candidate that always maps
every row beneath the outer arrow to `p0` likewise loses B's nested position.
The existing typed declarations require preserving distinct original positions,
but they do not complete the source rule determining the applicable permission
in either admitted target. The discriminator therefore demands a correspondence
witness; it does not choose a permission outcome for B. Once formation supplies
distinct positions, typed-boundary §6 already forbids transporting `p0` to `p1`
without an explicit matching correspondence.

This is a minimal *structural* witness, not a minimized executable counterexample
to the current compiler. No semantic mutants were executed. Flattening depth,
selecting positions after `Q` succeeds, rebuilding profiles from row support,
or turning permission into actual subtraction would each invalidate the stated
proof interface for different reasons.

## Dependencies, checks, coverage and freeze

All direct dependencies read from the worktree were byte-compared to
`git show <baseline>:<path>` and `git show HEAD:<path>` after inspection. Every
listed dependency matched both; HEAD remained the baseline. Mutable task/index
files and the laboratory startup seed were used only as routing context, not
as semantic premises. Their concurrent edits were preserved. No changed
dependency was consumed. The `spec/` directory and shorthand typed-core path
were absent; no substitute specification was guessed.

SHA-256 dependency snapshot:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `2b04b178b08e8f4fbb74988c528eb1c324d89242c9e060e52cbbe2f14c8fd2f8` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-05-annotation-scoped-effect-protection-boundary.md` | `1dabf2181313187faec48f87e405218f1a415ddef7eb8bfc1743faac81533fd3` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs` | `edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a` |
| `crates/yu-hir/src/lib.rs` | `56aafd7d958acdfa3362ffcc7bf3e815d795f455597cf4f8e471194addb04c1b` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-core/src/lib.rs` | `9c67fc1fbd1632233d10dd021805e37752be0e39e631714e983e228dbac65b0b` |

Checks: bounded `cat`, `sed`, `rg`/`rg --files`, read-only HEAD/status queries,
and a Python byte/hash comparison using read-only `git show`. The leased path
was absent before creation. Final artifact hashing and dependency revalidation
are reported in the return packet. No Git mutations, tests, builds, executable
probes, Oracle runs, randomized seeds, ranges or performance samples occurred.
One lightweight command process at a time; no children or heavyweight process.
Peak CPU/RAM and elapsed wall time were not measured. Some broad locator output
was truncated; conclusions use the subsequent narrow source excerpts only.

No independent oracle exists in this method: the positive facts come directly
from the pinned source declarations/code, while the conditional consequence
shares the Draft package's supplied-profile and typed-flow assumptions. It does
not validate those assumptions with another implementation. Omitted scope:
complete grammar/acceptance, legacy Oracle lowering, arbitrary annotations and
recursive profiles, inference/principality, complete Function membership,
operational removal/lifetime, and production conformance. Failure of admitted
annotation checking, completed-contract formation, shared assignment, the
missing correspondence or later event/removal evidence blocks the corresponding
conditional conclusion. None may be supplied after comparison success merely
to make a query pass.

Recommended next action: the primary should commission or adjudicate the local
source derivation from the admitted annotation boundary to the completed
original profile, using the two-depth discriminator to prevent occurrence
erasure. If sources cannot determine its clauses, return that exact seam for
a scoped design decision before any model or compiler assumes it.

## Commit packet

- Exact lease: `notes/progress/2026-10-06-annotation-occurrence-profile-bridge.md`.
- Baseline: `ea7146a5a5ef6edffe56fe258576ec4f15bbc862`.
- Changed dependency hashes: none; direct semantic/code inputs matched baseline,
  current HEAD and worktree at the recorded revalidation.
- Claim/review status: unreviewed bounded source audit and conditional obligation;
  no independent certification, theorem closure or implementation authority.
- Checks already run: source locator inspection and dependency byte/hash checks;
  no executable checks, builds or tests. Final artifact hash belongs in the
  primary's integration packet, avoiding a self-referential hash in this file.
- Proposed commit: `research: isolate annotation occurrence to original profile bridge`.
- Deferred shared deltas: primary/curator may link this audit and record the
  admitted-annotation-to-completed-original-profile premise as still open in
  `tasks/current.md` and theory maps. No authority, index, question, compiler,
  manifest or shared-record changes belong to this lease.
