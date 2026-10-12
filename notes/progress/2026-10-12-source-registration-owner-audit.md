# Nested helper: source registration and allocation owner audit

Date: 2026-10-12
Status: frozen unreviewed research; bounded source/API characterization
Assigned baseline: `ba93e1739`, branch `research/simple-sub-intrusion`
Producer: `/root/audit_source_registration_owners`, complementary researcher leaf
Exclusive write lease: this file only; no implementation authority
Requested model/effort: `gpt-6.1-sol/high`; observed effective metadata: unavailable

## Objective and exact premise

Trace the actual owners of helper publication `p_g`, validating source
component `K_g`, recursive f incidence, parameter declaration B, and the
scoped extrusion equalities `C=B`, `D=R`. Determine whether inspected
source routes supply the records needed by Source Generalize's typed
fixed-closure/allocation rules. This is a constructor/field census, not the
prover's construction, another correlated-helper attack, or a new witness.

The existing source is the unchanged 116-byte fixture in
[the exact-source bridge](../theory/2026-10-12-two-use-exact-source-bridge.md#1-frozen-statement-and-authority):

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

Its complete binder/Name/Call structure remains in scope. g has a
parameterized initializer and temporary self binding, but no resolved g
self-reference; f is the actual recursive capture in g's body. This audit
does not remove the existing answer, drop or first bindings, or substitute
another source program. The previously reviewed parser/LocalSource/candidate
observation is an imported bounded result, not a new execution by this worker.

**Result class:** bounded static owner-contract mismatch. The inspected
LocalSource/candidate route preserves this source structure and can plan
native constraints. Its registration outputs do not supply the selected
`p_g,K_g` and typed whole-component dependency records. Therefore this
route cannot presently instantiate the selected Source Generalize closure
from its emitted records. This does not refute the source theorem or show
source rejection, impossibility, or absence from every compiler route.

The first missing source-owned premise is **validating component registration
for the actual nested helper**, at `local_source.rs::Builder::block`, then
its transport through `ConstraintBatch::emit_candidate_source`. Their
outputs retain local identity and lexical scope; neither output records the
actual source component or distinguishes a recursive `Internal` description
dependency from an external `Established/Mono` contract. Local publication
later stores only `(id,root,boundary)` and cannot repair that missing fact.

## Governing sources and unchanged decisions

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5: native generation/accumulation/propagation; proof-directed
  construction; no proof-convenience source restriction.
- [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md)
  §§2–4, selecting [construction](../theory/2026-10-08-source-generalize-definition-and-proof.md)
  §§3–5.3. §3.3 supplies typed records at their owning constructors; §4
  builds the open rule program retaining those records; §5.1 obtains p's
  validating component from source registration and walks typed edges;
  §5.2 allocates whole component frames and original telescopes; §5.3
  distinguishes own/live recursion, external captures and publication.
- [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
  **Approved extrusion-event qualification** and **Definition-root origin
  for nested call-demand extrusion**: the existing G-origin/F-receiver
  event qualifies its actual polar pairs; the integrated nested-origin
  decision is `c0b67771d`. SCC membership decides activation, not `K_g`.
- `tasks/current.md`, latest **quotient solution correspondence and
  source-allocation boundary**: actual registration/classification is OPEN;
  numeric level and Value SCC do not supply it. The primary confirmed that
  the earlier architect result has no separate frozen artifact; its
  standalone-expression owner findings are in the current task record.

The audit assumes the source/authority dependency bytes below are the
primary's intended pinned inputs. Baseline equality was not independently
checked through Git. Exact-source parse observations are imported from their
record; no parser, semantic admission or solver execution was repeated.

## Complete bounded route and field trace

All source paths in this table are below `crates/`.

| Stage / required fact | Actual producer and consumer | Retained output and precise limit |
| --- | --- | --- |
| Opt-in full nested carrier | `yu-hir/src/shadow.rs:38`; `module.rs:1411–1427`; `module/local_source.rs::form` | LocalSource belongs to answer's DefinitionRootId and retains all binding/expression slots. This is nonshipping HIR formation, not semantic admission. |
| Local g and f registration; candidate for `K_g` | `module/local_source.rs::Builder::block:698–828`, especially `:746–818`; `LocalSourceBinding:164–174` | HirLocalId, binder SourceNodeKey, parameter list, initializer index, lexical block scope. No validating-component record, complete component relation or typed `Internal/Established` edge is produced. SourceNodeKey and HirLocalId are authentic syntax identities, not semantic component certificates. |
| Recursive Name f in g | `local_source.rs:329–372` installs f's temporary initializer identity; Name `:636–657` resolves it; `candidate_source.rs:251–306,369–380` sees f in `active_initializers` | Same Local f and open initializer endpoint; `Action::Link` is selected before f's Install. Execution `:665–668`, then `candidate_scheme.rs::admit_candidate_value_link:1337–1345`, creates a polarized relation with occurrence provenance. This is not `Live(K_g,f)` or `Internal(K_g,f)` and does not decide whether actual f belongs to g's validating component. |
| Parameter B introduction/telescope | `LocalSourceParameter:155–163`; `block:770–802`; Lambda `:341–364`; `candidate_source.rs:187–217,266–283,540–558`; `candidate_call.rs::FormalRegistrationInput:16–22` | Parameter y keeps HirParameterId, source key, source scope and optional annotation. Candidate registration adds answer owner, Lambda index, recipe position, native root and numeric level. Neither supplies `Desc(K_g,q_y,Value,sigma_y,Delta_y)` or its free semantic dependency telescope. Lexical ordering is useful source incidence, not the whole original type/event telescope. |
| Native c=`f y` demand | `candidate_source.rs:394–411`; `candidate_call.rs::ApplySourceInput:30–47`; `shadow_apply.rs::admit_candidate_fact:1308` | Actual child indices, endpoint recipes, level, cause/checking occurrence, and native Function ports are retained. The owner is the module DefinitionRootId, not an explicit G-origin/F-receiver extrusion event. Local f is not a FormalName callee. |
| Actual `p_g` candidate publication | `candidate_source.rs::Work::Install:307–325`; `Stage::PublishLocal:35`; `step_candidate_source:624–631,645–648`; `candidate_scheme.rs::install_candidate_local_term:1320–1335` | The schedule boundary is real; initialization effects are emitted separately. Publication stores `LocalScheme { id, root, boundary }` (`candidate_scheme.rs:116–120`). It supplies no semantic publication identity, selected final-root rule graph, validating component, original binder tree, or typed fixed/template partition. `Stage::PublishLocal` is an operational scheduler stage, not `Published(p_g,Sigma_g)`. |
| Current local capture/fresh use | `candidate_scheme.rs::route_candidate_local_run:1354–1380`; `capture_candidate_graph_inner:721`; `Capture::row:301–326`; `prepare_candidate_fresh_use:981–1023` | The first local use captures live bounds and a numeric boundary. Row eligibility is `level > boundary && !non_generic`; freshening additionally uses `row.local`. Bound/effect evidence is retained, but this eligibility calculation consumes no Source Generalize component/Desc/Established/Shared record. There is no demonstrated equality between its local bit and §5.1's typed fix walk. |
| Extrusion pair producer | `candidate_extrusion.rs::candidate_extrude:21–26,90–136`; `candidate_intrusion.rs::retain_extrusion_parent:174–222`; `Parent:23–28` | Actual signed row pairs and target level survive; `Parent` has only copy, parent, polarity, target. The interface accepts no extrusion occurrence/source Values, publication component, declaration telescope or scoped equality-clause owner. |
| Current equality activation/consumer | `candidate_intrusion.rs::settle_candidate_intrusion:358–486` | It constructs dependencies from solver Value/Effect rows and bounds/Function ports, then compares the row pair's component IDs. It does not consume the approved Value graph/event G/F record. Its existing merges are not evidence of the selected event-qualified, original-scoped `C=B,D=R` clauses. |

Here “no record” means no field or constructor output supplying the required
fact in the cited complete data structure/body on this route. A search for
the selected record spellings was empty, but the conclusion relies on field
and consumer contracts, not absence of identifier names.

## Admission, module routes and original-reference limits

`CandidateInference::solve` (`shadow_apply.rs:79–113`) allows the retained
LocalSource binding route after `candidate_source::preflight:83–111`, which
checks supported annotations/operations and resolved Names. For the existing
answer fixture, the reviewed exact-source bridge supplies bounded evidence
that this route is reached. `ConstraintBatch::collect_candidate_mode`
(`lib.rs:904,985–986,1126–1137`) passes an actual DefinitionOrderId for the
module binding. Local f/g/drop are separately planned through source local
slots, not added to `batch.definitions` by that local emitter. The module SCC
and its active-root maps (`candidate_scheme.rs:850–880`) therefore do not
establish a nested helper's semantic `K_g`.

This route's own contracts are explicit: `shadow_apply.rs::UNRESOLVED`
(`:9–49`) retains SourceTypingAndAdmission, TypedOccurrenceIntroduction,
WholeTupleScopeTransport and GeneralizationAndFreshUseCorrespondence.
`CandidateInference::unresolved` returns that list (`:194`);
`source_call` (`:191–192`) borrows actual carrier/port incidence.
`candidate_call.rs::PendingCallConstruction::suppliers:225–247` still
requires original Gen-Call-0, argument reification/whole carrier, and
receiver/complete result/future interfaces. Its authentic scoped complete
Call is therefore unavailable. That semantic validity debt is **separate**
from classification: §4's symbolic Build and §5.2's allocation can retain and
classify actual typed records before their local clauses are satisfied. This
audit stops because those registration outputs are missing, not because
every Call must first be solved or proved valid.

The previously inspected complete direct module spelling with a final
standalone Name has an additional entrypoint obstruction; it must not be
generalized to the answer fixture or the language. `CandidateInference::solve`
accepts standalone integers only (`shadow_apply.rs:97–100`); the neighboring
`CandidateValueObservation` preflight has the same item restriction
(`:532–536`) and a subsequent internal-module-use refusal (`:547–555`).
If preflight alone were relaxed, standalone collection has no definition
parent (`lib.rs:985–986`) but `emit_candidate_expression`'s resolved Name
requires one (`shadow_apply.rs:1193–1203`). Thus that named route still lacks
the architect's standalone expression receiving context; no fabricated
definition ID, wrapper or dropped final Name is authorized here.

Original Simple-sub supplies native recursive root/parameter creation,
level-aware polarized extrusion and generalization, as established in the
existing exact-source/occurrence notes. It supplies no Yulang Value graph,
Source Generalize typed registration, actual `K_g`, or scoped clause
classification. This worker did not execute or reread a pinned Scala
checkout; no additional claim about its constructors is made.

## Discriminating conclusion and next owner action

The available facts distinguish three separate cuts:

1. Syntax construction retains the witness and actual f/y incidence.
2. Native candidate publication/freshening works from IDs, row bounds and
   numeric levels, with source semantics/correspondence explicitly unresolved.
3. Source Generalize needs actual publication/component registration, typed
   recursive/external dependencies, ordinary Desc declarations and original
   scoped local clauses. Those are not outputs of the inspected constructors.

Consequently no inspected route both preserves the full existing term and
emits enough typed registration data to apply the selected closure. This is
bounded correspondence evidence; uninspected routes remain unknown. It
selects neither “C fixed” nor “C templated”, and neither `F <-> G` nor the
numeric level changes that conclusion. No new minimized counterexample is
claimed; the old fixed-anchor contradiction remains conditional.

Recommended next action: assign the source-registration owner a constructive
instance of the approved nested definition/recursive registration rules,
producing actual `p_g,K_g`, f's typed dependency edge, B's Desc telescope and
the equality clause's original scope, before applying §5.1's walk. Return
that record to the prover. Any compiler prototype needs its own exact source
edit authorization. Complete Call/local-law validity remains a parallel OPEN
obligation and must not be disguised as a component-classification result.

## Checks, independence and omissions

Commands run: bounded `cat`, `sed -n`, `rg -n`, `rg --files`, `tail -n`,
`head -n`, `pwd`, and `sha256sum`; static field/body traces only. Early broad
captures truncated; decisive governing §§3–5.3 and owner bodies were read
again in bounded slices. Two exploratory rg calls named nonexistent globs/
one absent file; corrected locators were used. No tests, builds, parser or
inference probes, random seeds/ranges, mutations, benchmark samples, Git
operations, delegation, manifest edits or production edits occurred.

No executable oracle was used. Normative meaning comes from selected source
rules; implementation claims come from constructor and consumer bodies. They
share the fixed source and authority with the existing notes, so this is
complementary source evidence, not independent mathematical certification.
Zero heavyweight processes; lightweight shell commands were sequential.
CPU/RSS and exact wall time were not instrumented; the assigned ceiling was
25 minutes. Runtime allocation failures, feature/opt-in disabling,
dependency drift and unsupported/recovered syntax invalidate successful-route
hypotheses. Other production/generalization backends, all HIR syntax forms,
runtime world/allocation behavior, native live quotient realization,
soundness/principality, complete Call/effects and universal source admission
were not exhaustively audited. Parent gates remain OPEN.

## Dependency snapshot

No dependency was changed by this worker. SHA-256 of decisive read inputs:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 notes/design/2026-10-12-intrusion-value-type-association.md
d2689d6e0ee7581926916454481be9b384b54e04c3e73c874b9bd43a0cc3902f notes/theory/2026-10-12-two-use-exact-source-bridge.md
692903a8e5c8866b24102b5223700d50815a4b8a9cc6239c17027555936c1953 notes/progress/2026-10-12-quotient-solution-correspondence-falsification.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5 crates/yu-hir/src/module.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
```

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-source-registration-owner-audit.md`.
- Baseline SHA: `ba93e1739`, primary-supplied; primary revalidates revision
  equality and direct dependency hashes before integration.
- Changed dependency hashes: none by this producer; snapshot above.
- Claim/review status: frozen unreviewed bounded constructor/API audit;
  no independent review, theorem closure or implementation authority claimed.
- Checks already run: static governing/constructor/consumer reads, targeted
  record census and SHA-256 snapshot; no executable inference checks.
- Proposed message: `research: audit nested helper registration and allocation owners`.
- Shared deltas left to primary/curator: retain registration/allocation and
  parent intrusion/Call gates OPEN; record the missing nested validating
  component/typed dependency output at HIR registration and candidate
  transport. `tasks/current.md`, design/index/authority files, questions and
  all compiler paths remain unmodified by this worker.

Writes stop at this handoff; independent review must use this frozen artifact.
