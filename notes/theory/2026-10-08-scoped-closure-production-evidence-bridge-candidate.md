# ScopedClosure: production evidence bridge candidate

Date: 2026-10-08
Status: Draft / non-authoritative / frozen research candidate; independent review pending
Claim class: bounded construction-owner audit and conditional correspondence derivation
Baseline: `47efeac749b110f322cb96c947c6372b73c30cb7`
Scope: current HIR/collection/SCC lifecycle to the selected native source Generalize object
Implementation, test-hook, API, cutover and gate-closure authority: none
Exclusive lease: this note only

## 1. Objective, authority and stopping point

The objective is to retain source construction evidence at its owner so a later
generalizer consumes it directly. This is a production/source correspondence
candidate, not another proof of the already selected native source partition.

Governing sources are [source Generalize definition](../design/2026-10-08-source-generalize-definition.md)
§§2–4 and [its proof](2026-10-08-source-generalize-definition-and-proof.md)
§§2–5.2, [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
Gates D–E and §5, [compiler engineering](../../rules/compiler-engineering.md)
“Natural compiler behavior and proof-obligation economy”, and
[current task](../../tasks/current.md) “FRESH_LIFE native source-partition
adjudication”, “Current F5 implementation locator audit” and “F5
frozen-consumer and publication boundary”. These sections retain the selected
language meaning and leave actual compiler identification open.

The selected object is
`ScopedClosure(p,C,T,anchors_b,templates_b,N_b,R_b)`. Current production
retains branded roots, parameters, occurrences and definition-use topology.
It does not supply this object's complete source program, original scope tree
or provider/world/lifetime anchor package. The precise stopping point is
the missing compiler output of source Build and complete invocation/initializer
formation, before source Generalize can consume those records. A row map or a
successful F5 solve cannot supply the missing evidence.

All novel record wrappers and phase handoffs below are conditional research.
The semantic records they reference already have owning source rules in proof
§3.3. Where an actual local source law or production owner is missing, this
note leaves an obligation; it creates no successful primitive or foreign law.
The pending Application_N answer is neither read nor used. F5 Q/R metadata
is never an eligibility oracle.

## 2. Proposed minimal typed interface

The following is interface notation, not Rust implementation approval. IDs
are opaque references branded by one immutable source construction artifact.
Existing HIR/collection brands can identify its inputs; they do not certify
the referenced semantic records. A telescope is the original ordered binder
and free-field incidence, not an unordered set of free variables.

```text
SourceBuild = (registered_components, T, rule_graph, record_table)

ScopedClosureInput = {
  p: SourcePublicationRef,
  C: RegisteredSourceComponentRef,
  T: OriginalBinderTreeRef,
  anchors: FixedFieldAndSharedBinderRefs,
  templates: ScopedDescDeclarationRefs,
  N: CompleteRetainedRuleGraphRef,
  R: FinalFormedRootRef
}

OwningRecord = MemberEntry | Live | Desc | Mono | Published | Family
            | Instance | Alias | Executed | Shared | ViewLogic
            | Event | EventField | EventProof | Check | Specialize

FieldEdge = Internal(C,member) | Description(C,introduction)
          | Established(contract,field) | Intrinsic(declaration,field)
          | OneShot(initializer,field)
```

Every edge references a typed target field and its complete dependency
telescope. A rule record retains its actual source occurrence, rule schema,
operands, binder region and clauses; these are references to the selected
§3.3/§4 data, not additional semantic success predicates. Shared/ViewLogic/
Event/EventProof remain distinct record constructors with their source
binders. Sort, scope and ownership cannot be inferred from a field's ID.

| Field | Required constructing owner and phase | Existing code evidence / missing supplier |
| --- | --- | --- |
| `p` | Actual immutable/SCC/source-boundary publication, after its source FinalRoot selection | `execute_scc_plan_inner` installs schemes before incoming routes; that is a compiler scheduling seam, not an identified source publication event. `DefinitionRootId` identifies a binding, not an execution/publication. |
| `C` | Source definition/recursive-group registration | `collect_mode` registers definitions and seals `SccPlan::build` after total endpoint resolution. Matching that SCC partition to validating source components remains an obligation. |
| `T` | Source Parameter, inference, checking and event binder introductions, during Build | HIR parameter scope resolves Name operands; `parameter_recipes` retains IDs. No complete original type/proof/event binder tree is supplied. |
| `anchors` | Member installation, import/rebind, execution and environment evidence introductions | HIR Name resolution and definition-use endpoints provide routing identities. Complete provider, allocation, world, lifetime, installed contract and one-shot evidence records are missing. |
| `templates` | Source Generalize's retain/fix walk on `p,C`, before use assignments | The compiler can retain the actual parameter introduction; it cannot derive its eligibility from `LiveVariableMetadata`, row level or Q/R. All fix dependencies must first exist. |
| `N` | Source Build at each constructor, followed by whole-component closure | `ConstraintOccurrence`, `LambdaRecipe` and live bound tables store F5 constraints/recipes. Identification with all selected source/checking clauses and original scopes is unproved. |
| `R` | FinalRoot at actual annotation/common/synthesis formation | `root_component_positions` stores the F5 definition-value recipe. An annotation target and its realization evidence need a separate authentic formation supplier; they are absent in the inspected ordinary slice. |

There is no extra `Eligible`, `LegalSource`, `CompleteRelation` or
`FutureSafe` Boolean. Retain/fix results are reproducible walks over typed
records. The whole relation and constraints to fixed fields remain active.
OneShot values are shared; Shared keeps its original binder even before a
witness is assigned. Native `ScopedClosure` is an internal producer object;
it is not automatically the transformed displayable public scheme.

## 3. Exact owner/consumer handoffs

Locators below are at the pinned baseline. They identify seams, not approved
replacement functions.

1. **HIR identity and resolution.** `yu-hir/src/module.rs`:
   `lower_module` (867), `lower_module_with_counters` (901), `lower_plan`
   (1246), and `lower_leaf` (1966) construct artifact-branded definition,
   parameter and expression identities and exact Name resolution. Conditional
   retention belongs beside the owning source introduction, while the rule
   operands and lexical environment are known. The optional source identity
   hooks at 877/889 are evidence joins only; parse locations alone cannot
   provide semantic records. `EvaluationClass::FetchValue` is an F5 admission
   classification and is not native Desc eligibility.
2. **Collection and registration.** `yu-solver/src/lib.rs`:
   `ConstraintBatch::collect` (855), `collect_mode` (859), endpoint resolution
   and seal (roughly 1190–1330), and `emit_lambda` (1717) retain existing
   recipes and freeze topology. A conditional SourceBuild output would keep
   complete constructor clauses and scopes alongside these identities, and
   classify internal versus established references from registered source
   ownership. It would be frozen before solving could influence classification.
   Neither `TermBuilder::seal` nor total endpoint maps establish this output.
3. **Component generalization.** `InferenceSession` (7419) and
   `execute_scc_plan_inner` (13135) freeze the component bounds, create member
   drafts, normalize/finalize all drafts, install them, then route incoming
   uses. `component_generalization_draft` (15475) currently starts an
   `F5cGeneralizer` from a live root row. The conditional native consumer would
   instead receive the complete SourceBuild, an authentic `p`, and FinalRoot
   evidence, perform §5.1's walk, and produce one component closure with member
   root incidences. Replacing that function alone does not change publication,
   closed-scheme storage or incoming consumption coherently.
4. **Use allocation.** `route_internal` (14253) and `route_incoming_inner`
   (15162) currently consume session rows and closed F5 schemes. Source §5.2's
   `new`, alias and actual-event allocation must consume constructor-owned
   Instance/Alias/Live records; “incoming” alone cannot decide those meanings.
   One native incoming instance opens the whole component, with internal peers
   and constraints in one frame. A correspondence from current routes remains
   unproved.
5. **Frozen results.** `SolvedModule` (7333), `run` (9969), `finish` (15740),
   and `SolvedModule::solve` (16027) own consuming completion. A successor
   design must cover durable member/root storage, occurrence and root
   projections, retained `ConstraintStore`, routed provenance, diagnostics,
   counters and feature-gated observations. Existing closed-type finalization
   is a different transaction from source component installation. The current
   root storage is `Vec<Option<ClosedValueScheme>>` plus a closed arena; there
   is no production ScopedClosure consumer.

All paths in this section are under `crates/`. Ordinary lowering/collect/solve
remain the F5 route. Existing `shadow-*` feature entrypoints and test-only
flat candidates are separate, default-off experiments that still use current
F5 products. A possible default-off source-record observer would require
separate exact authorization even if implemented only under `cfg(test)`.
This note neither adds that observer nor endorses an ordinary production route.

## 4. Local-law suppliers and residual obligations

| Premise | Selected source supplier | Actual production correspondence still needed |
| --- | --- | --- |
| L1 | Independently declared primitive's full local relation, operand telescope, guard, effects and admission/future laws, proof §2 | Int collection emits polarized leaf facts. No theorem here identifies those facts with every actual primitive law or complete evidence field; opaque primitive field classes must be supplied by its owner. |
| L2 | Proof §§3.1/4's original constructors; selected native signature formation §§2–4; captured closure definition §§2–4 | HIR Integer/Name/Lambda recipes supply syntax-directed operands for their admitted shapes. Complete receipt, Value entry, current-state Force, result forwarding, pending Bind and original event/evidence outputs are not retained by these recipes. No Apply law is inferred. |
| L3 | Proof §3.2's finite independent checking/conversion grammar, with whole Function domain/observation premises | Current solving and row comparisons do not provide identified local proof trees and original scopes. Actual annotation/conversion realization needs its owning certificate; query success cannot replace it. |
| L4 | Proof §2's joint world/annotation/primitive introduction; selected recursive interface definition §§2–3 and captured closure §§2–4 in their bounded cases | An SCC schedule does not prove original joint member/world validity. The exact `f/g` source constructor theorem does not identify the compiler's F5 SCC drafts with that constructor. General initializers, State and profile laws remain unprovided here. |
| L5 | Original future/context/lifetime constructors in proof §2, with all original Option 2 arms | No actual activation-liveness/future-context evidence supplier is identified in these HIR/solver files. Immutable native cases do not supply mutable State or foreign W/Z laws. |

The source theorem has independent declarative rules and symbolic Build rules;
their adequacy was already reviewed under these genuine local premises. This
audit shares that selected contract and reads production code independently
of a supplied toy transition table. It is independent evidence of the missing
record outputs, not independent review of the source theorem or a proof of L1–L5.
No executable checker is offered: duplicating supplied source transitions would
not establish their production construction or their independent local laws.

## 5. Cases that constrain retention

**Capture/import.** `Mono/Established` imports retain the entire installed
contract and all free fields in fix mode. A bound independently typed Family
parameter remains bound. A prior Family already instantiated to Mono is fixed
as that instance. `SemanticImports::empty()` is the only standalone HIR import
input; it cannot validate the general import case. A returned own closure fixes
its raw provider but keeps a separate Internal inferred-description edge.
The ordinary one-parameter/direct-body slice lacks the approved nested step's
complete capture/event output. No reclassification from provider equality is
allowed.

**Annotation.** FinalRoot retains the final source target and earlier local
realizations; actual conversion fixes the resulting provider. `plain_binding_header`
(module.rs 2023) admits identifier-only targets and a single identifier
parameter; these inspected ordinary recipes have no annotated root supplier.
A missing supplier is a research blocker, not a proposal to reject annotations
or export an easier pre-annotation root.

**Recursive SCC.** `MemberEntry` has fixed operational fields and Internal
description fields. Both remain distinct when walking a world back-reference.
The complete simultaneous relation is retained at member and tuple publication.
Current SCC internal/incoming partitions give graph evidence, not the semantic
classification of every record. All background/member clauses survive member
root selection. The selected pair `my f x=g; my g y=f` has two eligible
parameter declarations in its exact native scope; F5 row counts do not prove it.

**Alias/new.** Real polymorphic source instantiation creates Instance;
Alias/reuse preserves one frame. A later publication of a rebind can itself
generalize under its actual source rule. Thus syntax `my a=id` alone does not
settle all later new/alias events. A production bridge must retain the owning
rule's event rather than reconstruct it from a Name spelling or SCC direction.

**Event/proof scope.** Shared is once in the base tree; ViewLogic is once per
incoming description frame before its challenges. Actual EventField is shared
at its source event; EventProof may vary per frame under that same event while
sharing runtime operands. A template is only an ordinary Desc declaration at
its original type scope. Request rigid openings and inference existentials
remain distinct; variable guards apply on every derived comparison. Retaining
these records does not propose new runtime tags, extra allocations, or a
universal-handler reinterpretation of an ordinary pure function.

## 6. Conditional derivation and smallest construction-gap witness

The correspondence candidate has these explicit hypotheses:

- H1: authentic source registration and all constructor records from §3.3
  are retained with exact branded input/operand correspondence.
- H2: every retained rule graph node and binder corresponds to Build §4,
  with no omitted local clause, alternative, free dependency or telescope.
- H3: actual publication/FinalRoot and initializer/provider/world evidence
  are supplied at their independently authorized source owners.
- H4: every reached local law L1–L5 has genuine evidence for the claimed case.
- H5: use allocation and publication consumers preserve the complete records
  and transaction invariants, including one joint strategy and fixed fields.

Under H1–H3, run the selected §5.1 walk: seed whole `N,R,T` in retain;
seed operational/Established/Intrinsic/OneShot fields in fix; retain Internal
relations without undoing fixed marks; keep original logical/event binders;
select exactly retained own Desc records not marked fixed. Each step refers
to the same constructor edge and telescope as source Generalize. Induction
over the finite worklist (registered cycles visited once) gives identical
fixed/eligible sets and original template placement. Hence the constructed
tuple is the selected ScopedClosure. Under H4–H5, SRC/SRC-J/GS/GC apply to its
source uses; compiler solving, effective consumer completeness and public
transformed export still need their separate correspondence proofs. This is
a conditional derivation, not an established production theorem.

The smallest inspected source needing a nonempty template is:

```yu
my id x = x
```

HIR supplies one parameter identity and a Name resolved to that parameter.
`emit_lambda` recognizes that same operand and `LambdaRecipe` uses
`body_value_component=None`, preserving the current parameter/body linkage.
Native Parameter supplies `Desc(C,x,Value,sigma,Delta)` before invocation;
Name/Result uses that same declaration, and the complete invocation adds its
original receipt/entry/result scopes and evidence. Current recipes store
neither `sigma,Delta,T` nor that complete source rule/evidence graph. H1's
identity fragment is observable; H2–H4 are not established even for this
one-binding source. Removing the parameter leaves no parameter template;
removing its Name use loses the repeated-endpoint linkage. This is a minimized
construction-gap witness, not a claim that current `id` behavior is incorrect.

Named falsifiers for a future retained-record experiment are: omit a fixed
contract's free Desc dependency; relabel a MemberEntry Internal edge as
Established; copy Shared per incoming frame; allocate ViewLogic per challenge;
merge actual EventField with per-frame EventProof; drop a peer conjunct; or
replace an annotation target with the synthesis root. Each violates a specific
selected walk/allocation rule. None of these mutations was executed here.
An experiment would have to compare independently supplied owning-rule traces
with the retained artifact, not two walkers fed the same assumed edge table.

## 7. Rollback, publication and natural behavior

Conditional record retention must be private to one construction/solve attempt.
Collection failure returns no sealed artifact. Component failure cannot expose
one member's closure before its peer records and all required finalization are
valid; incoming attempt failure must discard its frame, facts, provenance and
diagnostic delta together. Actual initializer effects are fixed source events,
not operations retried by Generalize or type-view allocation. A successful
terminal solve publishes the records, closed products and projections together.
Branded roots from another build/solve cannot address the new artifact.

Current all-draft staging, route transactions and consuming `finish` locate
these engineering responsibilities. They do not prove an unimplemented native
record transaction. Existing per-scheme closed-type rollback is not sufficient
evidence for all-component/module atomic publication of a successor object.
Feature observations require an explicit preserve/revise/retire disposition;
silently returning F5 Q/R observations with new meanings would misidentify them.

Safety failures are omitted dependencies/scopes, stale brands, split worlds,
lost recursive relations, copied fixed witnesses or partial publication.
Natural-inference risks are treating every environment edge as established,
coupling eligibility to solved shape, reexecuting initialization per use,
requiring annotations because evidence is missing, or dropping independent
alternatives to obtain a finite graph. The selected contract forbids these
shortcuts. Output sharing alone proves no complexity bound. Graph dimension,
telescope/field incidence, alternatives, use frames, proof-development paths
and public output size require a separately budgeted Gate D analysis. No
numeric cap, deterministic rejection policy or performance claim is selected.

## 8. Coverage, checks and next action

Reads were bounded to the named rules/authority, current task sections,
selected constructor definitions and the two owning source files. This is not
a repository-wide absence proof. No legacy/oracle execution, tests, builds,
search enumeration, probes, mutations, formatting or Git mutation ran.
Seeds/ranges and oracle execution are inapplicable. Shell reads and final
deterministic note/link/hash/diff checks were sequential lightweight processes;
no heavyweight process ran. CPU/RSS and total wall-time were not measured.

Only this leased note changed. It is frozen before submission. Source
partition, aggregate FRESH_LIFE, Generalize/public export, L1–L5 correspondence,
solving, lifetime, State, foreign W/Z, resource behavior and cutover remain
unverified at their original scopes. Independent review of this note is pending.

Recommended next action: the primary should assign a narrow owner/phase design
for SourceBuild's complete invocation and original scope/event outputs for
`my id x=x`, using actual selected local laws. Obtain exact implementation
authorization only after that supplier/interface is reviewed. Until then,
another native partition or Q/R probe leaves H2–H4 untouched.

## 9. Frozen dependency manifest and commit packet

SHA-256 hashes below identify the final checked snapshot. HEAD advanced to
`605e455d32ef61a562a4274f11a1457f8aa75d54` during this lease. The twelve
listed rule/source/code dependencies other than `tasks/current.md` match both
the pinned baseline and final working files. The primary-owned task record
changed from baseline hash
`28937e084545822ba25a850e83a0f3c58d96dd4b697c0cdebc6d3cef5d3e372d`
through initial-read hash
`e2f0ecb8a1ddcb8fc8519ca163ced8f4559fed819ef20c2842c86c6ef304af79`
to the final hash below. Its relevant delta records bounded source-partition
counterexample/review evidence and preserves the production/lifecycle blocker.
The named F5 owner/consumer sections were rechecked unchanged. This unrelated
checkpoint/curation movement does not supply H2–H4 or invalidate this audit;
the primary should recheck any further movement at integration.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/compiler-engineering.md` | `1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442` |
| `tasks/current.md` | `24e24c3913e6be1aa094069eca4247ae825fb56ad2b992ab6ff617cc768a80ee` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-08-native-recursive-interface-definition.md` | `a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |

- Exact leased path: `notes/theory/2026-10-08-scoped-closure-production-evidence-bridge-candidate.md`.
- Baseline: `47efeac749b110f322cb96c947c6372b73c30cb7`; only task-record
  dependency hash changed, as described above; all source/code/rule hashes match.
- Review status: unreviewed, frozen Draft research; no gate closure or adoption.
- Checks: dependency/HEAD recheck, five relative Markdown file links, nine
  required sections, whitespace and exact one-file diff scope passed.
- Proposed checkpoint message: `research: map ScopedClosure construction evidence to production owners`.
- Shared deltas for primary/curator only: locate this candidate from the active
  production correspondence work; record the missing complete SourceBuild and
  event/scope suppliers. Preserve all aggregate statuses and prerequisites;
  no task/index/DAG/question record was edited.
