# Original source generation and reconstruction: constructive author packet

Date: 2026-10-26. Parent baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`.
Status: **candidate formalization of the adopted SG construction; the complete
original semantic interpretation and native correspondence remain OPEN**.

## 1. What is constructed

The two new modules supply a total, constructor-directed function from raw
resolved source to a finite local-rule program, a compiler from that program
to a scoped constraint formula, and a checked reconstruction in both
directions. The source entry point accepts the original 13 expression,
11 pattern and 3 statement forms. It does **not** accept a caller-supplied
registered rule tree, a source typing proof, a local reconstruction law, a
complete source relation or an inference-success certificate.

The construction is in:

- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`;
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean`.

The useful new result is

```lean
source_reconstruction
  (kernel : Kernel Value) (environment : Environment Value)
  (context : Context) (source : Source category) :
  Satisfies kernel environment (Build context source) ↔
    SourceJudgment kernel environment context source
```

`sourceRules context source` constructs the rule program from the actual raw
constructors. `Judgment` and `Judgments` are separate inductive finite-rule
derivation grammars. Their constructors mention neither `Build`, `Formula`,
`Satisfies`, publication success nor native solver success. `SourceJudgment`
indexes that independent rule grammar by the canonical program of the raw
source. `Build` separately compiles the program into `Formula`.

The proof `reconstruction`/`reconstruction_forest` mutually recurses over the
rule program and all its children. It constructs the local proof and every
child proof, reconstructs each admitted existential witness, checks every
independently admitted universal challenge, and retains the selected union
branch. There is no child-reconstruction premise. Applying this proof to the
computed program gives `generated_constraints_imply_source_judgment` for
every raw constructor.

There is also a source-directed finite-client construction. `clientRules`
implements SG's `new`, `alias`, `view`, `run`, `join` and sequential `bind`,
plus termination and placement of an independently typed client predicate
`W`. `BuildJoint` compiles it, and `joint_reconstruction` proves SRC-J for the
same local-rule grammar and fixed environment. A `newUse` contains a raw
`Definition`; the builder constructs its source proof obligations itself.
It does not receive a pre-proved source description.

This closes a real construction step: a caller no longer has to supply a
correct registered source tree or the all-source reconstruction induction.
It does **not** establish that an arbitrary `Kernel` is the original Yulang
semantic kernel. The latter is a separate concrete definition and
correspondence obligation, described below. No concrete `SourceProblem`
instance or theorem of full native inference soundness is claimed here.

## 2. Authority and domain

The authority for the construction is
`notes/design/2026-10-08-source-generalize-definition.md` §2, selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
The latter's §6 gives SRC; §3.4 and §7.0 give the finite joint-client rule
grammar and SRC-J. These clauses explicitly distinguish the independent
source judgment from generation, retain original local meanings L1–L5, and
require actual finite checking derivations rather than inclusion-oracle
leaves.

The 13/11/3 inventory and constructor crosswalk are also recorded in
`docs/yulang-source-type-safety-ja.tex`, sections `sec:source` and
`sec:all-source`, and
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex`, section
"全 IR 構文の型付けと束縛". Those documents are research material; their
proposed implementation corrections are **not** silently promoted to
production policy by this packet. For example, the OR merge map is retained
as explicit resolved source data and checked by an original local relation;
the builder does not equate source spellings by comparing numeric binder IDs
or assert that the current Rust lowering has implemented a proposed merge.

The raw grammar is raw **relative to typing**. It carries source occurrence,
lexical binder, declaration and written-annotation identities, original
component classification, OR merge metadata and catch-arm order. None of
these fields is a proof. Annotation IDs refer to original written syntax;
the builder never manufactures an annotation from a solved endpoint.
`Formal.entry` uses the retained outer-source-annotation tag before body
checking; its consistency is an explicit original local premise.

This is not a Lean copy of Rust's `LocalSource`. Its relation to Rust's
source carriers, syntactic sugar, declaration tables, source identities,
scopes and component registration is not proved. In particular, a production
correspondence must validate the supplied original component/merge/arm-order
metadata against the authentic source construction. It must not obtain those
facts from a typing-success predicate. The raw builder remains total on
malformed data; the independently interpreted local clauses must reject
invalid data. Totality of this data function is not a source-validity theorem.

## 3. Exact expression construction

Each expression retains an original `Mark`. Written annotations generate a
separate final boundary from the synthesis port to the written-target port.
Those ports are distinct constructors of `Port`, even at the same source
occurrence. No source root is replaced by an interior synthesis root merely
because their solved types happen to coincide.

| Original expression | Canonical rule and generated local obligations |
| --- | --- |
| `Lit` | `literalDeclaration`, carrying the original literal; no child typing premise. |
| `PrimitiveOp` | One `primitiveDeclarationInstance` with the actual declaration identity and its full independent original local relation. |
| `Var` | Resolved same binding and computed-fetch-once clauses. `Published`/`Family` context entries additionally introduce one original whole instance; formal, pattern, internal and monomorphic entries retain their existing certificate. |
| `App` | One description/checking frame; original descriptor formation, whole inert argument compatibility, complete decorated Call certificate, raw Call incidence, callable image, finite complete-value checking of the returned callee and finite complete-computation checking of the invocation image. The selected singleton seed is guarded as explained in §5. |
| `RefSet` | Original invariant cell protocol and result relation, a direct value-to-same-cell-content boundary, reference child, and value child under the predecessor's actual return/pending-suffix telescope. No new State law is asserted. |
| `Lambda` | Ordinary formal description before the invocation challenge, one view-description frame, original captures/closure formation, universally admitted invocation, receipt, the source-selected entry, formal pattern and body. Value entry introduces the actual return/rebind telescope before the body. Retained computation entry omits that Force/rebind. Body checking retains the complete body consumer and its independent finite computation check. |
| `Tuple` | Original ordered child occurrences and `tupleFormation`; child sequence uses the actual return/pending-suffix telescope. Latent components are not automatically forced. |
| `Record` | `orderedRecordFormation` on the original ordered item sites. Each field/spread retains its label, value occurrence and visible-field update clause. No record boundary is replaced by zipped equal-shape scalar record subtyping. |
| `PolyVariant` | Original tag, payload occurrences and exact arity; ordered payload construction. |
| `Select` | The actual receiver, member name and retained selection choice; qualified-child and whole-instance obligations stay together in one original view frame. No arbitrary method law is supplied. |
| `Case` | Original scrutinee, ordered attempts, all arm result references and the common join relation; each arm has its own direct result boundary. Pattern/default/guard/body derivations are constructed. |
| `Catch` | Original scrutinee, original mixed arm order, complete packet-instance relation, shallow immediate residual coverage, preservation of latent interfaces and result join. Operation payload and continuation patterns are checked under the original rigid operation telescope. |
| `Block` | Source-ordered statements, their exact binding owners, original final-root relation and final expression under the original predecessor/rebind telescope. |

Aggregate clauses carry the actual ordered source operands via
`Source.roots`, not an arbitrary zero container ID. `Source.bindingRecords`
retains each nested lexical introduction's own source occurrence. A formal
pattern that denotes the same resolved identity preserves the original
formal registration instead of shadowing it with a second invented binding.

The scope/data predicates in this table have deliberately limited meanings.
For example, `closureFormation` is the original constructor/capture/interface
formation clause, **not** a promise that the whole body is typed; that body is
a generated child. `completeBodyConsumer` identifies the actual consumer;
the required checking proof is a separate premise. `branchJoin` connects the
original result ports; it does not stand in for the separate direct branch
boundaries.

## 4. Pattern and statement construction

| Original pattern | Preserved local rule data |
| --- | --- |
| `Wild` | No new binding and no invented comparison. |
| `Lit` | Original literal and comparison with the original pattern input. |
| `Var` | The exact lexical binding occurrence and input view. |
| `Tuple` | Original child sites, arity and ordered child pattern contexts. |
| `List` | Prefix/suffix operand lists, prefix length, original rest name and list-length/rest relation. |
| `Record` | Original field occurrences, visible-presence relation, spread name, default presence and default/input join. A default is checked before its own field binding and under earlier original field bindings. |
| `PolyVariant` | Exact tag, payload sites and arity. |
| `Con` | Resolved nominal declaration and original invariant type-argument references. |
| `Ref` | Resolved existing-definition comparison; it is neither a fresh lexical binder nor mutable reference allocation. |
| `As` | Same input alias and the actual child derivation. |
| `Or` | Ordered left/right attempts, original resolved left/right/result merge triples, and the independently checked common output environment. Neither branch's original bindings are guessed from integer identity equality. |

The pattern skeleton alone is not a proof of the source resolver's merge
policy, the list-pattern scope convention, successful matching, rollback or
match exhaustiveness. Those meanings belong to the original local clauses.
All source pattern constructors are represented; none is removed to make the
reconstruction proof pass.

| Original statement | Preserved local rule data |
| --- | --- |
| `Let` | Original registration/component classification and binding identities. A recursive component uses original monomorphic `Internal` entries and the genuine original simultaneous member/world introduction. Each initializer retains one actual one-shot/shared anchor and its final publication root. Earlier members are not prematurely reclassified as `Published` while later members of the same component are checked. |
| `Expr` | Source expression derivation and original discard relation, in ordered statement sequencing. |
| `Module` | Original declaration/linking relation and source-ordered body. The linking atom cannot mean that the whole module body is typed; the body is generated and reconstructed separately. |

The genuine L4 simultaneous introduction is intentionally still an original
local premise. Merely registering recursive names is not a proof of
hereditary membership or a world fixed point. The packet also does not replace
the original component graph with an arbitrary all-definitions SCC or drop
computed-root order.

A binding's written annotation is a distinct outer source boundary. If its
initializer already has its own written annotation/conversion, the next
boundary starts at `initializer.finalRoot` and ends at
`binding.writtenTarget`. Publication uses the binding's own final root.
It must not restart from `initializer.synthesis` or merge the two actual
boundaries. This was repaired during the final crosswalk; the first freeze
attempt and its otherwise passing census are retained as superseded, not
as evidence that the earlier source mapping was semantically final.

## 5. Full Call and the selected seed restriction

The exact semantic Call template is
`notes/progress/2026-10-06-source-call-generation-construction.md` §5:

```text
exists_sigma(F_c,e).
  WF_Dec(F_c;xi)
  & VIncl(A_f,F_c;xi,e_value)
  & WholeArgCompatible(J_x,CarrierContract(F_c);xi,e_arg)
  & CIncl(ExecuteCallableImage(J_f,Delay(J_x),F_c,e;xi),
          original result Comp(E_c,A_c);xi,e_result)
  & TypedCallCert_Dec(c,F_c,e;xi)
  & the applicable original role/source-origin records
```

The source variables in this formula are full original decorated interfaces,
not the scalar four-field `SimpleSub` approximation. The returned-callee port
is distinct from the callee code's source result port. The argument operand
is the source occurrence of the whole original `J_x`, not a printed
`Comp(empty,A_x)` approximation. The callable-image relation includes callee
evaluation, inert argument, actual receipt, provider-owned entry, body,
designated result consumer, requests/pending suffixes and invocation return.
All clauses are interpreted at the same environment/whole tuple.

The cited §5 explicitly says these are existing independent decorated
semantic propositions, **not new production solver atoms**. Its Call
certificate retains supplied profile, operation, observation and
correspondence premises beyond raw source incidence. This packet preserves
that distinction. Semantic formula satisfaction is consequently stronger
than merely obtaining a successful scalar/native solve. No change to the
meaning of the native success result is made or proved.

An important restriction was found while constructing this module. The
progress note's §4.1–4.2 `Role_0`/`Gen-Call-0` construction is explicitly for
its selected one-use unannotated formal-call pattern. It is not an original
role policy for every `App`. Emitting that selected seed unconditionally
would silently strengthen or misclassify the whole-source relation.

The final builder therefore always emits generic original raw Call incidence
and the complete decorated obligations. It emits the selected
`roleAndInitialCallOrigin` clause only when `singletonFormalCall` recognizes
an unannotated, source-registered ordinary formal Name with exactly one
resolved source use, applied to an ordinary rebound formal Name. The use
count is computed by `Source.nameCount`, including latent bodies and
defaults; it is not inferred from successful native comparisons. This
recognizer does not assert any later provider introduction, profile
membership, independent admission or accepted receiver event. Every other
App remains represented, with its full original semantic role/certificate
obligations.

The source progress note's §7 still identifies original profile completion
and independently admitted initial challenge construction as real suppliers.
This packet does not replace those suppliers with `True`, infer admission
from body success, or call a retained `PendingCallSupplier` a certificate.

## 6. Checking and actual boundaries

`Checking`/`Checkings` are an independent inductive finite proof grammar:

- identity and logical composition on the same complete endpoint tuple;
- authentic declaration-specific primitive checking;
- original record/union/intersection/top, same-value/computation, result,
  guarantee, congruence and original recursive-equation constructors, with
  all their finite child derivations;
- complete Function checking with a domain-mode proof and, for **every
  independently admitted checked challenge**, an observation-mode proof
  under that same challenge's extended environment.

`Kernel.functionShape` is only the original same-callable/interface incidence
condition. The Function constructor does not use it as an inclusion oracle:
it separately requires the domain proof and the universally quantified
observation derivations. An original checking primitive is tied to an
actual independently typed declaration; it cannot be instantiated as a
generic arbitrary extensional-inclusion leaf.

`Boundary` is separate. A proof-only check retains the original source
normalization tag and its finite checking proof. An actual conversion uses
one admitted original declaration at the actual source boundary. There is
**no** constructor composing two actual `Boundary` successes into one.
Thus the proof grammar does not manufacture a direct optional-record cast
from a two-step path. Logical inclusion composition is not concrete
adaptation composition.

This distinction is necessary for the original example
`{foo?: str} -> {} -> {foo?: int}`: two separately executed hiding/view
boundaries do not prove the one-boundary comparison. The adopted semantics,
not scalar record equality or a transitive structural model, must interpret
the boundary primitives.

## 7. Constructed continuation scopes and one original strategy

SG §3.1 Bind and §6 require the actual RHS Return/rebind or pending-response
suffix to enclose later statements and the final expression. The final builder
constructs that continuation; it does not place statement trees beside the
final expression and rely on a local atom to repair their missing scopes.
`statementRulesK`, `statementsRulesK`, `expressionRulesK` and `bindingsRulesK`
are mutually recursive, source-directed continuation builders. In particular,
a binding first records its actual initializer entry, checks the initializer,
then introduces its own actual Return/rebind, its one original Shared
reference, publication, all later bindings/statements and the final expression.
An initializer Block threads its internal scopes through the enclosing
binding's actual return and publication. Recursive members retain Internal
contexts and receive their simultaneous publication after all initializers.

The own RHS Return may precede Shared. SG §§3.3 and 5.1 require a Shared
witness to remain under the original dependencies of its owning initializer;
they do not authorize moving a response-dependent value before its own
response. The Shared reference encloses all *later* uses and challenges.
A lambda body introduces the same source structure under its original
invocation, receipt and entry event; those invocation-local Shared fields are
not hoisted into the outer initializer.

### 7.1 Explicit original anchor and publication data

`Environment` retains one root, one total `anchors` strategy, one immutable
`publications` graph, the original declaration, actual event path, resolved
name-to-publication map, ordered frames, initializer-entry snapshots and an
optional fixed replay history. These are explicit value/identity fields;
none contains a source judgment, generated formula, successful solver query
or a callback that supplies a whole local rule package.

An `AnchorKey` consists of the original declaration, the complete actual
event path and the generated source binder. Each event step contains the
source site and binder kind, actual occurrence and unchanged raw payload.
`Environment.extend` constructs the parent path from the **current actual
environment**, rather than trusting the candidate's supplied parent list.
Description frames do not alter that actual path or either fixed map.
`description_extension_preserves_anchor` proves their invariance;
`event_extension_uses_actual_parent_and_payload` exposes the exact path.
`distinct_actual_occurrences` and `distinct_challenge_payloads` distinguish
both ways that actual events can differ. Original source identity and
admission still need their concrete interpretation; assigning a convenient
arbitrary occurrence number is not a proof of native event correspondence.

`sharedE` reads `anchors (origin, actualPath, sourceBinder)` deterministically.
It is not an existential allocation under each description frame. Two
independent descriptions replay the same fixed initialization and therefore
read the same original strategy at the same actual event. Two actual
invocations have their own event paths. The total strategy is solution data
for the original dependent witness assignment; its value is not a hidden
source-typing derivation.

`initializerE` saves an `InitializerEntry` **before** internal RHS events:
its actual path, original names and fixed frame prefix. A `PublicationRecord`
retains this entry path/name/frame snapshot separately from the completed
returned captures and the full fixed history. The list of initializer entries
is the original suffix beginning at the owning entry, excluding entries
introduced later inside that initializer. `publicationCandidate` computes
this record from the actual source frames. `publicationValid` requires exact
equality with the one original catalog entry. Neither aliases nor fresh
descriptions can replace that catalog.

`restore` starts raw-source replay with the original entry names and entry
fixed-frame prefix, plus the current description frames. The complete fixed
history is retained separately for event lookup. Preloading the completed
history would duplicate inner Return/Shared frames when replay appended them;
using completed captures as entry names would make an inner publication
capture itself. Both defects were found in the first scoped repair, preserved
as rejected evidence, and repaired without weakening publication equality.
The entry snapshot is explicit; it is not guessed from equal event paths.
`initializer_entry_is_actual_scope`,
`publication_candidate_retains_original_scope`,
`restore_uses_entry_snapshot` and `restore_uses_captured_anchor` expose these
facts. `alias_keeps_publication_identity` proves that an alias copies the
identical original publication ID.

### 7.2 Fixed initialization and the full independent challenge domain

`executionE` distinguishes checking an open actual RHS event from replaying
an already published initializer. In an open source check it quantifies over
every originally admitted raw candidate. During publication replay it reads
the exact original event from the separate fixed history by generated source
binder and actual entry path, checks original admission for that unchanged
value and continues with it. It neither allocates a new return value nor
universally demands a different initialization for each new description.
Future invocation/operation-response binders reopen the original challenge
history; `future_invocation_reopens_history` states the invocation case.

Every ordinary `forallE`, including Function observation checking, still
passes the **raw candidate** to both `Kernel.admitted` and `extend`. The
`choose` helper is the identity, as
`admitted_candidate_payload_preserved` states. The rejected intermediate
normalization that replaced candidate data from the anchor map is absent.
Keeping a syntactic universal quantifier would not have repaired that
normalization: it would have erased independently admitted payloads before
checking them. The final audit includes two admitted Bool payloads with the
same event metadata and a constantly false anchor strategy, and proves that
the true challenge remains observable and prevents the false-only body from
satisfying the universal.

The admission relation takes the original environment, binder and candidate;
it receives no body, formula or pending query. Interpreting it as callee
acceptance, body safety, or the subset of events observed in the stored graph
would not instantiate SG's original independent challenge domain.

### 7.3 Joint clients

The finite client builder retains the following actual scope operations:

- `newUse` creates one fresh description frame, restores the referenced
  original publication for its raw source obligations, and aliases that same
  publication ID for the whole client suffix. The existing public theorem
  `new_use_checks_source_and_client_in_one_frame` exposes the two explicit
  restored/aliased environments; it does not assert that their entire records
  are identical. Both preserve the same fixed strategy and publication graph.
- `alias` copies the original publication ID and introduces no new description
  instance. `view` introduces a checking witness for that same instance.
- `run` keeps original event operands and a universally admitted invocation;
  body checking witnesses remain below the actual event.
- `join` passes one identical environment to both branches.
  `join_uses_one_environment` proves this directly.
- `bind` keeps the predecessor's actual Return or pending suffix. `constrain`
  places the independent client predicate `W` at that exact current assignment;
  `client_predicate_uses_one_environment` proves the conjunction property.

These checked construction results still require a concrete interpretation
of the original decorated carrier, the authentic source identities and the
local typed dependencies. The immutable graph must be the graph of the
original initialized/imported definitions, as the source publication equations
require; an arbitrary graph is not automatically authentic. The module does
not redefine `SourceProblem.sameScoped` as root equality or as a frame-prefix
lemma, and it supplies no strengthened native success predicate.

## 8. The remaining semantic supplier is explicit

`Kernel` has seven fields, all local. The exact full types are in the
originating census. Their required original meanings are:

| Field | Required independent meaning; prohibited shortcut |
| --- | --- |
| `atom` | The enumerated original constructor, incidence, binding, event and declaration clauses. It must not interpret a clause as the desired whole source judgment, `Generalize` success or `CompleteRelation`. Authentic primitive alternatives/guards and unanchored conservative alternatives remain in their original local relation. |
| `admitted` | Original typed binder/challenge/future admission at its existing telescope; never body safety, callee acceptance or pending-query success. |
| `primitiveCheck` | The local checking law of an actual independently typed declaration, not an arbitrary semantic inclusion oracle. |
| `structuralShape` | Original constructor incidence, selected fields/alternatives and exact whole child interfaces; all child checks are separately derived. |
| `functionShape` | Same actual callable, original checked/source domain and observation interfaces, and original challenge binder; not either required inclusion. |
| `boundaryTag` | Original source-normalization/boundary tag; never a tag guessed from a solved latent shape. |
| `conversion` | One actual registered boundary conversion with original code, effects, input/output relation and evidence; not a transitive path or an unselected adapter law. |

The generic reconstruction theorem cannot certify an arbitrary
interpretation of these fields. Their names and types do not magically
establish their original meanings. A malicious or incorrect interpretation
could hide a desired conclusion in a local predicate; such an interpretation
would fail the required source correspondence and is not supplied here.
This is why the packet does not label a parameterized theorem as the proved
whole-Yulang `SourceProblem.InferenceSoundness` instance.

The shortest remaining dependency order is now concrete:

1. Define the full original decorated assignment carrier and these local
   meanings from the already selected L1–L5 semantics. Start with exact
   source/port lookup, declaration identity, literal/Name/formation and
   original admission, then the original finite checking and direct
   conversion clauses. Full Call must retain its whole image, profile and
   complete receipt/operation/observation tuple. Genuine L4 introduction is
   not obtained just by a recursive-name registration.
2. Validate this candidate 13/11/3 rule inventory against that concrete
   independent source judgment. This is a local constructor-definition
   review/interpretation step; the global child induction and raw-source
   supplier are implemented. The raw metadata representation must be
   related to the authentic resolved source/component tables.
3. Define the actual original generated-constraint/solution relation using
   that interpretation and apply `generated_constraints_imply_source_judgment`.
   Only then is a concrete original inference root with an honestly complete
   `sameScoped` witness available.
4. Prove current native success realizes that semantic solution, retaining
   every original Call/selection/record/scope/generalization owner. This is
   the separate `NativeCorrespondence` bridge. Do not strengthen native
   success by definition to contain the source derivation.
5. Use the genuine source-to-core elaboration and observation theorem for
   the actual original core. Choosing `Core := Source` and identity
   elaboration merely to populate `SourceProblem` would not discharge it.

The concrete reusable item for the next author is therefore an implemented
raw-source induction, not another assumed universal implication. No new
global `LocalLaws` or `InferenceSoundness` hypothesis is needed to apply this
induction once the original local semantics is defined.

## 9. Native/source findings and non-conclusions

At the supplied baseline, `Contracts.lean` defines `SourceProblem` and its
`InferenceSoundness`, `NativeCorrespondence`, `Elaboration` and other roots.
They are propositions, not proved instances. `CoreComposition.native_success_elaborates`
requires the first three as hypotheses. No concrete whole-original
`SourceProblem` instance was found in the inspected Lean source tree.

The existing execution typing lane cannot simply be renamed to fill this
source field. Its paper Function type omits the original complete effects,
profile and admission interface, its operational `view`/lambda metadata is
less constrained, and its supported execution constructors do not establish
the original 13/11/3 source rule derivation. Its results remain useful for
their stated execution obligations; they do not supply this missing source
interpretation by projection.

The actual Rust source pipeline preserves useful *data*. In
`crates/yu-solver/src/candidate_call.rs`, `ApplySourceInput` retains owner,
callee/argument, source level, recipe, value/effect endpoints, checking
occurrence, cause, formal/local routes, native interface and source receiver
attachment. The file explicitly describes these as inputs to pending
complete Call construction, never certificates. `PendingCallSupplier`
includes the original whole registration, actual formal route, checking/seed
exposure, original Gen-Call-0, whole argument carrier, complete receiver/result/
future interfaces, and module admission/export correspondence.

`CandidateSourceCall.unresolved()` still returns the static `UNRESOLVED`
inventory. `shadow_apply.rs` explicitly retains application typing, complete
invocation image, whole argument compatibility, source typing/admission,
role/entry/protection, whole-tuple scope transport, generalization/fresh-use,
complete Function interpretation and related event suppliers **after
successful structural solving**. Retained source-owned fields can be inputs
to a future interpretation proof; their presence is not that proof.

`LocalSource` also differs from the canonical original grammar: it includes
source sugar and auxiliary forms, while its current case-pattern carrier is
limited to its explicit variants and its record carrier does not itself
represent all original spread forms. A correspondence must translate those
real forms and preserve original unsupported/refusal results. It must not
claim all original pattern coverage from the existence of a canonical Lean
constructor.

No current-native accepted-drain counterexample was established by this
author lane. The parent owns that separate investigation. The historical
OR-pattern oracle failure described in the research manuscript is not
presented as a new counterexample for this current native carrier.

## 10. Verification and freeze

Execution is isolated under
`/workspace/scratch/f98087c7ac1a/whole-soundness-route-r4/check` with owned
`TMPDIR`, `LEAN_NUM_THREADS=1`, `PYTHONDONTWRITEBYTECODE=1`, a 120-second bound,
`-j1`, and `-M1024`. Only `Std` and the two owned modules are imported. No
live sibling Lean module was copied into this snapshot. No root import,
toolchain, dependency, Lake configuration, native source or Git state was
changed by this lane.

The native toolchain is:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release
```

Default-sandbox installation detection failed before proof checking, despite
the native `lake --version` succeeding. The preserved errors were
`failed to locate application` and `could not detect configuration of Lake
installation`. An attempted `LEAN_SYSROOT` override did not fix detection.
The parent supplied the already authorized supported invocation using
`sandbox_permissions=require_escalated`; no installation/configuration
change was made. These environment failures are not theorem failures and
are not omitted from the handoff.

All focused check outputs are retained as `checkNN.log` in the owned scratch
directory. Material ordinary failures were preserved: the first raw syntax
check found an ambiguous constructor-like pattern variable and doc-comment
placement; the first reconstruction check required a common `sizeOf` measure
for the mutual proof; a later source metadata check required explicit
structure-field syntax; the first census script used one unsupported
pretty-print option and untyped numeric counters. These were repaired from
their actual diagnostics. A successful intermediate check's two unused-simp
warnings were removed. No `sorry`, project axiom, native-decision axiom,
unchecked kernel option or admitted proof remains in the new modules.
The first check predated file redirection; its complete diagnostic remains in
the tool transcript and `check01.log` is explicitly labeled a diagnostic
excerpt. Later failed check logs are complete stdout/stderr captures.

The parent extended the initial 20-check cap to 21 solely for the concrete
binding-annotation repair: one final Generation compile and one complete
originating census. The old Generation hash
`630936ddef835eda6fa97310539bd5106bbf017bc4202516f86ea2e054b40a74`
and `check19-originating-census.log` belong to the superseded first freeze.
Those annotation-only bytes also failed the later independent scope review.
Their Generation hash was
`b7f5a1858d9615cdd099099889ab31ddd73bf47f3d085311996297000c420a5d`.

The parent then authorized eight focused checks through cap 29 for the actual
continuation, anchor and challenge-domain repairs, plus a 900-second wall
extension to finish the concrete initializer-entry repair. Check 23 preserved
ordinary parser/simplifier failures; check 26 preserved a mutual-recursion
measure failure. Checks 27–28 compiled the scoped modules, and check 29
successfully enumerated 2,372 declarations/912 theorem constants. That frozen
Generation hash
`fac3f6b47b5b933d4450daa67d145786725ce0c1f64223f02d75507b91c6dee0`
was then rejected for the concrete replay-prefix/name duplication in §7.1.
Its successful kernel check and census are retained as superseded; they did
not establish the desired source meaning.

The parent authorized up to four further focused checks, cap 33, specifically
for the entry frame/name snapshot repair and fresh census. Check 30 compiles
that repair with empty diagnostics. Check 31 failed on a newline before an
audit-only method invocation; its dependent regression proof consequently
contained elaborator-recovery `sorryAx`. That failed output and audit source
are preserved and are not accepted evidence. Check 32 repairs that audit
expression and passes with no diagnostics. The audit explicitly rejects
unapproved axioms in all three regression proofs as well as every originating
module declaration. No code changed between successful Generation check 30
and successful final census 32. This lane used 32 of the authorized 33
focused checks; the unused slot was not spent on optional verification.

The final complete census contains **2,394 declarations and 916 theorem
constants**: Syntax 1,577/561, Generation 817/355. It prints every originating
constant's full type and axiom set, including private and generated names.
The 5,046,372-byte log is `check32-originating-census.log`, SHA256
`8c28b1588b8bec3e67efd556eccf8dff72bec931996bce9bfe20b0d5b08f3d79`.
The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
There are no originating project axioms or `sorryAx` dependencies in the
accepted output. `OriginalSourceAudit.lean` has SHA256
`1be0ed04ed24e6020a50ab95fd37366b10a34e835df5c0928f73ad5aac63ec41`.

The focused source-path evaluation places final Name 20 under binding 11's
Return/rebind and Shared reference, then its own published-instance frame.
The lambda fixture retains that binding under the actual invocation/receipt
and entry scope. The three kernel-checked audit proofs are
`original_true_challenge_not_erased`,
`outer_record_is_exact_source_construction` and
`replay_inner_publication_is_exactly_original`; the last two use an outer
binding 30 whose initializer is a Block with inner binding 11 and preserve
exact publication-record equality under a fresh description frame.

The audit script enumerates **all originating declarations**, not just a
hand-selected public list, using the imported module indexes. It includes
private and generated constants, prints their complete types and full axiom
sets, rejects originating project axioms, and checks the actual application
roots are theorem declarations. The accepted axiom whitelist is the existing
`propext`, `Classical.choice`, `Quot.sound`; an empty/allowed axiom list is not
a proof of the semantic meaning of the `Kernel` hypotheses.

Final check results, complete census paths, counts, hashes and the exact
frozen file hashes are recorded in the paired inbox handoff
`tasks/agent-loop/inbox/20261026-whole-soundness-route-r4.md`. This author
packet is ready for fresh source/meaning review after that freeze. It is not
independent acceptance of itself and does not close the full native goal.

## Appendix: complete source-dependent computation crosswalk

The following is the complete construction inventory, including private
helpers. The raw source-dependent functions are total transparent definitions and
consult no solver, semantic solution or success predicate. Environment
interpretation operations additionally read the fixed assignment maps and
history described in §7. Equality for arbitrary semantic `Value` makes the
publication lookup/record operations noncomputable classical definitions;
this does not turn the raw syntax builder into a solver or assert an
effective native implementation of those semantic operations.

| Computation | Input and exact construction |
| --- | --- |
| `Formal.entry` | Select Value or retained Computation from the retained outer source annotation bit. `sourceFormalRole` is the independent consistency clause, so the Boolean is not treated as self-authenticating metadata. |
| `Source.site` | Return the original occurrence ID; ordered empty/list containers have no standalone source occurrence. `someExpression` retains its child's occurrence. |
| `Source.binders` | Collect declared resolved binder IDs through the actual pattern/statement containers. OR uses the supplied original result IDs of the merge triples, not intersection of unrelated resolved IDs. |
| `Source.bindingRecords` | Collect each binder's own owner occurrence and kind; definition publication records retain their original definition site. Recursive component marking is done by `sourceRules` at the actual group. |
| `Source.roots` | Collect the original immediate/ordered child references for formation; case/catch arm lists expose body result sites; field and binding containers expose their original field/binding sites. |
| `Source.nameCount` | Count resolved source uses recursively through every expression, pattern, default, continuation pattern, statement and latent body. Binding declarations themselves are not uses. This is used only for the selected singleton Call-seed recognizer. |
| `bindNames` | Prepend explicit source-owned binding records to the original context. It does not instantiate a scheme or evaluate an initializer. |
| `lookupBinding` | Find the first record for the resolved identity in that context. The independent resolved-binding clause must validate authenticity; a failed lookup is not silently a valid Name derivation. |
| private `patternContext` | Add the pattern's original binder records while retaining an already registered occurrence of the same resolved identity, notably the source formal's own pattern. It does not compare source spellings or create OR merges. |
| private `statementContext` | Extend with the actual statement's declared binding records, retaining their owners. |
| `singletonFormalCall` | Inspect two raw Name expressions and original context records; require absence of the selected written annotations, ordinary formal entries and the callee's computed one-use flag. No endpoint shape or query result is examined. |
| `atom`; private `premises`, `node` | Package the fixed local-relation names and the original site/context/operand lists. They contain no semantic tests. |
| `RuleForest.one`, `RuleForest.two`, `RuleForest.three` | Package the actual ordered child programs. They make no claim that any child is derivable. |
| private `endpoint`, `check` | Construct explicit original port references and finite-check goals. Written target, synthesis, returned callee, descriptor, callable image, body consumer, branch join and reference content are distinct ports. |
| private `annotated` | If a written annotation exists, retain its original ID, final-formation clause and actual direct synthesis-to-target boundary around the original child program. No annotation is inferred from a type. |
| `bindingsRulesK` binding-annotation branch | Preserve a second actual written boundary: already completed `initializer.finalRoot` to the distinct `binding.writtenTarget`. The publication clause and context entry keep the external binding-site root. This branch deliberately does not reuse `annotated` on the initializer's synthesis port. |
| private `suffix` | Retain the source predecessor as the owner of the original return/pending-response telescope. Admission is interpreted independently by `Kernel.admitted`. |
| `sourceRules` | Exhaustive structural recursion on all canonical raw constructors; the full 13/11/3 equations and the ordered containers are in §§3–4. It builds contexts, source-only singleton metadata, original local clauses and scoped child programs; it accepts no prebuilt rule package. |
| `clientRules` | Exhaustive structural recursion on six operational client instructions, termination and original-scope `W` placement. It recursively invokes `sourceRules` on a raw referenced definition. |
| `statementRulesK`, `statementsRulesK` | Construct the whole remaining statement/final-expression continuation inside each earlier binding's actual RHS and Shared scopes. Recursive publication occurs simultaneously after all member initializers. |
| `expressionRulesK`, `bindingsRulesK` | Thread initializer-Block scopes through the enclosing return/publication; place the owning initializer entry marker, each direct binding annotation, actual return, original Shared reference and whole suffix in source order. |
| `Binder.isEvent`, `Binder.isFixed` | Classify the explicit original binder kinds. Description/view/proof frames are not runtime event identity; fixed frames include the actual events and original Shared fields. |
| `ActualEvent.path`, `Frame.exitPath` | Construct a source-binder step with its unchanged payload and occurrence. A frame exit uses its recorded actual entry path, not an independently supplied candidate parent list. |
| `Environment.anchorKey`, `anchorValue` | Read the single original strategy by declaration, actual path and generated source binder. No new witness is allocated for a fresh description. |
| `Environment.choose` | Identity on the complete raw candidate. It is not used to normalize the original admitted challenge domain. |
| `Environment.extend` | Append the unchanged candidate, construct the actual event path from the current environment and generated binder, preserve root/maps/old frames and reopen future invocation/operation-response history. |
| `Environment.enterInitializer` | Save the actual source entry path, original names and fixed frame prefix before the initializer's own internal events. |
| `Environment.prefixAtShared` | Select the actual prefix ending at the owning Shared frame, including the RHS return on which it depends. |
| `Environment.publicationCandidate`, `publicationValid` | Construct the exact entry snapshot, completed captures, completed fixed history and original initializer-marker suffix; require equality with the one fixed original catalog. No derivation or success field occurs in the record. |
| `Environment.publish`, `publicationName` | Extend or resolve the explicit original binding-to-publication map from those source-constructed identities. |
| `Environment.restore`, `atPublication` | Read the same catalog record; replay from its entry names/frame prefix/path while retaining completed actual history separately. Preserve current description frames and both fixed maps. |
| `Environment.aliasPublication` | Copy the identical publication ID without a fresh instance, strategy or initialization. |
| `Environment.executionValue` | Look up the recorded actual source event by generated binder and original entry path during fixed initialization replay. It is not the domain of later universal challenges. |
| `compilePremises`, `compile`, `compileForest` | Translate a fixed original rule into conjunction, choice into union, and each original binder into the same binder. Local premise operands are copied unchanged. |
| `Build`, `BuildJoint` | Compose the source/client data construction with the formula compiler. No derivation, model or success input is available. |
| `Satisfies` | Interpret the generated logical constructors in one fixed environment using the independent `Local` checking/boundary judgments and original admission. It does not call `SourceJudgment` or `JointJudgment`. |
| `SourceJudgment`, `JointJudgment` | Index the independent inductive `Judgment` by the canonically constructed source/client rule syntax. These definitions do not call `Build`, `BuildJoint` or `Satisfies`. |

The generic rule compiler and reconstruction can also be used on a supplied
`RuleTree`; that lower-level API is not the source theorem's input. The
raw-source entry points and the `newUse` construction explicitly compute that
tree. The remaining concrete original-meaning obligation has not been
renamed into a caller-supplied tree or a global reconstruction hypothesis.
