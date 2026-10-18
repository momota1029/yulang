# R38: ordinary Call result introduction and its native port

Status: frozen candidate formation rule and bounded source/native audit;
independent review NOT_RUN. No adopted source rule, reviewed theorem,
source-qualified counterexample, implementation authority or parent closure.

Author: `/root/r38_call_result_proof`, constructive leaf; no descendants.
Assignment/handoff `R38-PROOF-RESULT-OWNER`, revision 1. Requested Sol/high;
observed model/effort UNKNOWN/UNKNOWN. Session:
`current-conversation-2026-10-18`; opaque runtime session ID UNKNOWN.
Luna's direct assignment and acknowledged contract revision 2 govern this
packet. All results below are producer evidence.

## 1. Parent application and result

Original parent: the full Yulang inference/executor theorem and original
Simple-sub A/B obligations, at R38 contract's **Original outcome and success
evidence**, retaining the source domain and quantifiers detailed in R36 §1.
This includes recursive worlds, every original provider/assignment/component,
context, occurrence, event, guard, continuation, interaction, future and
history; arbitrary well-scoped client W; two independent incoming frames and
their aliases; complete Call/effects; F1 and independently quantified FK1;
N-Transport; soundness, required principality and termination. R30 `j0/a0`
is unaffected. No claim is restricted to this specimen.

Parent conditions closed: **0 -> 0**. The actual first missing premise remains
the ordinary Call owner's introduction of its output ValueDescription R,
with validating component, original scope and complete ordered dependencies,
and its typed correspondence to the native result field. The independently
open C/D CopyScope, publication, both-frame lift, foreign-continuation and
production obligations remain open.

The adopted IF constructor outputs a complete result **interface slot**,
including actual result/provider/world and future interfaces. Generalize §3.3
does not turn that slot into an ordinary inference **declaration**. Actual
native allocation supplies a Value row and a retained occurrence/recipe path,
but no logical source declaration telescope. Section 4 gives the contract's
permitted alternative: one explicit proposal-only formation rule. It changes
the method from reconstructing scope from native endpoints to declaring and
retaining scope at source formation. Its adequacy and actual application to q
are unproved; this is not a renamed conditional parent theorem.

## 2. Exact occurrence and existing-rule audit

The original specimen, reused from R36 without substituting a smaller fixture:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Here q is **only** `loop y` inside helper; t=`loop x` in direct is another
Apply. f=loop and g=helper retain distinct validating registrations K_f/K_g.
The three helper applications in this source are not evidence of two observed
FreshUse maps. i0/i1 below denote the original independent frames. Helper
publication is under its enclosing outer invocation h. Native numeric IDs,
levels and a concrete runtime trace for this specimen were not measured.

| Exact supplier | Existing conclusion used | First missing inference |
| --- | --- | --- |
| Call source definition §§3–4, adopted IF construction §§3–5 | Actual callee, inert whole carrier, callee-return/current C1, dependent receiver, whole Call return/current C2, future and every original arm/reference; original symbolic result/check origins retained | No `Desc(K_g,q,ValueDescription,sigma_R,Delta_R)` rule instance |
| IF construction §3.1 | Original primitive exposes ordered `P_alpha,T_alpha`, with dependent field projections and genuine licenses | No concrete telescope can be recovered from a field name or opaque predicate alone |
| Generalize §§3.1,3.3–4 | Parameter y introduces B at its Parameter scope before g's challenge; a body declaration may occur inside an invocation **if its own rule introduces it there**; Build retains genuine owner records | The generic Call inventory is not an independently specified inference introduction for R |
| Generalize §3.3 event rules | Actual return/provider/world/receipt/response fields are EventField/OneShot; description proofs retain ViewLogic/EventProof scopes | Runtime result is not an ordinary Desc; a logical proof is not an executed witness |
| Result synthesis A §§1,3–4 | Preserve an already known computation interface; `Result(Value(A))=Comp(empty,A)`, `Result(Computation(E,A))=Comp(E,A)` | Neither rule supplies ordinary Call R's owner/sigma/Delta, nor equates body and invocation ports |
| `PendingCallConstruction::suppliers`, `candidate_call.rs:397` | Requests OriginalGenCall0, whole carrier and receiver/complete-result/future suppliers; formal/module routes add their own requests | A request enumerator emits no missing source derivation or typed telescope |

This is bounded underdetermination of the inspected governing inventory,
not a metatheorem that no adopted document anywhere could supply the record.
A locator to an adopted actual q introduction with all fields is a decisive
falsifier. IF's own independent original operator-typing/dispatch/C0 inputs
cannot be obtained by eliminating its output slot. The original complete
local laws L1–L5 remain required at their actual owners.

### 2.1 Output distinctions required by synthesis A and complete Call

Use separate names for the body's known synthesized interface I_body,
producer native return, designated consumer, receiver invocation interface
I_inv and the complete callee-Bind-then-receiver interface I_q. For whichever
original source derivation forms them, write an output computation interface
as `Comp(E,A)` only at its actually selected computation port. A denotes its
ValueDescription projection, not the computation itself or its provider.

For a computation-forwarding body, synthesis policy A preserves its known `Comp(E,A)` at the
body Result boundary; no new pure computation-data layer is inserted. Complete
entry, native return and designated consumption still determine I_inv.
The complete Call additionally includes callee evaluation and its Bind suffix.
These facts give no blanket equation I_body=I_inv=I_q. A value whose eventual
description is latent remains data until an actual source consumer acts.
An empty solved effect does not choose a different port or entry role.

Consequently, neither the body result nor actual returned provider can be
silently selected as R. The requested R is the output **ValueDescription
coordinate of the complete selected Call interface**, with all its original
effect, return, provider/world and future coordinates retained beside it.
Whether that coordinate has an ordinary declaration, and where, is exactly
the missing introduction.

## 3. Actual source allocation -> native demand -> observation

The following is a static derivation from inspected constructor code, not a
test execution or proof that the complete semantic Call supplier exists.

1. `ConstraintBatch::emit_candidate_source`, `candidate_source.rs:826`, checks
   actual HIR/source ownership. Its initial expression pass at :863 allocates
   `positions[index]` using `candidate_component(expr.occurrence)`.
   `candidate_component`, `shadow_apply.rs:1481`, creates separate Value and
   Effect components and records occurrence-to-position association.
2. The Apply case at `candidate_source.rs:1317–1361` retains q's callee and
   argument source indices, their endpoint/effect positions, checking
   occurrence/cause, recipe index, `result:pos.value` and
   `application_effect:pos.effect`. Its `CandidateRelation::Apply` contains
   those same positions; `source_input` links the recipe back to this input.
   A Local callee route authenticates the actual active name, not a new
   polymorphic publication. Neither component position is a logical sigma.
3. `InferenceSession::admit_candidate_fact`, `shadow_apply.rs:1763`, compares
   the recipe/source-input occurrence and every retained endpoint/effect/result
   position. With source input present it separately creates a fresh invocation
   effect row. The result term is obtained by
   `candidate_endpoint(Component(result),Negative)`; that method at :1746
   maps the component position through `live_components[position].ordinal`
   and obtains its live Value term.
4. The negative Function demand is made in this exact order:

   ```text
   (argument, argument_effect, invocation_effect, result)
   ```

   `NativeInterface` at `candidate_call.rs:135` stores that demand and result,
   with callee effect and application effect retained separately. The callee
   is admitted against the demand; this is constraint generation/admission,
   not prior satisfiability of the demand. Subsequent Simple-sub accumulation,
   propagation, levels, extrusion, qualifying intrusion and generalization
   remain necessary and unchanged.
5. `candidate_call::observe_inner`, :478–571, authenticates HIR Apply shape,
   operands, occurrence/cause and owned scopes, then checks the four demand
   fields and native kind/polarity. `native_result()` at :352 returns precisely
   that retained result. `observe_scoped` adds actual local-route authentication
   through `authenticate_scoped_apply`. These checks are local native
   authentication; they do not retain a Desc or establish a semantic type map.

| Port | Retained native relation | Source typing status |
| --- | --- | --- |
| R | `ApplySourceInput.result = CandidateRelation::Apply.result`; admission maps this component to `NativeInterface.result`; demand fourth field equals that term | Value/Negative native sort supplied; source ValueDescription declaration and its typed interpretation missing |
| Invocation effect | Fresh effect row; demand third field, `NativeInterface.invocation_effect` | Distinct effect port; not R, full application effect or body-result identity |
| Actual result/provider/current world | IF return slot `(actual_result,current_C2)` and output-dependent future fields | No direct provider/world projection exists in `NativeInterface.result`; row equality cannot supply one |
| Actual receiver | IF dependent `ExecuteCallable(actual_f,arg,current_C1)` slot | Demand/checking view does not replace this receiver or actual role/entry |

`DirectionalIntroduction` is constructed through `formal_name` and
`omitted_formals` in :1838–1856. q's Local f route does not supply this formal
route. Its absence is no language-wide absence-of-protection theorem, and
its presence elsewhere would not supply R's Desc.

No representative stability, final-row identity, complete source typing,
native FreshUse square or two-frame correspondence is inferred from this
allocation path. R37's temporal and canonical-map-hit blockers remain intact.

## 4. Single candidate rule: Call-Result-Desc-Formation

**Proposal only.** This rule explicitly chooses a body source-description
formation cursor. It is not asserted to be the existing rule, semantically
conservative, principal, or source-forced. Its adoption is outside R38.

Inputs are the actual resolved q and its two source children; its authentic
helper definition registration C_g; the original source binder tree T and
the typed source-rule input cursor; authentic complete Call declaration Q_q,
with original local law/schema and all its arm interfaces; and child static
interface constructions. Original source/checking origins, lexical/checking
uses, exposure, carrier hole, dispatch and licenses remain inputs, not outputs
inferred from shape. No successful typing or solved endpoint is a premise.

Let `Gamma_q=(d1:S1,...,dn:Sn)` be the **entire original ordered typed input
context** at q's body source-description cursor after forming its two child
interface schemas, and before opening this q's callee-execution, receipt,
response or returned-value binders. The child schemas are retained with their
internal telescopes bound, not flattened into Gamma_q. Gamma_q includes every
inherited declaration, capture, actual enclosing event and earlier proof
dependency; no item is deleted because it looks unused. Its types are exactly
`S_j(d1,...,d_(j-1))` with the original binders and record classes. In particular:

```text
original outer/definition prefix
  -> helper description prefix, including Parameter B at its earlier scope
  -> actual enclosing helper entry/body prefix, if present in T
  -> static callee/whole-inert-argument interface schemas
  -> proposed fresh R
  -> q-local callee/result-rebind/receiver/return/future and arm telescopes
```

These arrows denote inclusion order, not exchanges of original binders.
The inherited prefix contains h and any g challenge/receipt only where the
original source-rule input actually contains them. This proposal does not
move R out of that prefix to B's pre-challenge scope. It inserts R before
q's own event telescopes. Thus a later q-return witness cannot be a free
dependency of R. If that placement is wrong for ordinary Call, the proposal
fails; moving it is a different proposal requiring Luna.

The retained operand vector is explicitly **all** of Gamma_q, in that order.
Hence this proposed header uses `Delta_R:=Gamma_q`, with the identity typed
inclusion into sigma_q, rather than guessing the minimal free support of an
already existing declaration. This is a deliberate full-context
input convention of the proposal; it is not evidence that the actual R has
that dependency telescope. Infinite worlds/futures are retained as typed
families at their original binders; finite graph references are not unfolded.

```text
q : resolved Apply(callee_q,argument_q) in authentic C_g
T; sigma_q has complete typed input telescope Gamma_q
Gamma_q |- child interfaces and all complete Q_q arm schemas formed
R fresh, ordinary ValueDescription variable; rho_R=(C_g,q,result-description)
---------------------------------------------------------------- proposal only
at sigma_q, append R : ValueDescription with ordered inputs Delta_R=Gamma_q
emit Desc(C_g,rho_R,ValueDescription,sigma_q,Delta_R)
emit Description(C_g,rho_R) for the selected Call output-value endpoint
generate Q_q's entire original local rule program with that endpoint R
retain the complete selected output interface, not merely R
```

Here rho_R is a distinct source declaration/port address at occurrence q;
the word `result-description` is a constructor coordinate, not an identifier
spelling used to infer ownership. No other rule in this packet introduces R.
The output-effect description has its own existing source scope; this rule
does not classify or generalize it. The proposal adds no check-first branch,
source execution, search, new consumer or successful-Q atom.

To instantiate the last line, the original local schema must expose its
typed output-description parameter and all its original clauses. A bare
`FrameCall.return` pair does not meet that input. For symbolic generation,
the new declaration and all old constraints remain open; they are not solved
at generation. Any independent typing/checking/conversion law needed to use
the schema still belongs to L1–L5. The proposal therefore specifies the
missing source-owner output without purporting to discharge those laws.

### 4.1 Whole dependent telescope and alternatives

The proposal preserves the original eight IF frame fields, each with its
entire internally ordered telescope:

```text
Gamma_q ; R
  [ callee schema ; whole carrier schema ; callee-return(actual_f,C1)
    ; receiver(actual_f,carrier,C1) ; complete-return(actual_result,C2)
    ; future(actual_result,C2) ; every original arm ; source/origin fields ]
```

The brackets indicate the existing dependent frame/schema from IF §4,
not a flat conjunction of independently chosen witnesses. Original source
origins can be available earlier even where their frame projection is printed
last. Each genuine field type is retained from Q_q, not supplied by these
schematic labels. Gamma_q and those field types have **not** been concretely
instantiated for q by any inspected source owner. That missing instantiation
is recorded, rather than calling this display the actual complete telescope.

For a callee-pending branch the receiver and return/future remain suspended
suffixes under the original response/current-world binder. For receiver
pending, retain the remaining entry/rebind/body/consumer/return suffix and
never replay receipt. For Return, retain the same actual returned provider,
current world and its dependent future interface. For W/Z and opaque arms,
retain their own whole tuple, guard, actual output provider, independent
admission/license and future fields in that arm's original scope. An
unanchored Z remains available without source execution. None is replaced
by a structural provider or by an R equality.

This is a precise preservation requirement on the candidate rule program;
its semantic validity is unproved. In particular, a full arm with a genuinely
later dependency needed freely in R would refute the proposed placement.
Synthesis A is fixed before any endpoint substitution: a known computation
interface remains a computation interface; R is its output-value coordinate,
not a new result-interpretation parameter or implicit inert layer.

### 4.2 Candidate typed field correspondence and falsifier

If the source owner supplies that formation output, a separate retained
translation must produce the following typed square, without changing source
scopes or recovering them from native levels:

```text
Desc(C_g,rho_R,ValueDescription,sigma_q,Delta_R)
      -- source construction at exact q --> ApplySourceInput.result position
          -- component/live-row map, Negative --> NativeInterface.result
                                                 = demand.Function.result
```

The top edge must carry the declaration reference, source sort and entire
typed context inclusion. The lower edges currently establish only native
identity/kind/polarity as §3 explains. A semantic/native interpretation of
every dependent field is missing. The same selected port must commute with
the complete effect/provider/event/residual tuple, not just the row.

**Exact falsifier:** exhibit an actual q source derivation in the original
domain with a required free dependency d of R whose introduction is below
sigma_q (for example an output-provider-dependent descriptor coordinate
introduced only at q's return), or with one required inherited dependency
missing/reordered in Gamma_q. Then the proposed declaration cannot type at
that cursor. A source derivation requiring a pre-g-challenge R also defeats
this chosen body-cursor introduction. These are falsifier specifications;
this packet constructs no such source witness.

Additional concrete rejection controls are: t's result substituted for q's;
demand's invocation-effect field substituted for its result field; actual
returned provider substituted for its descriptor; extra pure wrapping of a
known computation body; missing W/Z or pending-suffix field; provider/future
or witness lineage collapsed; or required equality only after solving.
Native checks alone cannot rule out the logical-scope falsifier.

## 5. Application back to the original parent and mutual TODOs

The unchanged parent's required R remains unauthenticated. If the proposed
header were independently justified at q, R would acquire a precise owner,
sort, insertion cursor and retained dependency vector; the next required
edge would be its actual typed native translation. Even then R36's
parent-context D_hat:=R definition could be formed only at that supplied
scope; actual native D would still need its own CopyScope. No native copy
receives its parent's dependencies by this note.

For the two original incoming frames, any eventual Generalize action must
act on every genuine retained dependency at its original scope. Aliases use
their existing instance; Shared/OneShot fields remain shared, and the active
f relation is not relabeled `Internal(K_g,f)` or an Established external
scheme. The full fixed/retain walk is required before R can be called fixed
or eligible. No joint i0/i1 strategy, arbitrary-W fiber equality, F1 inventory
or FK1 foreign-continuation transport follows from one Call-local header.

The next in-envelope work has reached its permitted stop condition: existing
rules audited; one explicit candidate formation rule and falsifiers supplied.
The next authority seam belongs to Luna. No alternative rule or wider owner
domain is silently tried after freeze.

| Stable TODO / owner for Luna intake | First missing evidence and required inputs | Proposed output / exact discriminator |
| --- | --- | --- |
| R38-SOURCE-INTRO / ordinary Call source-rule owner | At exact q, original T, authentic complete Q_q, child schemas and actual C_g input context | Existing adopted introduction with complete ordered field types, or adjudication of this one proposal; exhibit inaccessible/missing dependency to reject it |
| R38-TYPED-RESULT-MAP / source-to-native bridge owner | Frozen source declaration plus actual Apply input/recipe/live-row path | Typed declaration/context reference for `ApplySourceInput.result` and `NativeInterface.result`; reject wrong q, wrong Function field or provider/descriptor substitution |
| R38-COPY-PUBLICATION / Apply/extrusion and Generalize owners | Actual R record, both C/D copy contexts and original active K_f/K_g registrations | Separate CopyScope and authentic retain/fix actions, followed by whole signed/effect/residual commutation; inaccessible parent dependency or fixed-copy/eligible-parent mismatch falsifies it |

The minimal possible future implementation TODO is **retention only**, after
Luna establishes the source header: attach its typed declaration/context
reference when `emit_candidate_source` creates ApplySourceInput, carry that
same reference through `admit_candidate_fact` to NativeInterface, and have
observation reject mismatched occurrence/result field. This is provisional,
not an authorization or a proposed production patch. Its falsifier is any
native R accepted without the exact source declaration and ordered context
inclusion. No code-only certificate may manufacture the missing source rule.

Prior work reused: IF's adopted complete frame and supplier construction;
Generalize's reviewed scoped rule program and record partition **under L1–L5**;
synthesis A's selected port equations; R36's exact specimen and its distinction
between source definitions and native copies. R36's alias proof is not
repeated or counted as R introduction. R37's frozen blockers are preserved,
not used as source typing. Solved shapes, HIR region labels, numeric levels,
Value SCC membership, pending-supplier names and tests of assumed transitions
are rejected as replacements for the missing owner output. No withdrawn
Simple-sub bypass is restored.

## 6. Frozen dependencies, authors, checks and cessation

Baseline supplied by Luna: `887eed4370278cd9e789fb2b9b10ff58369da540`.
No Git command was run. Contract revision 2 is acknowledged and byte-verified;
revision 1 remains frozen history. Working-byte SHA-256 inputs inspected:

| Input | SHA-256 | Authorship/provenance |
| --- | --- | --- |
| `tasks/agent-loop/sprints/ordinary-call-result-owner-20261018-r38-rev2.md` | `f119bf4f031ab8b28fd060921723ddb235bf208ff3b48a87bc169aa1b7fa0421` | Luna primary |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Individual code authors UNKNOWN |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` | Individual code authors UNKNOWN |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Individual code authors UNKNOWN; required actual source producer |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | Primary selection; independent reviews recorded in source |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | Original producer identity UNKNOWN; selected reviewed body |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Researcher; independent repaired theorem reviews recorded in source |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | Primary selection with read-only architect input |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` | Primary selection; recorded independent reviews |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` | Primary/user-selected A; recorded independent reviews |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | User decision; recorded transcription/scope reviews |
| `notes/theory/2026-10-18-apply-scope-publication-r36.md` | `43edea46d93a8b7eac6a68e6544aa34cc36797c59e232fd31599d8eec15ef5a9` | `/root/r36_proof`; unreviewed candidate, not source authority |
| `notes/progress/2026-10-18-r37-rev3-review-closeout.md` | `5c1aa3ea9f653a73d5f7466f61f9cbc32bc641fcc56ac5eeed6ff3da201f1d44` | Primary closeout with named independent review results |

The native audit uses these inspected baseline inputs. Other lanes' later
test-only changes are not inputs or results certified here. Authority hashes
and the unchanged source producer are rechecked at freeze; moving native file
hashes are reported in the inbox without silently replacing the baseline pins.

Checks: bounded text/section reads, static producer reasoning, dependency
SHA-256 and artifact formatting inspection only. No proof checker, test,
build, Cargo, numerical probe, source acceptance measurement or runtime trace.
Coverage omitted: concrete original q rule/telescope, actual trace IDs,
source-lawful countermodel, all L1–L5 validity, typed native translation,
C/D copy/publication and both-frame/foreign-continuation lift.

Resource grant: 1500 seconds, fully charged; worker requests no extension or
refund. Observed exact runtime/effort consumption UNKNOWN. Astra0, probes0,
heavy verification0, descendants0. Only new/written paths are this artifact
and `tasks/agent-loop/inbox/20261018-call-result-owner-r38.md`; scratch paths:
none. No central/shared records, production/compiler/tests/expectations,
semantics, rules, config, manifests, lockfiles, questions or foreign worker
outputs were edited. No Git, nested CLI or user/external contact.

Freeze receipt: this revision is immutable when its hash is submitted in the
assigned inbox; both leased paths stop writing after that submission. No
descendant or unresolved generated-output lease exists. Assignment terminates
at candidate-rule handoff; fresh review and authority adjudication belong to
Luna. This producer is ineligible to certify the combined R38 result.
