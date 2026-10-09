# Annotated apply attack: selected nested-source expiry and exact request removal

Date: 2026-10-09
Assignment baseline: `c4cf02dd3307e6051b6d23b8af17c6f0633c09f0`
Status: independently reviewed bounded source lifetime and request-image theorems;
incomplete annotated-source attack
Method: source constructor expansion, structural inversion, and complete request-image calculation
Exclusive write lease: this file only
Semantic selection / implementation / aggregate gate closure: none
Review: independent mathematical and specification reviews passed the exact
bounded scope; see the [review record](../progress/2026-10-09-source-semantic-attacks-review.md).

## 1. Result and precise failure of the full objective

The exact source target is `my apply (f: _ -> [io] _) x = f x`.
This note supplies three substantive results, rather than another supplied
`Lawful`/`Frame` composition:

1. A conservative **header macro** into two existing Lambda constructors,
   with original annotation, binder, Name, Call and capture incidences retained.
   The macro is an explicitly unselected missing source constructor. It does
   not complete the semantic annotation rule.
2. On the **selected original unannotated nested-block source**, the receiver
   which receives `f` cannot be live at a later execution of the body Call.
   This is a genuine source lifetime theorem, including pending entry and raw
   resumes. Its core proof also applies to the candidate annotated expansion.
   It does not erase the captured annotation/profile or static seeds.
3. An actual shallow-handler image calculation removes one eligible request
   prefix and preserves its entire raw suffix at the correct outer state.
   The corresponding two-request calculation leaves a same-family request
   in the output. These derive local removal and its frame from the handler
   equations; they do not assume a `Lawful` judgment.

A separate head theorem shows exactly why exporting a completed
Function-headed annotation target would make the body Call cease to be an
inferred-variable exposure. It leaves the earlier annotation exposure open.

The assigned full annotated-formal objective is **not achieved**. No authentic
complete normalized target for this written annotation, no exhaustive
annotation seed-introduction rule, and no plain-`[io]` static protection-release
rule have been constructed. Consequently the operational examples below are
core-source witnesses and applications of existing handler laws, **not proved
accepted annotated Yulang programs**. They must not be reported as an actual
accepted-source counterexample or as C5/C6 closure. The dynamic theorem does
eliminate a real premise: a later callback request cannot obtain live capture
authority from the original, returned `f` receiver in this expansion.

## 2. Governing original meanings

Read the following original sections, rather than adopting the production
Call proposal or the conditional annotation draft as semantic rules:

| Source | Meaning used |
| --- | --- |
| Inferred Function call views §§1.1, 4–5 and its integrated a2 answer | Written annotations, public schemes and internal views differ; the annotated formal permits only its corresponding `io` contribution to be removed; permission does not execute removal. |
| Directional protection addendum §§2–4 | Dir-Protect acts at an already protected inferred variable's original upper use; it never back-protects the existing provider lower occurrence. |
| Integrated annotation-boundary d1 decisions 2–3 | Direct current-endpoint check, target export, preserved previous evidence, and unchanged outer entry. |
| Charter §§13–17, 21, 24 | User-selected typed-value transport and activation expiry; outside shallow selection, raw resumption, whole-argument reification, Value-entry forcing and separate actual callable role. |
| Selected complete captured-closure definition §§2–4 and selected construction §§3–5 | Original receipt/Force/rebind/complete invocation return and pending prefixes; actual selected nested Lambda/Name/Result/Delay/Bind/Call source-constructor instances. |
| Typed computation core §§3, 6–7 | Not wholesale Authority: notation and reviewed derivations for those same inert/source roles and the distinction between same-value checking and executed conversion. |
| Ordinary computation package §§2–6 | Not wholesale Authority: the displayed equations express the selected charter clauses; unresolved whole-package adequacy is not used as an established theorem. |
| Typed source-owner realization §6, selected outside-image equation | The exact equation selected by charter §§14–15, with actual applicability at yielding boundary and original raw continuation; not all owner/model clauses of the Draft. |
| Selected nested-block source addendum §2 | The exact **unannotated** nested form constructs and returns a closure capturing the same `f`; returning that closure does not invoke it. |
| Native source Generalize definition §§2–3 and construction §§3.1–3.3 | Annotation final roots and constructor-owned original scopes, Desc versus Intrinsic versus actual event fields; local annotation laws remain genuine independent inputs. |

The nested-block addendum selects only
`my apply f = { my step x = f x; step }`. It is not authority for adding an
annotation or for the multi-parameter header. The R1 draft's reference to
“ordinary curried headers” is intent/navigation evidence, not the missing
semantic constructor theorem. Current shadow HIR retains the original
parameter list and annotation incidence; it does not semantically elaborate
this annotated multi-parameter definition. Its refusal or pending markers are
not a semantic rejection proof.

## 3. Original incidence and the proposed header completion

Fix one resolved source declaration `d`, its two ordered formal occurrences
`b_f,b_x`, written annotation occurrence `a`, Name occurrences `n_f,n_x`, and
body Call occurrence `c`. They are original source occurrences, not positions
reconstructed from equal types. Name resolution gives `n_f -> b_f` and
`n_x -> b_x`. Let `sigma_d`, `sigma_f`, `sigma_x` be the original declaration,
first-formal and second-formal source scopes, respectively. Their source
containment is `sigma_d < sigma_f < sigma_x`; this is lexical containment,
not a statement that the invocation events are nested live activations.

Keep the full original binder tree and `xi=(nu,K,D)` and all introduction,
formation, license, guard, role, entry and dependency fields. Define the
candidate macro on a **resolved header**, before any checking success:

```text
H[d;b_f:a,b_x;e] := Lambda(b_f:a, Lambda(b_x, e))
e                := Call(Name(n_f,b_f), Name(n_x,b_x))
```

The source-root Lambda is anchored at `(d,b_f)`; the inner Lambda is anchored
at `(d,b_x)`. These are constructor indices over original source occurrences,
not new source tokens or a second positional identity system. Their original
annotation `a` remains at `b_f`, not at the body Name and not at `b_x`.
The inner closure captures exactly the lexical binding of `b_f`; it does not
capture an activation snapshot or invent a second formal.

| Item | Exact source/core correspondence |
| --- | --- |
| Current endpoint at `a` | Must be supplied by Parameter/annotation introduction at `b_f`; the macro does not identify it with a fresh `v_f` by fiat. |
| Normalized target at `a` | Must be supplied by the written-type owner in `sigma_f`; the two `_` occurrences and concrete `io` clause retain separate identities. |
| Exported formal contract | The actual annotation target and prior-plus-local evidence, if the genuine boundary succeeds. |
| Body callee Name | Restriction of that same binding/certificate at `n_f`; same actual provider, capture reference and scope map. |
| Body argument Name | Actual `b_x` binding at `n_x`; distinct binder and contract root, even if its endpoint equals another endpoint. |
| Argument carrier | The original inert `Delay(Name n_x)` with its independently typed whole-computation fields. |
| Body Call | Original `c`, with separate callee, argument, checking, receipt, complete invocation, result-consumer and future-provider fields. |
| Permission | `a`'s original `io` clause at its typed Function output position; no family-wide association is invented. |
| Event contribution | An actual provider request introduced inside `c` has its own original operation, provider, path, dynamic event and `K,D`. Annotation incidence still needs its genuine typed correspondence. |

**Header macro theorem.** For every independently legal derivation of the
right-hand two-Lambda tree with its complete original formal/annotation/body
local laws, there is exactly its macro-headed derivation; expansion maps the
latter back to that tree. Expansion and compression preserve the entire
dependent operand tuple, rules, scope maps and observations, up to renaming of
the two constructor indices. Neither operation tests Q.

**Proof.** The new macro rule has the exact two-Lambda derivation as its sole
premise, with no weakened or additional local law. Expand one macro node to
that premise. Compress the matching root and inner Lambda nodes, keeping
their original anchored formal indices. Induction on surrounding source
constructors transports all shared operands and complete guard packages by
their original constructor maps. The executable tree is unchanged; the
new macro label has no execution rule. The two transformations are inverse
on derivations with this chosen matching subtree. QED.

This is conservative label/composition completion, **not** an annotation
constructor or a theorem that the premise exists for the actual source.
All old W/Z alternatives, whole domains, worlds and primitive laws remain
unchanged because none is added, deleted, filtered or reinterpreted. An
arbitrary old annotated rule is not strengthened by this macro. It follows
that this completion alone cannot discharge any missing original guard,
target, port or local annotation law. A source language which chooses another
multi-parameter elaboration is outside this macro theorem; that choice has
not been selected here.

## 4. Expired-original-receiver theorem

First take the exact selected source

```yu
my apply f = { my step x = f x; step }
```

Use its selected source root
`Lambda(f, Bind(step, Return(Lambda(x,Call(Name f,Name x))), Return(Name step)))`.
The complete captured-closure definition §4 selects these actual source
Lambda/Name/Result/Delay/Bind/Call and finite-prefix cases; §2 selects their
complete Value entry and invocation Return. This is the genuine source
fragment for the theorem. Any independently valid original inlet/captured
provider/whole-argument/guard/primitive package stays its original input,
as in that selected constructor. The theorem does not assume membership of
the newly constructed step or original receiver expiry as a premise.

Let `p` be the actual decorated callable returned while the first invocation
forces its whole argument. It is fixed at that actual Return; no alternate
provider is chosen after checking. Let `r_f` be that invocation's actual
receiver and `s_p` the returned inner closure capturing `p`. Name/capture
transport retains `p`, its installed certificate, annotation/profile and
original `K,D`.

The first invocation has this complete source equation:

```text
receipt(r_f,t_f);
Force(t_f) >>= (p,C1).
  rebind(b_f,p,C1);
  Return(Closure(b_x, Call(Name p,Name b_x), captured=p),C1);
ReturnFromInvocation(r_f)
```

For the selected nested source the sequential Bind additionally installs
the inert inner closure as `step`, and its final pure Name returns that very
closure. These selected Return/Bind/Name steps add no request or invocation
of `step`. Suppressing those administrative steps gives the same equation
above; the candidate curry macro has it without the local Bind.

The Lambda construction in the body is inert. In particular its body Call
`c` cannot execute between the Return of `p` and this invocation Return.
Effects, pending requests or divergence of `Force(t_f)` are not omitted.
While entry is pending, `s_p` has not been returned. If entry diverges there
is no manufactured returned inner closure. A raw entry resume reinstates
only the original still-pending invocation suffix; upon normal completion its
`ReturnFromInvocation` removes that resumed occurrence.

**Expired-f theorem on selected source.** After the maker's completed Return,
the returned `s_p`'s direct invocation/callee-entry spine does not carry the
maker's exited receiver occurrence `r_f`. No incidence from that exited
occurrence can satisfy the live capture predicate for its body Call. The
same conclusion holds for ordinary request/resume/future developments of
that later invocation which retain its unfinished suffix, including divergence.
The theorem concerns the particular completed receiver occurrence: it does
not forbid another call or independently lawful invocation re-entry from
creating a current occurrence associated with the same static declaration.

**Proof.** Ordinary invocation Return removes `r_f` before returning `s_p`
to its caller. The returned closure retains lexical value references and
lineage, not an activation snapshot. Its later application starts from the
caller's current configuration and introduces a fresh `r_x`. Executing `c`
introduces the actual provider invocation `r_p`; neither transition pushes
`r_f`. A source request suspends the pending invocation suffix. Its raw
resume wrapper re-enters that pending invocation and supplies no revival
action for the already completed maker occurrence. Future uses similarly
begin at their actual caller configurations. Induction on the direct spine
and its unfinished-suffix developments proves absence of that exited
occurrence. Any independently created current receiver, including a genuinely
licensed replay of another retained raw handle, is its own current occurrence
with its own original lawful re-entry evidence; it is not an automatic
restoration by lexical capture. The live capture predicate requires
`Active(r_f,C)` and hence has a false conjunct at every proposed original
`r_f` incidence. All finite prefixes of an infinite development obey that
same induction. QED.

The theorem is stronger than merely placing a Call outside an ambient
handler: it rules out the **exact original receiver** by its construction
and lifetime. It does not infer that no eligible receiver exists. A new
legitimate receiver or current caller handler can be live, and the retained
static annotation/profile may participate in an independently justified
typed view at that receiver. Static seed applicability is not `Active(r_f)`.
Nothing in this proof deletes or releases static protection, changes the
actual provider's lower mark, or proves a generic annotated-implies-unprotected
rule.

The same core induction proves the candidate macro consequence. That
corollary does not transfer the selected source meaning to an annotated
header. For the concrete pure-entry providers in §5.1 there is no maker-entry
raw handle, retained continuation in `p`, or re-entrant source code, so the
inapplicability conclusion covers **every** later finite execution and raw
resume of that witness without an excluded re-entry case.

The selected theorem itself changes no original domain, W/Z arm,
world rule or operation law: its conclusion is exact activation absence on
the actual source developments, not a restriction of admission.

## 5. Actual eligible prefix removal and complete suffix frame

This section supplies local removal mathematics from the original source
handler equations. It is independent of a proposed plain-annotation release
policy. A receiver's expired permission cannot replace its premises.

Fix an actual original typed operation `op` in the `io` family, exact payload
`a`, response `z`, provider, original request occurrence and dynamic event
`q`. An independently supplied primitive declaration must supply the complete
operation packet and law; a printed `io` row is not that declaration. Fix a
current live shallow handler `h`, ordinary visibility at the actual search
configuration, compatible accepting pattern/arm, and a pure total selector.
Its selected arm runs outside `h`, returns no latent handler capability, emits
no request and invokes the **raw** continuation once with exactly `z`.
These are concrete handler code/laws, not a `Lawful` hypothesis.

For the finite witnesses, use the original declaration-instance Request
constructor with payload and response `Unit`. At its actual declaration
instance, the packet has the existing operation/provider identity, payload
`()`, response type `Unit`, request occurrence/event, and the full original
family `K,D` fields. Any family parameters retain their original bound
telescope. The arm returns the correctly typed response `()` and never
narrows a generic request opening. Its Request continuation is either
`Return(())` or the second original Request followed by `Return(())`.
These are Request/Return/Bind constructor instances, not arbitrary primitive
acceptance facts. The genuine declaration/port/license/initial-world package
is still a necessary independent input, as required by the selected native
constructor; this note neither creates a foreign primitive nor asserts that
the current repository has a concrete `io.tick` declaration.

The image rule is the charter-selected equation from typed source-owner §6:

```text
H[Request(q,k)] = MatchRequest_H(q,k) >>= Finish_H(q,k)
Finish_H(q,k)(Accepted(arm,bindings),C) = Run(arm.body,bindings,C)
```

Our pure matcher immediately returns `Accepted`; the arm is the ordinary
`Resume(raw-k,())` constructor in the current outer context. This explicitly
instantiates the original selected law rather than treating the Draft
ordinary-computation package as wholesale semantic Authority.

For any independently legal full source suffix `S`, put

```text
C_q = Request(q, C_h, lambda z. S(z,C_after))
H   = shallow handler whose q arm is Resume(raw-k,z)
```

`C_after` is the actual outer state/configuration after selection and source
unwind. It is not a snapshot of `C_h`. The selector/arm has the specified
store frame; any allowed source configuration change is exactly the original
unwind/pop and required pending invocation re-entry. All request, response,
resume and future proof fields retain their original scopes.

**Prefix-removal theorem.** The complete source observations of `H[C_q]`
are exactly those of the raw suffix `S(z,C_after)`, preceded only by the
ordinary administrative selection/resume steps. The event `q` has been
handled and has no outward Request occurrence from that consumed prefix.
Every observation, pending suffix, divergence prefix, returned latent value
and later-use obligation of `S` remains in the image at that same tuple.

**Proof.** The selected handler sees the actual eligible `q`. The original
shallow rule pops the selected occurrence and executes its arm outside it.
The pure selector/arm adds no outward request or store update. The raw resume
equation substitutes the same `z` and current state into the original saved
suffix, with no automatic handler wrapper. Thus the remaining source
configuration is exactly `S(z,C_after)`, including its pending invocation
return wrappers. Its complete finite developments are unchanged. Conversely
every such development is reached through that same selected prefix and raw
resume. Return and Request/Bind inversion prove equality of observations,
and finite-prefix induction covers divergence and all later interactions.
QED.

**Contribution frame.** If `j != q` is introduced by `S`, its operation,
payload, source occurrence, provider, original typed path and `K_j,D_j`
are exactly those supplied by the original suffix rule. The transformation
does not subtract that contribution, change any provider-owned protection,
erase any prior annotation evidence, independently choose its shared `nu`,
or delete a symbolic predicate still used by the suffix/return/future result.
Its live activation state is the original post-selection state; retaining a
stale `C_h` would be an invalid frame claim. The theorem preserves all the
actual suffix alternatives jointly and is not a family-name cancellation.

No production Option 2 alternative is removed by this proof. It proves the
actual source image, not that every opaque W/Z observation has a source
witness or disappears with `q`. A claim of output-family absence for a
complete production bound must separately cover every original W/Z arm with
its independently fixed guards and image law. The source calculation is
valid in any unchanged background kernel supporting these original local
actions; it does not construct an arbitrary initial world or State law.

### 5.1 Nonempty later-request witness on the selected nested source

Construct the actual source provider at the original native closure rule:

```text
p := Closure(ValueEntry(I_Unit),
             Request(op,(),lambda z.Return(())), empty-capture-environment)
F_p := Strict(I_Unit, ignored-formal:Unit, R_op, IF_p)
```

`I_Unit` is one independently fixed complete Unit-result carrier interface,
with its original domain and guards; its carriers may request, diverge or
return, and those alternatives are retained in `Strict`. `R_op` is the
independently typed complete descriptor of the original declared Request
and Unit Return above, including every opaque alternative in that declaration.
Its primitive request proof and response-to-Return proof use the same packet
and world, not a membership assumption about `p`.

The selected complete Value-entry constructor composes the actual inlet
receipt, Force, dependent Return/rebind, this local typed body and invocation
return. Thus it constructs the source provider at `F_p` under its original
port/world/local-operation premises. Choose the inner checked `F_c=F_p`;
same-provider inclusion is identity and not an unproved cast. Choose the
actual inner carrier as `Delay(Return(()))` with its original complete
`I_Unit` proof; whole-argument checking is identity at that same carrier.
The selected captured Step/Block/OuterTrace constructor now applies with
those original independent fields. All source entry prefixes and source
W/Z clauses remain in its complete description; the witness below uses the
actual pure returning carrier diagonal, not a restriction of that domain.

Supply this newly constructed provider as the pure
Value argument to the outer Lambda of the exact selected nested source,
obtain its returned `step=s_p`, then invoke `step` on a pure
scalar Name argument. Value entry and both Name computations are returning
and request-free; the body Call exposes `q`. Expired-f proves its original
`r_f` is absent. With no current eligible handler, `q` is an outward pending
request. With a fresh ordinary eligible caller handler of the form above,
prefix-removal yields `Return(())` and a genuine consumption of `q`.

Thus an actual nonempty request can occur after the original receiver exits;
its handling can be real and lawful while that old receiver's activation is
provably unavailable. No old grant has been resurrected. This core witness
does **not** prove that the omitted semantic annotation elaborator accepts
this provider at `_ -> [io] _`. Adding that assertion would fill the missing
target/checking rule with success.

### 5.2 Two requests refute a stronger subtraction shortcut

Take a raw provider suffix

```text
Request(q1_io, lambda z1.
  Request(q2_io, lambda z2.Return(b)))
```

where `q1 != q2` have the same family and actual provider, but different
dynamic events and original request occurrences. The handler above consumes
`q1` and resumes once. By prefix-removal, the full output begins with the
unchanged `Request(q2_io,...)`. The raw suffix runs outside the consumed
shallow occurrence, so that occurrence cannot consume `q2`.

This is a minimal two-request source-image witness against the inference
“one eligible removal plus `[io]` permission implies no outward `io`”. A
singleton returning suffix genuinely removes the prefix; a two-request
suffix preserves the second event. Both calculations retain family predicates
needed by the remaining continuation. They are not a representation collision
or a transition table assuming the desired removal. They also do not prove
an accepted annotated-source counterexample: the annotation's authentic
target/check remains missing.

## 6. Static body-head theorem and the surviving C5 cut

Suppose an authentic annotation owner eventually constructs a target with
outer head `Function`, directly checks its actual current endpoint `E_a`
against that complete target `T_a`, and exports `T_a` as selected by d1.
This hypothesis is not used in the dynamic theorem and is not proved here.

**Head theorem.** On the direct capture/Name/Result path of the candidate
header, the body's callee endpoint is `T_a` at its certified scope map.
Consequently the body Call is not a source exposure of the pre-boundary
inferred endpoint `E_a`; if `T_a` has the structured Function head, the
body Call is not itself an inferred-variable-to-Function Dir-Protect step.

**Proof.** The boundary exports its target. The inner closure captures that
same binding/certificate; Name restricts it; Result returns the same decorated
value and endpoint. None of these source rules restores the hidden pre-check
endpoint or creates a fresh description for a monomorphic capture. Therefore
the original body endpoint is the mapped `T_a`. Structured Function head is
preserved by those maps even when its nested hole coordinates remain
flexible. Dir-Protect requires an already protected **inferred variable at
this exposure**. A former variable's eventual equality with `T_a` cannot
replace that original premise. QED.

This eliminates a misplaced **body-Call** seed bridge for an authentic
Function-headed export. It does not prove absence of protection already
recorded in the exported target, nor remove provider lower marks. A genuine
later new inference-variable exposure needs its own source introduction.

The remaining potential direct upper exposure is the annotation itself,
`E_a <: T_a`, if its actual owner classifies it as such. If `E_a` is still an
inferred variable, C5 requires its genuine exposure-time seed origin or a
complete no-seed theorem. `b_x` remains a distinct root; an absence-origin
seed at `b_x` cannot become one at `b_f` by endpoint equality. Provider
lower protection cannot flow backwards to `E_a`. Neither exclusion proves
that all annotation seed introductions have been exhausted. The selected
sources do not supply that exhaustive rule set, so this note claims no full
`ProtectedVarAt` inapplicability theorem for the annotation boundary.

## 7. Why no completed target is claimed

A tempting construction declares fresh `v_f,A,B` and writes
`E_a=v_f; T_a=Fun(A,io,B)`. It is not the required complete owner judgment:

- Parameter-local introduction needs the original scope/port telescope and
  every formation/license/Intrinsic guard. Native source Generalize retains
  that output but does not establish an unprovided annotated introduction.
- The two written `_` occurrences introduce description choices at their
  own source scopes. They do not themselves determine the whole argument
  carrier's independent domain, actual entry, receipt, guards or future arms.
- Value entry forces the whole argument before the body. The complete target
  must account for argument effects and body effects jointly; replacing the
  output with a support-only `io` row loses that coupling.
- A concrete `io` annotation clause needs a resolved complete operation/family
  contract and original output incidence. Family spelling alone cannot supply
  the typed body/contribution/receiver correspondence.
- Every original W/Z, complete admission and world field remains active.
  Building a convenient singleton trace descriptor is not normalizing the
  source contract; deleting opaque arms is not a conservative extension.

The header macro proves no new local target or seed law. Choosing a new
annotation target descriptor, a default annotated seed/no-seed rule, or plain
annotation slot-release activation would be a **new semantic choice** unless
its exact conservative correspondence to independently selected local rules
is proved. Those choices are explicitly unapproved here. The selected `?`
meaning is a different marked-slot release rule; this source contains no `?`.
It cannot be inserted silently to realize `[io]` permission.

## 8. Eliminated premises, coverage and next action

| Obligation | Actual progress in this note |
| --- | --- |
| Source header construction | Exact natural macro and conservative derivation correspondence; semantic selection not claimed. |
| Current annotation endpoint / complete target | Not constructed; source owner input still open. |
| Original `f` receiver activation at body request | Eliminated by return/later-call induction in the nested-Lambda core; actual selected application available on the unannotated nested-block source. |
| Body inferred-variable seed exposure | Inapplicable after an authentic Function-headed target export; the earlier boundary remains open. |
| Exhaustive annotated boundary C5 | Not proved; absence-origin inversion is not reused as a complete answer. |
| Concrete local effect removal | Actual eligible prefix consumption derived directly from shallow source equations, with exact current-state suffix frame. |
| Annotation C6 incidence / static release | Not derived from permission; no new release policy selected. |
| Observability | Nonempty pending request versus handled Return, and retained second same-family request, in complete core-source calculations. Accepted annotated source not established. |
| Production W/Z coverage | All alternatives preserved as original inputs; universal production absence/removal is not claimed. |

The next productive annotated-source step is a genuine written-type owner
constructor, including complete Value-entry coupling and original incidence,
followed by direct target export. That would make the head theorem applicable
without its current substantial premise. An activation proposal must account
for the expired original receiver and any newly legitimate receiver separately.
Another absence-origin audit or a checker which assumes the missing local
target/seed/release laws would not advance this cut.

## 9. Verification, dependency pins and commit packet

Checks: sequential required rule/source reads; narrow actual source/typed-core,
Generalize, header/shadow and selected scope inspection; creation guard and
leased-file readback; SHA-256 direct dependency capture. No Git commands,
children, user questions, production/shared-file writes, tests, builds,
parser execution, probes or mutation experiments were used. No executable
oracle, finite-range search or timing claim exists. Resource use was only
lightweight reads and one Markdown write; process RSS/wall totals were not
instrumented. Producer inspection is not independent review.

One lightweight Python metadata check reread all 17 dependency hash rows:
17 matched, zero mismatches. It also checked paired Markdown fences (14).
This is file integrity evidence, not an executable semantic model or proof
checker; it used no solver, parser, compiler or external oracle.

The theorem's oracle is the independently stated source Return/Bind/Call and
shallow equations. The macro uses those same equations and introduces no new
transition; it proves correspondence, not their source adequacy. The target,
annotation legality and missing seed calculus have not been filled with
shared assumed transitions. A supplied-record checker would not discharge
them. The primary must verify these read bytes against the assigned baseline
before integration; this worker performed no Git operation.

| Direct dependency | SHA-256 read snapshot |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-09-annotated-formal-constructor-draft.md` | `e927639da0cbfa1c31735ad486004095d04451191d1d883a678dfa1b198301d3` |
| `notes/theory/2026-10-08-production-call-elaboration-proposal.md` | `e6e333cdffc532310f58ad1fd56091b3e58185fb89802e9ac1814985182487dd` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-hir/src/shadow.rs` | `5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f` |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |

Commit packet:

- Exact leased path: `notes/theory/2026-10-09-annotated-formal-seed-and-removal-theorem.md`.
- Baseline: `c4cf02dd3307e6051b6d23b8af17c6f0633c09f0`.
- Dependency changes by this worker: none. Baseline byte equality is left to
  the primary; read snapshot hashes are above.
- Claim/review status: independently reviewed bounded local constructor/lifetime/
  image theorems; full annotated attack incomplete; no accepted annotated-source
  counterexample, complete target, C5/C6 closure or implementation authority.
- Checks already run: lightweight policy/source/owner reads, dependency hashes,
  creation guard and focused readback; zero tests/builds/probes.
- Proposed checkpoint message: `research: prove returned-formal receiver expiry and exact request-prefix image`.
- Shared-record deltas intentionally deferred: preserve C5/C6/target owner and
  production gates open; record the authentic unannotated nested-source
  receiver-expiry consequence and the explicitly unselected curry extension;
  avoid promoting the core examples to accepted annotated programs.
