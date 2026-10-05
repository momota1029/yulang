# Q-independent capture attachment: exact source-rule attempt

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed with no findings; bounded rule inversion
Baseline: `1a3e6c89c760b36e386ee0033a568613ebc8e524`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: constructive source derivation, followed by premise inversion
Implementation/semantic authority: none

## Objective and result

Attempt to construct the first typed evidence-environment attachment and
captured-name lookup certificate for exactly

```text
my apply f = { my step x = f x; step }
```

The new lexical `CaptureUseIncidence` supplies the previously implicit
association of the local lambda, outer binder, inner callee use and source
position. It does not discharge the typed association. The strongest route
through the inspected rules reaches a source-interface/name skeleton and
then an open typed lookup premise. A supplied original receipt makes that
premise expressible, but the inspected rules still do not construct it.
Without that supplied receipt, original Q-independent contract/receipt
formation is an additional unresolved prerequisite. Neither prerequisite is
assumed proved in this note.

This is a bounded characterization of the named rule interfaces and a
conditional derivation prefix. It is neither a global impossibility result
nor an accepted-program counterexample. The result does not close source
adequacy, principality or production conformance.

## Authority, dependencies and claim classes

The Authoritative nested-block addendum §§1–3 fixes sequential binding,
return of the local function value, lexical resolution, and retention of
that same outer `f` across later calls. The Authoritative inferred Function
call-view document §§2,3,5 fixes shared component generation, stable static
slots, Q-independent admission, the provisional protected Handler formal/use
view and ordinary-value determination. It explicitly leaves the exact
generation and preservation judgments open. The annotation/public/internal
view separation in its §1.1 remains in force.

The typed-computation-core document §§3,6,9 and source-computation-role §10
remain Draft constructions with scoped reviewed results. Their source input
description (core §2) is needed to invert §3. They supply conditional
constructors and preservation laws, not additional authoritative rules that
complete the open call-view source producer. Their independent prior reviews
do not certify this note.

Read prior results: nested-block-function-conditional-core-derivation,
nested-block-capture-transport-derivation, and shadow-capture-use-incidence.
The assignment's shorter `nested-block-conditional-core-derivation` locator
does not exist; the first listed file is the actual dependency. The first
note assumes complete decoration T2/T3. The second stipulates an independently
certified original receipt. Neither assumption is imported as an established
source fact here. This attempt adds direct inspection of the implemented
lexical incidence and inverts the name/environment interfaces against it.

Established decisions: exact source meaning, fixed source identities and
capture. Bounded code facts: the incidence's fields, construction and
validation at this baseline. Conditional facts: the ordinary result/entry
skeleton and preservation of an already admissible decorated descriptor.
Candidate assumptions: original certificate formation and the typed
environment/lookup judgment displayed below. They remain open proof leaves.

Frozen Oracle is not read or used as a premise or reference oracle. This
attempt makes no independent claim about its behavior.

## What the new incidence actually supplies

Let `l_s` be the local lambda expression, `d_f,d_x,d_step` the binders,
`u_f,u_x,u_step` their relevant uses, `p_f` the retained position of `u_f`,
and `c` the inner application. The selected lexical map is
`u_f -> d_f`, `u_x -> d_x`, `u_step -> d_step`.

At this baseline, HIR `CaptureUseIncidence` has exactly four fields:

```text
(lambda: ExprId, captured: BinderId, occurrence: UseId, position: PositionId)
```

The narrow projector records `(l_s,d_f,u_f,p_f)` after obtaining the
callee use of the local lambda's `Apply`. Validation checks artifact identity,
the local lambda's singleton capture, its application's callee binder/use,
the retained use position, uniqueness per lambda, and coverage of lambdas
with nonempty capture lists. Lexical scope validation checks the captured
binder is in the enclosing scope. The core facade reexports this record.

These checks give concrete source anchors for the proof obligation. The
record contains no provider activation, original receipt, completed contract,
`beta`, `Slots(beta)`, typed path, `Flow`, `nu`, `K` or `D`. Its local lambda
correspondence remains `PendingTypedCaptureProviderReceiverAndSemanticDischarge`.
An artifact brand prevents cross-artifact identifier confusion; it does not
identify a dynamic enclosing activation or attach evidence to a binding.
This is a field/interface observation, not an experiment demonstrating
semantic failure when evidence is deleted.

## Constructive prefix and original joint scope

For the inspected ordinary parameter fragment, core §6 generates

```text
P_f = Value(A_f)        Gamma_f = Gamma_0[d_f:Value(A_f)]
P_x = Value(A_x)        Gamma_fx = Gamma_f[d_x:Value(A_x)]

synth(name d_f) = (Value(A_f), name d_f, result(name d_f))
synth(name d_x) = (Value(A_x), name d_x, result(name d_x))
```

Fresh endpoints here are names for constraints, not independently selected
semantic witnesses. This construction does not make the supplied callable
Pure, rewrite its entry, or resolve the provisional Handler seed. Name
synthesis copies `Gamma`'s source interface; it does not synthesize a receipt.

The application row constructs an inert `reify(call(n_f,n_x))`, symbolic
`E_c,A_c`, and obligations for a Function result, the **whole** argument
computation and its typed paths/contract. It does not solve those obligations.
The lambda/bind rows construct the structural target

```text
lambda(P_f,
  bind(d_step,
    result(lambda(P_x,call(result(name d_f),result(name d_x)))),
    result(name d_step)))
```

with the §6 administrative reify/eliminate pairs retained unless their
same-context contraction premises hold. This tree is the already selected
structural target; constructing it adds no proof of complete decoration.

Fix an enclosing activation `r_A`, its rebound provider value `g`, local
closure instance `s`, later `step` activation `r_S`, and eventual invocation
`r_G` of `g` if the body reaches `c`. These labels select no allocation policy.
The source decision fixes the captured value from `r_A`; it does not make
`r_A`, `r_S` and `r_G` the same activation.

Write `C_f` descriptively for the original completed contract/profile and
all associated source/scope/path/receipt references. Write `R_f` for its
finite original certificate at the original joint `xi=(nu,K,D)`. This is
notation for the required evidence, not a new carrier or chosen language
rule. Its complete `Slots(beta)` inventory and all shared dependencies must
remain in that one original scope. No projection to independent port
witnesses, choice of a new `nu`, fresh `K,D`, or discharge by `Q` is allowed.
Historical owner/activity facts remain interpreted at their original events;
preservation does not assert that an expired owner is active later.

## Two open premises, with the attachment leaf isolated

The unconditional source proof requires at least these two distinct leaves:

```text
O: source component independently of Q generates/certifies
   Original(d_f,r_A,g,C_f,R_f; xi).

A: from that original certificate and the selected lexical incidence,
   closure introduction and captured lookup retain that very
   (d_f,r_A,g,C_f,R_f; xi) in the evidence environment of s at u_f.
```

`O` is not discharged by the lexical incidence. Call-view §§2,5 require it
and explicitly leave its constructing judgments open. Source-role §10's
`Receive(...,typed correspondence)` and `RebindResultPath` do not prove
`O`: they take the matching typed correspondence and contract as input.

To isolate the assigned attachment gate, temporarily grant `O` as the exact
explicit hypothesis **H_original**, without claiming it follows from source.
The required judgment is then the following unfilled proof leaf:

```text
H_original: Original(d_f,r_A,g,C_f,R_f; xi), independent of Q
LexicalCaptureUse(l_s,d_f,u_f,p_f)
the selected closure s captures the rebound g from r_A
--------------------------------------------------------------- ?
AttachAndLookup(s,u_f,p_f) preserves the whole original
(d_f,r_A,g,C_f,R_f; xi), including beta, Slots(beta), annotation
absence, source scope, complete typed paths and shared dependencies.
```

`AttachAndLookup` names the desired certificate rather than an admitted rule.
An implementation might use different representations. A proof needs both
association at closure introduction and the correspondence at name lookup.
Lexical agreement alone is insufficient to instantiate that proof interface.
This statement demands preservation of the original certificate, not a new
receipt at closure construction or a later active receiver.

The failed inversion is exact: core §6's name row has premise
`Gamma_fx(d_f)=Value(A_f)` and conclusion consisting of that interface and
`name d_f`. It has no evidence-environment premise or conclusion from which
the attachment/lookup certificate can be recovered. Adding `R_f` to a
metatheoretic context does not change that row. Core §3's `V[name]=lookup`
can consult an environment that already carries the required descriptor,
but its input includes the typed correspondence. The association that
would make this particular lookup typed is precisely the unresolved leaf.

Thus the first missing **attachment** premise under H_original is at the
callee occurrence `u_f`, before using its typed path to justify the complete
call at `c`. In the unconditional source proof, `O` remains an earlier
prerequisite. The scoped attachment blocker does not replace or conceal it.

An independent compiler-referee reviewed this bounded inversion and found no
blocking, major, or minor findings. The review inspected the complete note,
its governing rule sections, the prior conditional derivations and the
capture-use incidence implementation. It did not inspect or certify
production lowering or solver behavior.

## Why the available routes do not close that leaf

| Inspected route | Constructed or preserved conclusion | Missing input on inversion |
| --- | --- | --- |
| Core §6 parameter generation | fixed Value role and finite receipt/entry skeleton | admitted typed paths; original complete contract/receipt |
| Core §6 name synthesis | interface copied from `Gamma`; inert name and result | evidence-environment association with `R_f` at `u_f` |
| Core §6 application | symbolic call/result skeleton and boundary constraints | complete typed call and captured callee correspondence |
| Core §3 closure descriptor | lexical references and evidence of a finite typed derivation | already decorated local body/capture, including A |
| Core §6 substitution | transport of an existing derivation preserving typing premises | A must already hold for the transported derivation |
| Source-role §10 entry/rebind | matching result/value path image at original joint scope | receipt/typed correspondence; no closure-capture introduction conclusion |
| Core §9 return/storage/path directions | preservation/classification of already typed interactions | resolved original correspondences; no grant or attachment creation |

The descriptor statement that closures capture typed evidence is a
preservation specification for a supplied decorated input. Reading it as
an unconditional source attachment rule would supply its own missing input.
Similarly, identity substitution on the whole `R_f` preserves every original
reference but does not add its association to `s` or `u_f`.

Sequential binding and final-name return can pass an already certified
descriptor unchanged. Inverting them returns to closure introduction;
they do not construct a missing captured-name certificate. Later entry of
`step` receives `x`, and invocation of `g` has its own actual entry. Neither
event retroactively derives closure introduction evidence. Receiver
activation after static attachment remains a separate dependent gate.

This stops the method at the interface mismatch. No larger supplied-rule
checker or second identity-map construction is proposed: both would assume
A and leave the same premise untouched.

## Checks, independence, coverage and failure conditions

The derivation uses the named source decisions and Draft rule premises.
It has no independent executable oracle. The implemented lexical record
independently exposes the source anchor fields relative to this derivation,
but its implementation/validation shares the approved lexical interpretation
and does not validate typed source rules. No checker assuming receipt or
capture transitions was run.

Read-only checks: `git rev-parse HEAD`, `git branch --show-current`, bounded
`rg`/`sed`/`cat` source reads, `git diff HEAD -- <nine direct inputs>` (empty),
`sha256sum <nine direct inputs>`, and the leased-path absence guard (exit 0).
The initial batched task/record read was truncated; decisive governing
passages and prior derivations were read narrowly afterward. No exhaustive
repository absence claim is made. The primary owns integration-time
dependency rechecking and independent review.

Coverage: one exact source candidate, one inner captured callee occurrence,
the recorded incidence's construction/validation, and inversion of the named
ordinary rules. Seeds, ranges, mutations and numerical search coverage do
not apply. Zero executable probes, tests, builds, child agents, network
queries or Git mutations. One leased Markdown artifact; no scratch outputs.
Individual shell reads took about 0.0–0.1 seconds. Aggregate agent CPU,
peak RSS and full wall time were not instrumented and remain unknown.

Failure conditions: changed dependency bytes; a demanded rule outside this
fragment; loss of any original joint certificate reference or source scope;
non-Q-independent receipt formation; or inability to supply the admitted
typed paths. These invalidate a proposed completion of the conditional
proof, not the selected source meaning. No source rejection is inferred.

Unverified: source producer O; attachment/lookup A; two-stage formal/use
role resolution; local generalization/instantiation; active receiver
realization; complete Function admission/direct queries and joint-image
containment; arbitrary captures, mutation/aliases, recursive local groups,
other brace forms, effects/handlers/resumption; parser or production
acceptance, solver behavior, principality, adequacy and implementation.

Recommended next action: have the primary assign construction/review of the
single source evidence-environment introduction/lookup judgment, with O
explicitly retained as an open prerequisite or separately certified input.
Its contract must retain the whole original `xi` and prohibit deriving
attachment from `Q`; later receiver activation should use that certificate
in its own gate.

## Frozen dependency snapshot

Whole-file SHA-256; all nine direct inputs matched the pinned HEAD when read.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb` |
| `notes/progress/2026-10-06-nested-block-capture-transport-derivation.md` | `5e15ec1c99369c2d6d14f234cd02d4fc2f37ab918fa36f0ecb06ee5a74eb2f62` |
| `notes/progress/2026-10-06-nested-block-function-conditional-core-derivation.md` | `fc227427abc438c3d9fb5f07ff97e25cd6f8c4e08d6b1a270fe253a3b80f8746` |
| `notes/progress/2026-10-06-shadow-capture-use-incidence.md` | `ad79d1a4afbba985c498dbae2d13d354177bbac320a23eb6954ed4276db0122a` |
| `crates/yu-hir/src/shadow.rs` | `a0ff42ed537502737102fb7da6a79983eb81766a4da4b06a0578f703d2fded50` |
| `crates/yu-core/src/shadow.rs` | `e17a0459931d1fa0ae414ab6256ffc67a2eb98ca1784145f44e0cf9d6a2e8562` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-q-independent-capture-source-rule-attempt.md`.
- Baseline SHA: `1a3e6c89c760b36e386ee0033a568613ebc8e524`.
- Changed dependency hashes: none observed; frozen inventory above.
- Claim/review status: frozen, independently compiler-referee-reviewed with
  no findings; research-only bounded inversion; O and A remain open; no
  theorem closure or implementation authority.
- Checks already run: read-only baseline/branch/scope reads, nine-input HEAD
  equality and SHA-256 inventory, lease absence guard, artifact readback and
  dependency recheck. No tests/builds/probes.
- Proposed checkpoint message: `research: isolate Q-independent captured-name attachment premise`.
- Shared-record deltas left for primary/curator: record that lexical incidence
  now anchors A's source occurrence without deriving A; retain original
  Q-independent source formation O and later receiver realization as separate
  open gates. No task/index/theory/authority/question-board edit was made.

Writes remain frozen; independent compiler-referee review is complete with no
findings.
