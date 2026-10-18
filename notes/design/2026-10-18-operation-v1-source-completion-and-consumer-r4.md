# Operation v1 callback field and source completion — revision 4

This new Luna-authored revision preserves the r17 parent and corrects the
fixed-contribution identity regression found in r3 review. r1/r2/r3 designs
and their receipts remain at their original paths. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure 0.
This is an additive, reversible research-semantics v1 rule, not yet an
old-rule derivation or production change.

## Source case and exact identities

The candidate input, not yet accepted by the current compiler, is:

```yulang
act outer:
    our next: () -> int
act signal:
    our ping: () -> (int -> [outer] int)

my response (x:int): [outer] int = outer::next()
my result = catch (catch (signal::ping())(1) {
    signal::ping(), k -> k response,
    v -> v
}) {
    outer::next(), _ -> 42,
    v -> v
}
```

There are four separate source identities: the `signal::ping()` request use
`u_ping`; the `signal::ping` handler-pattern occurrence `p_ping`; the source
call `outer::next()` in `response`, `u_outer`; and the outer handler pattern
occurrence `p_outer`. The first two resolve to the same declaration id but are
distinct HIR occurrences. The latter two likewise resolve to the same outer
declaration but are distinct occurrences. No occurrence equality is inferred
from declaration equality.

The original fixed contribution `c` is retained at the `signal::ping` request
use `u_ping`, before any handler or runtime choice, in accordance with the
governing Operation rule. Its resolved operation declaration, HIR occurrence,
complete signature and field path remain part of the same indexed evidence.
The callback body's distinct operation contribution is `c_outer`, formed from
`u_outer`; it is the realizer checked against the field owned by `c`, never an
equality or replacement for `c`. The source field licensed for `c` is `outer` at
`ping`'s nested result function path
`s1 = Operation.Function.ResultValue.Function.ResultEffect`, ordinal `j=0`.

## Typed formation and license (complete premises)

Use a source-directed judgment, not raw HIR-shape recognition:

```text
OperationUse_v1(u_ping, decl; d_use)
DeclSigTyped_v1(decl, theta, binder_path, Sigma_theta; d_sig)
PositiveWrittenField_v1(decl, theta, s1, 0, outer; d_sig, d_pos)
WrittenLicense_v1(decl, s1, 0, outer; d_sig, source_span, scope; ell)
FixedContribution_v1(u_ping, decl; c)
LicensedField_v1(c, decl, u_ping, s1, 0, outer; d_sig, d_pos, ell; q)
EffectUse_v1(u_outer, outer_decl; d_call)
RealizerContribution_v1(u_outer, outer_decl; c_outer)
```

`DeclSigTyped_v1` has recursive rules for every node of this declaration's
complete annotation, and retains its whole telescope and output binder:

```text
resolve(decl) = signal::ping
resolve all effect names in the declaration, including `outer`
------------------------- V1-Int
IntType_v1(int)

IntType_v1(A)      EffectRowType_v1([outer], Written(outer), source_pos, j=0)
------------------------- V1-Function
FunctionType_v1(A, [outer], A)

UnitType_v1(Unit)  FunctionType_v1(int, [outer], int)
------------------------- V1-OperationSignature
d_sig : DeclSigTyped_v1(decl, empty_theta, exact_binder_path,
          Sigma_theta = Unit -> (Int -> [Written outer] Int))
```

The actual implementation must recursively check the complete `SourceAnnotationType`
stored at the declaration, resolve each source row member, and retain every
node/path/position. The abbreviated rules above apply only to this fully
closed concrete candidate; they are not a general signature derivation.
`d_pos` is the projection of `d_sig` at the exact path `s1`, proving positive
`Written(outer)` at ordinal 0 under the callback result binder. It is not
produced by looking up the family at another site. `ell` is introduced by the
source declaration itself at that exact path/scope, before request evaluation;
it is a distinct license object indexed by `d_pos`, not a response or solver
observation.

The fixed contribution and separate callback-body realizer have ordered
introductions:

```text
d_use : OperationUse_v1(u_ping, decl)
d_sig : DeclSigTyped_v1(decl,theta,binder_path,Sigma_theta)
d_pos : PositiveWrittenField_v1(decl,theta,s1,0,outer; d_sig)
ell : WrittenLicense_v1(decl,s1,0,outer; d_sig,source_span,scope)
------------------------- V1-Fix-Contribution
c : FixedContribution_v1(u_ping, decl)

c, d_sig, d_pos, ell
------------------------- V1-Licensed-Field
q : LicensedField_v1(c,decl,u_ping,s1,0,outer; d_sig,d_pos,ell)

d_call : EffectUse_v1(u_outer, outer_decl)
source syntax binds `u_outer` inside `response`; it precedes evaluation
------------------------- V1-Fix-Callback-Realizer
c_outer : RealizerContribution_v1(u_outer, outer_decl)

c, q, d_sig, d_pos, ell, c_outer, d_call
whole response type derivation has q's exact field path and Written outer operand
source typing derives response : Int -> [outer] Int
source typing derives the actual body operation at u_outer, producing c_outer
------------------------- V1-Response-Field-Realization
m0 : SourceFieldRealization_v1(c, q, response_definition,
       response_type_derivation, c_outer, u_outer, body_lower_derivation)
```

`m0` is a relation between the fixed field owner `c` and its distinct source
realizer `c_outer`; it does not assert `c = c_outer`. It retains the exact
source positions, complete declaration and response type derivations, response
definition identity, body occurrence and realizer contribution. If the body
derives a different effect family or the complete response type lacks the
field, this rule does not apply.

## Negative response port: allowance only

The used continuation `k` has a negative interface for the operation's result
type. Revision 1 currently rejects it in preflight and signature construction.
V1 replaces that rejection only for this exactly derived field:

```text
d_sig, d_pos, ell : above
result value type is exactly Int -> [Written outer] Int at s1
fresh effect row r0 at the same solver level; no existing tail or sibling erased
allowance view v0 stores q=(c,decl,u_ping,s1,j,d_sig,d_pos,ell) and [outer], tail=None
------------------------- V1-Negative-Response-Field
neg0 : NegativeResponsePort_v1(q, r0, v0)
```

`candidate_source::preflight_catch_signature` may traverse this nested
negative function only after constructing and validating `q`; all function
arguments, results, sibling rows and source occurrences remain traversed.
`candidate_effect::candidate_catch_operation` uses `neg0` for its exact
`negative_response`; `candidate_signature_effect` uses the same `v0` only at
the indexed `s1,j`. This new rule is **not** a blanket relaxation of negative
concrete rows. `neg0` is indexed by the original fixed `c` through `q`; it
does not own or rename `c_outer`.

The negative view is an upper bound on the effect of an actual callback
response. It creates no positive term, lower Contribution, dynamic request,
or constraint inflow. Only the actual source body `response` and its operation
use `u_outer` generate lower `c_outer`. Permission or Allowance is never converted
to lower flow, installation, selection, residual removal, or an old Inc/Cover
fact. Without q, v1 returns the existing Unsupported result for this shape.

## Actual callback completion and live handler

The request/resume machine has these state transitions:

```text
Running(state S, frames F, active handlers H)
 -- evaluate u_ping -->
Pending(request=(decl,u_ping,payload,event,history), suffix=(k >>= A_decl),
        live_state=S', frames=F', active handlers=H)

resolve p_ping to decl; validate outer/inner installations and exact request
u_ping != p_ping is retained; declaration equality is the matching condition
evaluate the actual source closure `response` in its captured lexical environment E
check its complete type derivation against neg0's same q/result field
-- capture actual continuation and supply that exact closure -->
Resuming(template=(suffix,F',S',H), response=(response_definition,response_code,E), evidence=(c,q,m0))

run template with this response; execute saved application `(response)(1)`
the response body's actual operation site u_outer emits outer::next()
inner signal handler is already removed; outer handler p_outer remains active
outer handler resolves its own declaration and selects the request
-- evaluate its source arm --> Completed(value=42, full_trace, final_state)
```

The runtime response type check accepts a Function only when the solver has
supplied the complete type derivation for this same source response and the
received value is the source closure (code and captured environment) passed to
`k`. A `Closure` runtime tag alone is insufficient. `ResumeArgument` retains
the original declaration/result type and `ResumeTemplate`; it installs the
actual closure without reconstructing it from a family or function name.
The outer handler installation, owner, source occurrence and live state remain
in the captured machine chain; inner handler removal does not reinstall it.

For this vertical example, completed output evidence is:

```text
CompletedOperation_v1(c,q,m0,c_outer, request_at=u_ping, response=(definition,code,E),
   suffix=(k >>= A_decl), event_history, outer_event=u_outer,
   outer_handler=p_outer, final_value=42, final_state; d_run)
```

`d_run` is the actual `RuntimeOutcome::Completed` trace of this source run,
not a wrapper around a missing old `d_orig`. It proves only this concrete
run; it is not a total construction for all old R/W/Z cases.

## Compile-time consumer and post-run receipt are separate

Solver construction precedes runtime execution in the playground. Therefore
`d_run` is not a premise of static constraint insertion, and the solver may
not use a future value `42` or runtime callback as evidence that its own solve
succeeded. The vertical has two ordered phases:

```text
Phase S (source solve): c, d_sig, q, ell, neg0, m0 and actual source-lowered
  endpoints -> insert/record the exact v1 field constraint -> propagate/check
  -> solver returns a successful candidate carrying the source identities.
Phase R (runtime): only that successful candidate authorizes execution -> the
  same source closure is passed through k -> saved suffix runs -> outer handler
  handles u_outer -> a runtime receipt matches the source/field identities in
  the candidate.
```

Neither phase proves the other. Phase R failure does not retroactively license
Phase S; Phase S success alone does not claim a runtime completion. The final
vertical evidence pairs the successful solver candidate with its matching
runtime receipt after both independently exist.

## Exact v1 constraint consumer

The consumer retains original fixed owner `c`, distinct realizer `c_outer`,
`q`, and `m0`, and identifies an exact field-bound constraint emitted during
Phase S. Its lower endpoint is the actual contribution `c_outer`; its upper
endpoint is the exact allowance for `q`, which remains indexed by `c`. `ConstraintOccurrenceId` is formed only from a real HIR occurrence
and a source owner's actual local slot; no guessed `normal_operation_slot` or `HandlerOperand` is part of this rule.
The source-owner audit must establish which actual term is the callback body's
lower computation and which allowance endpoint is indexed by `q` at the
callback result field. In particular, the operation expression path currently
emits its primitive value/effect links in `candidate_source.rs`, while its
declaration typing runs in `candidate_operation`; these facts alone do not
establish the required callback-to-field edge. Until exact endpoint and slot identities are traced
through `candidate_source.rs`, `candidate_effect.rs`, the constraint-store
API in `lib.rs`, and `shadow_apply.rs`, this is a conditional rule schema, not
a claim about an existing constraint.

Once those source terms are identified, the v1 consumer is an insertion rule:

```text
c : FixedContribution_v1(u_ping,decl)
q : LicensedField_v1(c,decl,u_ping,s1,j,outer; d_sig,d_pos,ell)
neg0 : NegativeResponsePort_v1(q,r0,v0)
m0 : SourceFieldRealization_v1(c,q,response_definition,...,c_outer,u_outer,...)
source lowering derives the real contribution lower_outer for c_outer
q supplies the exact allowance upper_q at its indexed callback result field
source typing links response_definition to q; no runtime fact is a premise
no lower endpoint is synthesized from Allowance/Permission/family equality
source audit supplies actual occurrence, slot, term types and propagation API
------------------------- NPAIR-Consume-v1
admit_and_record_v1(FieldBound_v1 { owner:c, realizer:c_outer, field:q,
                                    source_id:id_field, lower:lower_outer, upper:upper_q })
enqueue effect propagation/check for (lower_outer, upper_q)
-------------------------
consumed_v1(c,c_outer,q,m0,id_field,lower_outer,upper_q)
```

`FieldBound_v1` is an explicitly new v1 solver record. Its insertion must use the
real store/propagation API after source audit establishes exact term and
occurrence types; it must not masquerade as the repository's existing
`ConstraintOccurrence` if those indices do not fit that type. Tests/proof must
inspect the stored v1 record and propagated result. After Phase R, a separate
`RuntimeReceipt_v1(candidate_id, source_ids, c, c_outer, q, m0,
response_definition, closure, outer_event, outer_handler, final_value=42;
d_run)` is accepted only if it matches the successful candidate and actual
source trace. `consumed_v1` is never delayed
until runtime and is never a marker emitted merely because runtime returned
42. If ordinary lowering does not create the displayed endpoints/occurrence
or the exact path cannot be tied to them, this consumer rule is false and the
vertical goal is blocked at that owner.

## Pending, finite prefixes, and unchanged cases

- Before the handler commits, the complete request record, event/history,
  live state, active owners, and ordered suffix `k >>= A_decl` are preserved.
  No partial callback response is a completed output.
- The playground's `Running` and `ResourceExhausted { steps }` are finite
  observation statuses with retained machine prefix/state. Neither is
  semantic divergence or evidence of eventual return.
- Mathematical Diverged cases keep each actual finite R prefix and the same
  ordered continuation/history. This single-run machine does not decide
  infinite behavior, add eventual return, or discard a prefix.
- The new callback rule applies only after the precise q, typing, source
  closure, request match and consumer premises above hold. W, independent Z,
  alternate providers, domain changes, futures, G, nested composites and all
  original F1/FK1 quantifiers remain open.

## Review, code scope, and falsifiers

Spec review must check the recursive complete `d_sig`, positive projection,
independent license, fixed c, exact m0, allowance-only negative port,
different source occurrences for request/pattern, ordered runtime state
transitions, exact constraint insertion/propagation and every unresolved
parent case. Code remains unleased until that review and the Sol source
correspondence proof are frozen and independently checked.

After a clean design/proof gate, the conditional exact owners are
`crates/yu-solver/src/candidate_source.rs` (`preflight_catch_signature`),
`crates/yu-solver/src/candidate_effect.rs` (`candidate_catch_operation`,
`candidate_signature_effect`, stored evidence/consumer),
`tools/inference-playground/src/runtime/machine.rs` (`propagate_request`,
`Frame::ResumeArgument`, response validation), and only if needed
`tools/inference-playground/src/runtime/continuation.rs`. Focused additive
tests belong in `crates/yu-solver/tests/candidate_operation_catch.rs` and
`tools/inference-playground/tests/runtime_resume.rs`. `program.rs` and
playground `lib.rs` are read-only; Luna must add an exact follow-up lease if a
source proves wiring changes necessary. Keep baseline behavior and existing
expected outputs intact; v1 tests call the explicit v1 entry.

Falsify on wrong `c`, source row or ordinal; synthetic lower flow from
Allowance; omitted function child; response/pattern occurrence conflation;
different same-family closure or lost environment; `c`/`c_outer` conflation;
changed saved suffix or dead outer handler; 42 injected rather than executed; missing exact stored
constraint; or any cast to the old parent. No original condition closes from
this example alone. Old semantics, full NPAIR, W/Z/future transport, F1/FK1,
soundness, principality, termination and production remain OPEN.
