# Operation v1 source field bound — revision 6

This is a Luna design after r4 falsified the claim that existing code already emits the needed consumer and the r5 independent review found that the response argument was not linked to the matching handler continuation. It adds one explicitly versioned, research-only solver constructor and propagation edge. It does not close the unchanged parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, does not claim old `At(c,...)`, and does not authorize production.

## Fixed source identity

Use the candidate source from r4: `ping: () -> (int -> [outer] int)`, source callback `response (x:int): [outer]int = outer::next()`, inner handler `k -> k response`, and an outer handler whose `outer::next()` arm returns `42`.

There are distinct identities:

- `c`: v1 owner at the actual `signal::ping()` source request occurrence `u_ping`, fixed before any handler/runtime choice. It matches the prior r16/r17 interpretation of original fixed-c formation.
- `q`: complete typed signature evidence and independent source license for the positive Written operand `outer` at `s1 = Operation.Function.ResultValue.Function.ResultEffect`, `j=0`, owned by `(c,u_ping,decl)`.
- `c_outer`: a separate callback-body realizer, fixed to the actual source operation application/use `u_outer` inside `response`. It is never equated with `c` or a native `Contribution` index.
- `p_ping` and `p_outer`, native view/member indices, local constraint IDs, and dynamic runtime events are all distinct identities.

## New typed source constructors

The source prepass and inference path must produce:

```text
c : OperationOwnerV1 { request_use:u_ping, declaration:ping }
d_sig : CompleteSourceSignatureV1(ping, Sigma_theta)
d_pos : PositiveWrittenProjectionV1(d_sig, s1, j=0, outer)
ell : SourceFieldLicenseV1(d_sig, d_pos, declaration_scope)
h_arg : HandlerContinuationArgumentV1 {
       owner:c, request:u_ping, catch_occurrence:u_catch,
       arm_source:matching_arm, declaration:decl, continuation_binder:k,
       apply_occurrence:u_k_response, callee_resolution:CatchBinder(k),
       argument_occurrence:u_response_arg,
       argument_resolution:Definition(response_definition) }
q : LicensedOperationFieldV1(c, d_sig, d_pos, ell, handler_argument:h_arg)
neg0 : NegativeResponsePortV1(q, allowance_view:v_q, tail=None)

c_outer : CallbackRealizerV1 { response_definition, u_outer, source_apply }
m0 : CallbackFieldRealizationV1 {
       owner:c, field:q, handler_argument:h_arg,
       source_definition:response_definition,
       complete_response_type_derivation,
       body_lower:actual_native_member, realizer:c_outer }
```

`CompleteSourceSignatureV1` recursively validates the entire declaration `SourceAnnotationType`, resolves every row member, retains all path/position/telescope/binder data, and only then projects `d_pos`. `q` packages `c`, the request occurrence, declaration, exact typed/license derivations, and the same `h_arg`; neither shape lookup nor family equality creates it. The declaration and callback response annotations are separate source objects. `h_arg` is constructed only from one retained local-source derivation: the exact `u_ping` operation node lies in the scrutinee subtree of `u_catch`; the selected arm has the same resolved declaration `decl`; its continuation pattern introduces binder ID `k`; the `k response` Apply has a callee Name whose `LocalSourceResolution` is exactly `CatchBinder(k)`; and its argument Name resolves to the exact response definition identity. The Apply callee and argument are taken from that Apply's child indices and retained occurrences, not from spelling, type, or family equality. The response definition body is then followed to `u_outer`. If any edge is absent, ambiguous, or crosses source roots, no `h_arg`, `m0`, q-owned field, or `FieldBoundV1` is emitted.

`m0` proves the linked source definition's complete function type has the same field at the corresponding result path and that its body operation lowers to the exact native member recorded in `c_outer`; it retains `h_arg` and does not assert `c=c_outer`. The fixed specimen uses a direct named response argument; this versioned research constructor is partial on source forms for which the exact resolved path is unavailable, while the original theorem's source domain and quantifiers remain untouched and open.

The q-aware preflight must receive or retrieve the same source-local evidence keyed by `u_ping` and the matching declaration. The handler pattern `p_ping` is used only to check declaration matching; it is never substituted for `u_ping`. Missing or ambiguous q leaves the current `Unsupported` behavior intact.

For the negative callback port, construct a fresh effect row and a q-indexed native allowance view `v_q` with exactly `[outer]`, no tail. The nested `Function` traversal checks every argument and result child at its existing variance. This rule accepts only the exact typed positive `q`; it does not relax arbitrary negative concrete rows. The allowance produces no lower endpoint or dynamic request.

## Native lower realizer and exact consumer

The current effect algebra already has an actual `AnnotationMember(view,j)` lower endpoint and an `Allowance(view)` upper endpoint, and its typed drain checks these endpoint kinds. R4 established that operation-family Support decomposes into an `AnnotationMember`; it is not a native `Contribution`. Therefore the v1 realizer record explicitly links source `c_outer/u_outer` to that actual member, preserving its family, view and member ordinal. It never renames/casts the member to `Contribution`.

Construct a q-owned upper view `v_q` for the exact callback result field. Add a v1 record in the candidate effect state:

```text
FieldBoundV1Id(n)
FieldBoundV1 {
  id: FieldBoundV1Id(n),
  source_occurrence: actual callback-body Apply occurrence,
  source_slot: dedicated V1 field-bound slot allocated by this producer,
  owner: c,
  realizer: c_outer,
  field: q,
  lower: AnnotationMember(actual_body_view, actual_member_ordinal),
  upper: Allowance(v_q),
  derivation: m0,
}
```

The producer checks that the member and allowance resolve to the same written family, but stores the distinct proof identities. The dedicated slot is introduced by this v1 producer and must be collision-checked against all existing slots for that actual HIR occurrence; it is not an existing or guessed `normal_operation_slot`. The record carries enough information to audit the exact source occurrence, native endpoints and field owner.

After storing the record transactionally, call the existing typed constraint API on these actual native endpoints (`constrain_live_effect` / `enqueue_task`), using a matching source occurrence/cause for diagnostics, then run the ordinary candidate typed drain. Do not convert native endpoints to `Term`, manufacture a `ConstraintOccurrence` with ill-sorted operands, or skip the drain. `FieldBoundV1` is the versioned evidence record; `consumed_v1` is returned only after its exact task drains successfully. A conflict or resource error returns no successful consumer receipt and rolls back the record and edge together.

`candidate_check_effect_operand(AnnotationMember, Allowance)` supplies the native membership/check rule. Its successful family membership does not itself prove `q`, `m0`, `c_outer`, source occurrence or field license; those remain stored in `FieldBoundV1`. No Permission/Allowance-to-lower conversion, old Contrib/Inc/Cover cast, `c=c_outer`, or `AnnotationMember=Contribution` is permitted.

## Phase boundary and present sprint outcome

This revision's implementation outcome is the static Phase-S vertical only:

```text
same source -> c/q/license/neg0/h_arg/m0/c_outer -> stored FieldBoundV1
  -> exact AnnotationMember <: q-Allowance task -> ordinary drain -> consumed_v1
```

Solver runs before runtime. No `d_run`, closure environment, returned `42`, or runtime event is an input to source admission, `q`, `m0`, or `FieldBoundV1`. Phase R remains the next goal seam: retain the successful candidate/certificate across `execute`/`RuntimeProgram`, validate the actual source closure through captured continuation, preserve the saved suffix and live outer handler, then attach a matching runtime receipt. r4 showed current playground `execute` discards its candidate and `from_hir` receives no proof evidence; this sprint does not write playground wiring/runtime owners.

## Implementation owners and exact gates

After clean independent design/proof review, the bounded implementation owners are:

- `crates/yu-solver/src/candidate_source.rs`: build same-source field/license evidence and q-aware negative preflight; preserve Unsupported outside the exact rule.
- `crates/yu-solver/src/candidate_effect.rs`: q-owned allowance view, callback realizer mapping, `FieldBoundV1` transactional storage and native effect task/drain.
- `crates/yu-solver/src/shadow_apply.rs`: if the ordinary apply recipe is the only owner exposing the actual callback-body `AnnotationMember`, add narrowly scoped v1 metadata/observation there. No generic endpoint rewrite.
- `crates/yu-solver/tests/candidate_operation_catch.rs`: additive source-driven tests of exact `c`, `q`, `c_outer`, stored field bound, exact endpoints and drained result; negative controls vary occurrence/ordinal/family and ensure no lower from allowance.

`crates/yu-solver/src/lib.rs`, `candidate_scheme.rs`, and all playground/runtime owners are read-only in this packet. If source inspection proves an exact change there is required, freeze the reason and exact functions; Luna issues a follow-up lease before writing. Existing expected outputs are protected. Do not change production entry behavior; new acceptance is behind an explicit v1 research entry.

Fresh spec review checks the constructor indices, complete signature recursion, no hidden Sigma coordinates, same-request q, exact source application/argument path h_arg, matching declaration and continuation binder identity, lower member origin, upper view origin, m0 linkage, source slot uniqueness, transaction rollback and no endpoint cast. After implementation, a separate compiler referee inspects exact code and tests before a focused solver test run. Tests must parse and infer the whole source; they cannot inject q, member, allowance, lower, source slot, or bound record.

## Falsifiers and unchanged parent cases

Falsify if changing `u_ping` changes no owner identity; changing `u_outer` leaves the same realizer; another same-family member can replace the actual callback lower; the upper is not q-owned; the q carries a different declaration/path/ordinal/license; the dedicated source slot collides; a lower appears from Allowance; FieldBound storage survives failed propagation; endpoint kinds are cast; or `consumed_v1` is reported before typed drain. A decisive source-linkage falsifier changes `k response` to `k other_response` while retaining the old response body/type/family: the old response definition must no longer appear in h_arg, m0, or FieldBoundV1. A distinct callback is not rejected merely for being different; it must be the argument actually resolved at that application.

This local constructor establishes no original universal condition. W, independent Z, alternate providers, domain changes, futures, G, nested composites, whole-use transport, all original F1/FK1 quantifiers, soundness, principality, termination, runtime Phase R, full NPAIR and production remain OPEN. Pending/history/live state and ordered continuation rules remain as in the frozen r4 specification; this static source test is not evidence of runtime completion or Diverged behavior.
