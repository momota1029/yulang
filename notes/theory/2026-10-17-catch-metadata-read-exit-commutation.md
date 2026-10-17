# Catch metadata read across exit: current runtime retains only a partial projection

Status: static source/consumer correspondence; no language-semantic conclusion,
independent review NOT RUN, and no code or production authority.
Sprint: `catch-raw-answer-and-metadata-read-20261017`, contract SHA-256
`16c4ea4b8bd3ace3d11b0066eb1e32955f20358d14fe94d455f516269244f800`.
Author: Luna primary, exact source correspondence lease. No tests, builds,
execution or probes.

## Question and bounded answer

The fixed 138-byte specimen has a Function-shaped operation result. The runtime
checks that response shape before continuation capture and Catch pop; it returns
`HandlerEvidence` on this branch. Thus this specimen has no selected post-exit
arm environment in which to observe metadata. No post-pop Function-response
execution or concrete specimen commutation is claimed.

The field comparison below follows the runtime data layout and the conditional
capture/pop path for sibling candidates whose response-shape check succeeds.
On those paths, the candidate's declaration/grant/payload/response checks read
pieces of `PendingRequest` while `CatchReturn` is still the top frame. Capture
then retains the continuation's code frames plus only the request declaration
and numeric event ID; the Catch frame is popped before the arm body runs. There
is no `PendingRequest`/Event operand in that body's environment through this
inspected implementation path.

Therefore the current producer/consumer path does **not** commute as a direct
projection of the same complete request record. The first absent post-exit
fields are the payload `ReceivedValue` and request `observations`/their original
execution-view evidence. In the fixed Unit-pattern specimen the payload is
not rebound: `payload=None` on the candidate side and the runtime Unit case
leaves the environment unchanged. Reconstructing these fields from an event
ID or external registry is not established by the inspected path.

This is not a source-qualified semantic counterexample to the unadopted Draft
rule. An explicit source evaluator could retain a full metadata operand across
the administrative exit, but that retention has no current runtime producer
or consumer correspondence here. The specimen-specific pre-capture refusal is
already frozen in [Catch Request-exit source/runtime instance §First broken
join](2026-10-17-catch-exit-source-runtime-instance.md#first-broken-join-for-the-specimen).
No change is proposed to the earlier active-H grant, compatibility, or
admission checks.

## Fieldwise path

For a sibling candidate whose earlier checks succeed, the inspected owner path
is `Request(PendingRequest) → propagate_request → capture_template? → pop
CatchReturn → Evaluate(selected arm)`. The fixed specimen stops inside
`propagate_request` at the Function-response guard before `capture_template`
and before `pop CatchReturn`; it has no reached selected-arm endpoint. The
following inventory describes available fields and successful sibling-path
capture behavior. Exact fields and phase changes:

| Field | Before pop at `propagate_request` | After capture/pop in selected arm | Result |
| --- | --- | --- | --- |
| Operation declaration/signature | `request.declaration`; compared with Catch arm resolution; signature supplies argument/result tags | `capture_template` clones the same `Arc<SourceOperationDeclaration>` into `ResumeTemplate` only when the arm has a continuation binder; without that binder, no template is made | Stable identity on the captured-continuation branch only; no general metadata operand in arm environment |
| Historical event identity | `request.event`; passed to `local_grant` with the active installation owner and request observations | Stored as `ResumeTemplate.original_event` only on the capture branch | The integer lineage survives capture; it is not itself an Event value or lookup proof |
| Payload value/view | `request.payload: ReceivedValue`; checked against the declared argument before pop | No payload field is stored in `ResumeTemplate`; exact Unit arm does not bind it. A variable payload arm binds it into the arm environment after pop | First structurally absent component of the full proposed historical tuple on this sibling path; fixed specimen never reaches post-pop |
| Observation/evidence vector | `request.observations: Vec<Observation>`; used by `local_grant` while the exact handler installation is active | Not copied into `ResumeTemplate`; no observation is issued after pop | No direct post-exit reference; old observations cannot be promoted to current eligibility or a fresh observation |
| Source origin | `request.source: SourceSite` | Not stored in `ResumeTemplate` | Not in the retained metadata projection |
| Saved suffix | `request.suffix`; consumed to construct ordered `TemplateNode::{Bind,Owner,View,ForwardHandler}` when continuation capture is requested | Saved frame code/handles remain in the template; original owner IDs are resolved through current control mapping on entry | Executable continuation lineage survives, but it is not a typed S/answer declaration |
| Current handler owner/eligibility | `validate_handler_installation` and `local_grant` require the active installation/current owner before commit | `self.frames.pop()` removes the `CatchReturn` delimiter; no grant is reissued | Correct phase separation; cannot be carried as active post-exit authority |

The exact runtime layouts are `PendingRequest` in
`tools/inference-playground/src/runtime/machine.rs:238–245` and `ResumeTemplate`
in `tools/inference-playground/src/runtime/continuation.rs:11–22`. The
pre-pop order is in `machine.rs::propagate_request` (`:1235–1358`): validate
installation and local grant, inspect resolved declaration/signature, check
payload primitive compatibility and continuation response shape, optionally
capture, then pop Catch and bind/evaluate the selected arm on successful paths.
The fixed specimen's Function response fails that check before capture/pop.
`capture_template`
(`machine.rs:1013–1082`) stores `request.declaration` and `request.event`, and
copies only saved suffix frames into nodes. It does not store payload,
observations or source origin.

## Relation to the Draft proposal

The target declaration proposal §3 makes `HistoricalMeta(q)` the complete
dependent Event telescope, including original declaration/instance, provider,
payload carrier, event origin and historical observation/evidence references.
Its operational clause substitutes `fields(q)` after exit without re-emission
or a global lookup. The current runtime chain above does not show that full q
operand reaching that post-exit location. `ResumeTemplate.original_event` and
`.declaration` account for only two references; the continuation template
accounts for saved executable frames. The fixed Unit case also has no actual
payload binder that could retain the missing payload in lexical environment.
For the fixed Function-response specimen, however, this is an un-reached
post-exit limitation: the earlier response-shape guard returns before capture
and pop. The field-loss comparison is structural evidence from successful
primitive-response sibling paths only.

Consequently the only supported alignment is partial:

```text
pre-pop declaration + event lineage  --capture branch-->  template declaration + original_event
pre-pop payload + observations + source  ---------------->  no same-record post-pop consumer found
pre-pop saved suffix  ----------------------------capture-->  ordered executable template nodes
```

The newly proposed metadata elimination could close this interface gap only
after its source evaluator and runtime representation/consumer are specified
and independently reviewed. It must preserve the original event and its
historical evidence without reviving H, interpreting old receipt evidence as
current, or issuing a new Observe. This note does not author such a runtime
change and does not decide whether the Draft source rule should be adopted.

## Parent and implementation application

This narrows the source/implementation bridge for `CATCH-EXIT-INPUT-1/M_exit`:
the event/declaration pair is partially retained, while the exact current
runtime does not carry a complete historical operand to the outside matcher.
It supplies no typed `M_exit`, full raw descriptor, payload/Receive map, or
general preservation. Original FORWARD-FIRST-CALL A/B, F1/FK1, adopted
MI-Intro, source acceptance, native correspondence and production remain OPEN.

No compiler code, test, expected output, semantic assertion, fixture or public
surface changed. No execution result is claimed. The exact next step is a
reviewed decision about the Draft metadata operand's source/runtime carrier,
after consuming the independent ApplyOne proof review and this note's own
review. Only a separately authorized, precisely leased provisional
instrumentation slice could test that carrier; this packet itself contains no
safe code slice.
