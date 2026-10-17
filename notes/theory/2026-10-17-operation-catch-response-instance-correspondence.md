# Operation-to-Catch response instance correspondence map

Status: static source/native correspondence artifact; no implementation or
semantic adoption. Sprint `operation-response-signature-introduction-20261017`,
contract rev2 SHA-256
`88d4d24eff0fd69054643ff86176fc75abcd04d403256b80de8951276e7ea74a`.
Baseline/checkpoint `e71b38928`; exact dependency pins reverified. This audit
is independent of the unadopted response-rule proposal: it does not use its
clauses as source evidence.

## 1. Source declaration identity

Pinned `source_annotation.rs` defines
`SourceOperationId = (family: SourceEffectId, declaration: SourceNodeKey)`.
A `SourceOperationDeclaration` retains that id, spelling, visibility, name and
signature source positions, range, and parsed `SourceAnnotationType`. The
signature contains optional effects, a value tree and row variables as names.
This is declaration syntax plus stable source identity; it contains no
instantiation witness or semantic `D_B/P_B` certificate.

A resolved source occurrence retains `Arc<SourceOperationDeclaration>`. The
operation-value expression and Catch operation pattern therefore carry the
same declaration identity when resolution names the same declaration. Their
use owners and occurrences remain separate: candidate source records the
operation expression occurrence for `Action::Operation`, while
`Action::CatchOperation` records the arm-body occurrence, payload/continuation
binder endpoints, the original scrutinee endpoint, and its effect endpoint.
Declaration identity is not use identity or dynamic request identity.

## 2. Static operation value path

For an actual `LocalSourceForm::Operation`, `Work::Finish` emits the operation
expression's ordinary immediate pure-effect constraints and queues
`Action::Operation { declaration, owner, occurrence, target, level }`.
`candidate_operation` creates fresh local `values`, `effects`, and `views` maps,
then calls `candidate_signature_value` on the whole declaration signature at
positive polarity and links the resulting term to the occurrence's value
component (slot 42).

`candidate_signature_value` recursively preserves Function variance and
argument/result positions. A `Variable(name)` obtains/reuses one fresh solver
coordinate by name **within that call's map**. Row variables are likewise
mapped within the call. For the root Operation Function only, the family is
injected into the declared result's effect port when that port has no explicit
row. The operation expression itself is pure; family support is not copied to
every nested Function.

The maps are local temporaries and are dropped after constraint generation.
The generated value/effect relations remain, but this action does not retain a
named, complete declaration substitution `theta` or a dependent semantic
response record.

## 3. Static Catch continuation path

For a resolved operation pattern, the source walk retains the same declaration
Arc. It records an actual payload endpoint only for a payload binder and an
actual continuation endpoint only for a continuation binder. It queues
`Action::CatchOperation` with the original scrutinee value endpoint and its
effect endpoint. Wildcards create no binder endpoint.

`candidate_catch_operation` allocates a second fresh set of local
`values/effects/views` maps. If a payload binder exists, slots 60/61 connect the
argument signature at both polarities to that binder. If a continuation binder
exists, it constructs the declared result at both polarities and forms a
Function whose argument is that response and whose result is the **original
scrutinee value endpoint**; slots 62/63 link both directions. Slots 64/65 carry
entry and whole-scrutinee effect bounds into the provisional continuation
interface. The handler is not reinstalled by these constraints.

The exact partial joins are therefore:

```text
same resolved SourceOperationDeclaration
  ├─ Operation expression -> candidate_signature_value -> slot 42 -> expression value
  └─ Catch pattern -> candidate_signature_value(result) -> slots 62/63 -> continuation endpoint
                                                    continuation result -> original scrutinee endpoint
```

The declaration and structural signature positions are shared. The local
`values/effects/views` maps are separately allocated and discarded in the two
calls. The source inspected here does not construct or retain one shared
`theta` relating both generated maps and all dependent profile/observation
fields. Resulting solver constraints may relate particular endpoints; that
fact is not a proof that they are the complete same operation instance or that
all original dependent fields were transported.

## 4. Runtime response path

`machine::execute` creates a `PendingRequest` containing the declaration Arc,
actual payload value, source site, event, observations and growing saved suffix.
`capture_template` on supported paths retains the declaration and original
event lineage in `ResumeTemplate`; it retains executable suffix nodes. These
are construction and lineage joins, not a typed instance packet. The fixed
Function-response Catch specimen fails its response-shape guard before
capture/pop, so it has no reached `ResumeArgument` consumer.

For supported primitive paths, resumption pushes `Frame::ResumeArgument`.
`return_value` reads the template declaration's result annotation and accepts
only a matching primitive response before entering the saved template. This
checks a concrete runtime value against a primitive shape. It does not consume
solver `theta`, profile coordinates, contextual challenge evidence, original
`D_B/P_B`, arbitrary Function response observations, or output-dependent
futures.

Thus the actual runtime lineage join is:

```text
resolved declaration + payload + event + observations + suffix
  -> PendingRequest -> (supported capture) ResumeTemplate(declaration,event,suffix)
  -> ResumeArgument primitive response-shape check -> saved suffix execution
```

It is conditional on reaching a supported capture path. It does not give a
post-pop consumer for the fixed Function case and does not prove a source rule.

## 5. First missing correspondence and parent use

The first precise missing join is an explicit, same-use substitution/instance
witness connecting the source declaration's scoped binders to (a) the
independently generated static Operation signature coordinates, (b) the Catch
payload/result/continuation ports, and (c) the dynamic request/resume lineage,
while transporting all dependent observations, worlds, profiles and future
interfaces. The code retains declaration identity and several structural
endpoints but no such complete object. In particular, matching family IDs or
arrows and linking a response endpoint cannot recover local operation binders
or establish that an arbitrary response tuple is admitted.

This is a missing source/native correspondence result for the audited owners,
not proof that the compiler cannot construct one elsewhere. It is also not a
compiler bug finding: static constraint relations, broader inference lifecycle,
and all possible post-lowering enrichments were not exhaustively audited. The
contract forbids a repeated global census. No code path was modified.

Application: the new source-rule proposal's `OPRESP-DEFAULT-1` and
`OPRESP-DOMAIN-1` remain open; this map cannot close either. The original
checked `d_B(τ)` is still absent. B remains separate from the continuation's
result port / S-answer `A_S`. Original A/B, F1/FK1, `M_exit`, source/native
acceptance, implementation and production stay OPEN.

## 6. Evidence and boundary

Inspected the exact pinned owners: `SourceOperationDeclaration` and
`SourceAnnotationType`; operation and Catch action planning; candidate
signature recursion and the operation-specific family injection; runtime
`PendingRequest`, `ResumeTemplate`, `Frame::ResumeArgument`, primitive response
check and Function-response pre-capture refusal. Relevant meanings were kept
at their pinned authority: operation-instance binding package is a reviewed
Draft (not an adopted inference rule); contextual Function membership and
Call semantic-input formation are selected definitions with independent
inputs; source contracts/common allowance is conditional and does not itself
instantiate this declaration's complete B.

Checks: static source reading and SHA-256 only. No tests, builds, runtime,
probes, code, expected-output changes, or Git by this author. No descendant or
scratch file.
