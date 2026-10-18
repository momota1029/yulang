# R66 Luna source/native owner map

Status: bounded static owner map for R66; no compiler change or source-rule
derivation. The exact contract and its 26 direct dependencies are frozen in
`tasks/agent-loop/sprints/lambda-boundary-staging-20261019-r66.md`.

Owner: `/root` (Luna/high), session `current-conversation-2026-10-19-r66`.
Exact leases: this note and `tasks/agent-loop/inbox/20261019-r66-implementation.md`.
Grant: 500 seconds. Requested and observed runtime/model details beyond the
configured role are UNKNOWN. Static source/document reads only; no tests,
builds, compiler execution, probes, instrumentation or measurements.

## Fixed source and HIR ownership

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

`source_annotation.rs:317–357` has distinct header-binding and expression-
`as` constructors. Both retain a `SourceAnnotation` with its `SourceRootId`,
source position and parsed annotation type; `SourceAnnotationType::Function`
keeps separate argument and result children (`:68–96,342–358,364–390`).
Consequently the formal `p_t` and whole-binding `p_A/p_R` are separate source
occurrences even when concrete row contents coincide. The HIR stores syntax
and ownership here; this storage does not itself establish a typed source
judgment or permitted source solutions.

`local_source.rs:267–274,348–365` represents an expression ascription, Lambda
with its formal parameter/body, and binding with its initializer/optional
annotation as distinct nodes. During definition projection (`:591–628`), the
formal annotation is parsed at the actual formal and its scope; the body Name
is resolved through the lexical binding builder. The definition header
annotation is separately retained at `:714–720`. This preserves the original
Lambda/formal/Name and annotation owners needed by the R66 question; it does not
construct a completed symbolic Lambda operand under the whole binding's joint
context.

## Candidate source construction and consumers

For a Lambda formal, `candidate_source.rs:992–1023` records the formal position
and queues its own `FormalEntry` (when the annotation has an effect row) and
`FormalAnnotation` actions, retaining the formal occurrence and formal scope.
The `Lambda` visitor creates its own recipe from the original formal
registration, Lambda root, body endpoint and body/Lambda effect components
(`:1403–1425`); execution later sends that recipe to `admit_lambda_fact`
(`:1679`). A body parameter Name is registered against that same formal
(`:925–931`), with its effect action routed through `FormalNameEffect`
(`:1229,1663–1665`). These
native endpoints/facts are not a source proof that the annotated Lambda can be
first synthesized independently, nor evidence that its solution set equals
the original whole-binding rule.

For the annotated whole definition, collection queues the final `Annotation`
action on the body's endpoint and the definition component target
(`candidate_source.rs:1448–1468`). The action consumer is
`candidate_effect.rs:1605–1617,1627–1699`: it constructs the negative checking
and positive exposed signature in one annotation context, links the actual
body endpoint to the checking side at slot 40, handles the annotation's
computation effect at slot 42 when present, then links the exposed side to the
definition target at slot 41. The body endpoint and target are already inputs
to this consumer. This describes the current candidate route; those native
links do not prove source-level staging equivalence, typed substitutions, or
solution lifting/reversal.

The owner where a staged proof object could be consumed would be the
source-owned binding/definition formation before this candidate endpoint
consumer. The pinned HIR owner retains the needed syntax identities but offers
no staged-source-evidence field. The pinned candidate consumer accepts native
endpoints and generates native constraints; it is not a constructor for the
missing source evidence. Thus the owner map locates a seam, not an authorized
code slice.

## Reachability guard and implementation decision

`shadow_apply.rs:401–421` runs local-source preflight before candidate
collection. Root whole annotations are checked at
`candidate_source.rs:455–465,603–617`; negative polarity rejects a nonempty
concrete row. For the fixed whole Function annotation, the root is positive,
its Function argument is negative, and concrete `[io]` therefore fails this
candidate preflight. The signature constructor has an independent negative
concrete-row refusal at `candidate_effect.rs:1930–1935`. Both guards remain
intact. Neither refusal says the source program is semantically invalid.

The selected source-result rule A applies to an **unannotated function
result** (`notes/design/2026-10-02-source-result-synthesis-choice.md:7–26`);
it cannot by itself supply the Lambda synthesis premise in this explicitly
whole-annotated binding. The generalize/source-checking definition retains the
actual completed source root, annotation target and prior evidence at their
owning boundary (`notes/design/2026-10-08-source-generalize-definition.md:58–75`;
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md:44–67`).
The approved typed-root bridge consumes a completed operand endpoint and prior
evidence; it assigns those to the source owner rather than constructing them
(`questions/2026-10-10-source-annotation-typed-root-bridge/approved-answer.md:35–41`).
Formal permission is local to the authentic formal and does not cap incoming
effects or migrate to `p_A` (`notes/theory/2026-10-15-computation-formal-permission-construction.md:38–51`).

**Decision: `NO_SAFE_CODE_SLICE`.** The inspected owners show where HIR stores
the original operands and where native checking consumes their eventual
endpoint. They do not provide the source derivation R66 is testing, its joint
solution equivalence, or typed witness transport. Editing candidate collection
or relaxing either negative-`p_A` guard would cross from a bounded native
construction into an unproved source/semantic change. No compiler, test,
expected-output, semantic or production change is justified by this map.

This result is limited to the fixed source and the exact pinned owners in the
R66 contract. It establishes no global absence, ambiguity, source
counterexample, theorem closure or production correspondence. Apply the proof
and counter-reading results to the original `R65-CURRENT-OPERAND-1`; R64 and
R61 and Simple-sub A/B remain OPEN, closure `0→0`, and R50 remains NOT ADOPTED.
