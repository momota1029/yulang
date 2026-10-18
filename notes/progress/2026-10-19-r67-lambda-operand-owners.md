# R67 Luna direct Lambda operand owner map

Status: bounded source/native owner map. This map does not establish the
missing direct Lambda/body-check source rule and authorizes no compiler slice.
Contract and direct dependency manifest are in
`tasks/agent-loop/sprints/direct-lambda-checking-20261019-r67.md`.

Owner: `/root` (Luna/high), session `current-conversation-2026-10-19-r67`.
Exact leases: this note and `tasks/agent-loop/inbox/20261019-r67-implementation.md`.
Grant: 500 seconds. Runtime/model observations beyond the configured role are
UNKNOWN. Static reads and hashing only; no tests, builds, compiler execution,
probes, instrumentation or measurements.

## Fixed source and source owners

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The pinned `source_annotation.rs:317–357` keeps a header annotation and an
expression `as` annotation as separate constructors. Both retain source-root
owner, annotation position and parsed type; the function type keeps distinct
argument and result occurrences (`:68–96,342–390`). In
`local_source.rs:267–274,348–365,591–628,714–720`, the original Lambda,
formal `t`, body expression and whole-binding annotation remain separately
owned. The direct body `Name(t)` keeps its resolved parameter binding. This
forms the source occurrence inventory, not a completed `D_s` Function
interface or body-checking judgment.

The governing source grammar requires the authentic role/entry, original
captures, body checking under the actual formal binding, body consumer and
complete invocation (`source-generalize-definition-and-proof.md:140–156`).
Its Function checking constructor consumes independently formed domain and
observation obligations, while final Annotation checking consumes an actual
completed operand (`:158–190`). These are the source owners for the missing
`R67-DIRECT-BODY-CHECK-1` evidence. Merely selecting the Lambda constructor
does not form its independently admitted challenge or body target.

## Current candidate/native route

For the annotated formal, the pinned `candidate_source.rs:992–1023` records
the actual formal position and queues separate `FormalEntry` and
`FormalAnnotation` actions at the formal occurrence/scope. In the body Name
case, it recognizes the resolved computation formal and queues
`FormalNameEffect` (`:1210–1230`); execution relates the Name effect component
to that formal registration's entry effect (`:1661–1665`). The selected
Name/permission construction is also pinned in
`computation-formal-permission-construction.md`; it grants local permission
at the formal annotation and does not cap open `E_t` or transfer permission
to `p_A`.

The Lambda visitor builds a native recipe from the Lambda occurrence, actual
formal registration/position, Lambda root, body value endpoint, and body and
Lambda effect components (`candidate_source.rs:1403–1425`). Its queued action
passes that recipe to the candidate Lambda consumer (`:1679`). The pinned
call-site input is a collection of native endpoints/registration identifiers;
it is not the source proof of an independently admitted challenge, body
checking target, designated semantic consumer, or complete invocation
required by the source grammar. This call-site observation does not promote
the candidate construction into source evidence.

For the whole annotation, collection separately queues an `Annotation` action
on the body endpoint and definition component target
(`candidate_source.rs:1450–1468`). `shadow_apply.rs:401–421` performs
preflight before candidate collection. Root whole-annotation preflight rejects
negative concrete rows and recursively flips polarity through Function
arguments (`candidate_source.rs:455–465,603–617`); the signature constructor
has its own negative-concrete refusal (`candidate_effect.rs:1930–1935`). For
the fixed positive-root Function annotation, argument row `p_A=[io]` is
negative. Both native guards remain unchanged and neither refusal decides the
source program's semantic validity.

## Owner boundary and code decision

The source Lambda checking rule is the owner that must supply the challenge,
body-check target and consumer before an operand can be passed to the
whole-annotation boundary. The pinned candidate collector instead passes a
native Lambda recipe; the whole annotation consumer receives an endpoint,
annotation and definition target. No pinned interface at this seam transports
the required source proof or establishes the same joint source assignments.
That is consistent with the proof and counter-reading's exact premise
`R67-DIRECT-BODY-CHECK-1`.

**Decision: `NO_SAFE_CODE_SLICE`.** Changing Lambda recipe creation, adding a
body target, or weakening either negative-`p_A` guard would introduce or
promote unproved source evidence. The current owner map identifies the source
owner and native call site but does not prove their correspondence. Any
additional entry/consumer/invocation authority outside R67's 34-file manifest
returns to Luna before inspection or use.

The map is limited to the fixed source and exact pinned owners. It proves no
global absence, source counterexample, ambiguity, parent closure or production
correspondence. `R67-DIRECT-BODY-CHECK-1`, `R65-CURRENT-OPERAND-1`,
`R66-LAMBDA-RESULT-STAGE-1`, downstream R64/R61 and the parent remain OPEN;
Simple-sub A/B remain OPEN at `0→0`; R50 remains NOT ADOPTED.

## Read-boundary receipt

While locating the pinned caller, a broad symbol-name search also returned a
match in an unpinned source file. I did not inspect that file's body, use that
match as a premise, or include it in this map's source evidence. Every owner
claim above is supported by the R67 pinned source files and selected source
rules only. If the consumer implementation itself becomes necessary, Luna
must first reconcile a new exact dependency and review snapshot.
