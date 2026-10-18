# R68 Luna retained-entry Lambda source/native owner map

Status: bounded owner map for the R68 retained-entry introduction attempt.
It supplies no source Lambda membership rule and authorizes no code slice.
Contract: `tasks/agent-loop/sprints/retained-lambda-introduction-20261019-r68.md`,
revision 1, SHA-256 `04070e85b4ee10fa308954916653955aee761f8fa59b937ea6cf78349901cd14`.

Owner: `/root` (Luna/high), session `current-conversation-2026-10-19-r68`.
Exact leases: this note and `tasks/agent-loop/inbox/20261019-r68-implementation.md`.
Grant: 500 seconds reserved/charged. Actual elapsed, CPU and RSS UNKNOWN.
Only static reads/hashes; no compiler, tests, builds, probes, instrumentation,
measurements, production changes or Git by the owner-map lane.

## Original source and source owners

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Pinned HIR keeps the source header annotation and expression annotations as
different owners (`source_annotation.rs:317–357`), with Function argument
and result occurrences distinct (`:68–96,342–390`). The source-local HIR keeps
the original `forward` Lambda, its annotated formal `t`, resolved body
`Name(t)`, and the whole-binding annotation at separate occurrences
(`local_source.rs:267–274,348–365,591–628,714–720`). The formal Name resolves to
the actual parameter binding; it is not a fresh module lookup or a new carrier.
R67's frozen owner map records the finer source occurrence/capture inventory
and remains pinned in this packet.

The source Generalize Lambda constructor requires actual role/entry, original
captures, checking the body under that actual formal binding, a designated
consumer, and complete invocation evidence
(`source-generalize-definition-and-proof.md:140–156`). Its Function-check and
final annotation rules consume an already formed interface and completed
operand (`:176–190`). These are the source owners of the body/consumer gap;
the structural existence of the Lambda and its `Name(t)` child does not derive
the callable's semantic Function membership.

The selected source-input grammar makes the consumer obligation explicit:
`Data-Name` retains a resolved binding, while `Code-Consumer` additionally
requires `ConsumerOrigin(d,p,Comp(E_t,Int),profile,K,D,scope)` at an actual
designated port (`call-input-construction-proof.md:154–175`).
`Code-NameValue` uses `Data-Name` followed by `Code-Result`; the distinct
`Code-NameRetained` uses `Data-Name` followed by `Code-Consumer`
(`:193–195`). The fixed formal is retained computation entry, so Name lookup
and carrier identity alone do not establish that this body has the latter
consumer origin. R68 must show that the authentic Lambda/body/invocation rule
supplies the source body port and consumer, or stop at this exact local
premise. It cannot silently treat lookup as Force/consumer or change retained
entry into Value entry.

## Selected source construction and semantic input owners

The selected source-interface construction takes an actual finite resolved
source derivation plus authentic complete operation contracts. Its §5
constructors retain registration/Name/capture, producer entry, Lambda body,
Bind, Call and designated-consumer interfaces; Theorem IF in §6 emits the
structural Call frame and inclusion maps. The theorem is static formation,
even when generated constraints have no satisfying assignment. It expressly
does not turn its slots into semantic challenge admission, actual-provider
acceptance or body observation membership. This gives the proof a candidate
typed structural input, not the missing Lambda introduction.

Contextual Function membership requires the same actual callable/provider to
accept every independently admitted complete challenge and satisfy every
complete or pending observation at the original joint coordinates
(`contextual-function-membership-definition.md:44–100`; its selected
realization is `call-semantic-input-realization.md:149–234`). That semantic
input theorem eliminates membership of an already genuine callable; it does
not introduce membership for the newly constructed `forward` closure. Its
challenge formation is independent of actual-U acceptance, so a proof cannot
choose only challenges the candidate Lambda happens to accept. It must prove
acceptance and observations at those same independently formed inputs.

The selected positive immutable root introduction is a different, exact
two-closure mutually recursive theorem (`simultaneous-immutable-root-introduction.md:1–35`).
It does not apply to the ordinary nonrecursive `forward` definition or supply
a general retained-entry Lambda rule. No source restriction, new semantic
clause or fixed-point interpretation is selected here.

## Candidate/native route and invariant boundary

The pinned candidate collector preserves source formal registration and
separate `FormalEntry`/`FormalAnnotation` actions (`candidate_source.rs:296–302,992–1023`).
For resolved computation-formal `Name(t)`, it records a formal Name effect
action tied to that registration (`:1210–1230,1661–1665`). At the Lambda
occurrence it queues a native `LambdaRecipe` containing the source occurrence,
formal registration/position, root component, body endpoint and effect
components (`:1403–1425`); the action dispatches `admit_lambda_fact` at
`:1679`. At the definition boundary it separately schedules the whole
annotation against the body endpoint and definition component (`:1450–1468`).
These are native construction inputs and endpoints. They do not carry a proof
that independently admitted source challenges are accepted by this actual
callable or that all invocation/pending observations meet the source Function
contract.

`shadow_apply.rs:401–421` preflights before candidate collection. The pinned
candidate preflight rejects negative concrete argument rows through
Function polarity (`candidate_source.rs:455–465,603–617`), and the signature
constructor independently refuses that case (`candidate_effect.rs:1930–1935`).
Both `p_A` guards remain unchanged. Neither guard establishes the source
program's validity or invalidity.

The R68 source/consumer map stops at the pinned action call site. The native
Lambda consumer implementation is outside the exact 30-pin manifest; it was
not inspected in this lane. The previous R67 disclosure records an earlier
broad search returning a symbol locator in unpinned `lib.rs`; that body was not
read or used. No source/native correspondence is inferred from either locator.

## Decision and retained obligations

The proof lane must show that the retained formal stores the exact incoming
whole carrier at `t`, that `Name(t)` consumes or returns that carrier at its
actual source port, and that the actual Lambda invocation/result relation
preserves it for all independent challenges, including pending prefixes and
future-provider contracts. The result must then be related to the written
Function interface before the whole annotation can consume it. All original
provider, captures, open `E_t`, `p_t/p_A/p_R`, formal-only permission,
ordinary constraints, local scopes and typed substitutions stay in one joint
context.

The owner map identifies no pinned source constructor that itself proves this
new closure membership. **`NO_SAFE_CODE_SLICE`**: changing Lambda recipe
construction, its consumer, or either negative-`p_A` guard would encode or
promote an unproved source premise. Parent and A/B remain OPEN at `0→0`; R65,
R66 and R67 supplier obligations, R64/R61 and R50 statuses are unchanged.

No global-absence, source-counterexample, ambiguity, or theorem conclusion
follows from this bounded map.
