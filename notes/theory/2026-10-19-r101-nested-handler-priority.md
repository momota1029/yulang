# R101 conditional nested handler construction

Status: **frozen candidate derivation; exact new-source entry unresolved; fresh review pending Luna**.
Assignment `R101-PROOF`, revision 1; sole author `/root/r101_nested_handler_proof`.
Contract revision 2: `tasks/agent-loop/sprints/nested-handler-priority-20261019-r101-rev2.md`,
SHA-256 `e8ba3e6280a3ee5d88881160de2bb8681b66c730a003e2c49e5c8bd94609946a`.

## Parent and result

The finite parent is the contract's three-cell source/runtime prediction for nested
ordered Catch selection and a selected arm's fresh shallow request. The broader
effect-hygiene parent preserves provider, annotation, receiver, request, residual
and witness lineages under the joint assignment `(nu,K,D)`. Its original universal
source and continuation quantifiers, F1/FK1, native residual correspondence,
Simple-sub soundness/principality and evaluator obligations remain OPEN.

Given the explicit source-entry premise below, the pinned LocalSource,
RuntimeProgram, receiving and machine constructors derive the three predicted
outcomes: integer 11, integer 23, and an outward tick request carrying integer 11
whose SourceSite belongs to the inner arm's Apply. This is a conditional
construction, not a source-qualified theorem or an observed runnable result.
The exact nested source-to-CST/admission premise has not been discharged.

The charter is reviewed research direction without implementation authority.
The ordinary-computation package is expressly Draft candidate source rules;
its ordered current-configuration and shallow-arm rules (§§4–5) motivate this
finite audit, without promoting its adequacy/principality. No Simple-sub
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
or generalization rule is changed. R85 adoption, R100-ENTRY/P2/P3/P4 and all six
broader effect-hygiene fronts remain separate and open.

## Exact cells and remaining source-entry premise

Cell A, exact source:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::tick 7))
```

Cell B swaps only the complete two inner arms; all remaining bytes are the same:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 23, io::tick(p), _ -> io::tick 11 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::tick 7))
```

Cell C starts from A and replaces only `tick` with `other` in the outer operation
pattern; the declarations, inner arms and main remain byte-identical:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23 }
my outer (thunk:[io] int) = catch thunk { io::other(p), _ -> p }
my main = outer (inner (io::tick 7))
```

`ENTRY` is the following unproved premise for each exact cell separately:

1. The public shared-SourceText header/parse/lower route emits diagnostic-free
   authentic CST and admitted roots for these declarations and three bindings.
   Catch arms have the written order, patterns and bodies; nested parentheses
   produce `outer (Group(inner (Group(tick 7))))` as applications/groups.
2. Formation supplies original distinct definition roots `Ri`, `Ro`, `Rm`, original
   formals `ti`, `to` with retained `[io] int` annotations owned respectively by
   `Ri`, `Ro`, and their exact scrutinee Names. Authentic family `F` has distinct
   declaration objects `op_tick`, `op_other`, both signature `Int -> Int`, with
   absent outer/argument effects. Module Names resolve uniquely to inner/outer.
   Source keys/ranges preserve the individual inner-arm and main call occurrences.
3. CandidateInference::solve succeeds without candidate conflicts, and normal
   RuntimeProgram/start preparation succeeds on these roots, using default
   evidence and the ordinary execution schedule. Primitive integer decoding of
   `7`, `11`, `23` succeeds with their written values and identities do not exhaust.

The existing helper (`runtime_receiving.rs:12–40`) calls these public APIs and
asserts success; written assertions do not prove these new inputs satisfy them.
RuntimeProgram construction is separate from candidate solve and cannot establish
candidate acceptance. Decoder source and the parser/module/declaration formation
owners are outside this packet's pinned read domain.

R88 §§3–5 establish the corresponding source bridge only for its exact U/O/S
single-Catch strings. Its reviewed closeout explicitly retains that finite scope.
Those facts cannot prove ENTRY for this new fixture by substituting names or
nesting applications. R88 is reused for its single-Catch result, identity
discipline and owner locators only. Its observed single-Catch duplicate-arm
11/23 contrast supports that older executable case; it proves no new parser
constructor or nested receiving transition. Luna explicitly acknowledged this
boundary and instructed the conditional derivation to continue under rev2.

## Pinned LocalSource and RuntimeProgram consequences of ENTRY

`local_source.rs:596–628` copies each supplied original formal and parses its
retained annotation with the definition owner. `:647–652` installs each arm's
own binders and restores lexical depth afterwards. `:1008–1040` resolves the
scrutinee to its original formal and the outer arm's `p` to that arm's payload
binder. Binder IDs include definition owner, arm SourceNodeKey and ordinal
(`:1103–1118`); repeated `p` spellings across arms/definitions do not merge them.
Continuation `_` becomes Wildcard, with no continuation binder or resumption.

`Builder::catch`, `:1120–1186`, validates CatchScrutinee/CatchBlock, iterates block
children, skips separators and pushes arms without sorting/deduplication. Both
inner matching arms are retained. The reverse body worklist only controls
construction traversal; it does not reverse the vector. Given ENTRY, A/C retain
tick-to-11 then tick-to-23, and B retains tick-to-23 then tick-to-11.

`resolve_operation` (`:1091–1101`) uses the supplied family/member namespaces
for both operation expressions (`:943–972`) and Catch patterns (`:1148–1170`).
Thus all written tick uses within one cell resolve to the same `op_tick`, while
C's outer arm resolves to distinct `op_other`. IDs from separate parsed cells
are not equated. `:894–938` constructs each ML Apply from its argument tail;
`:1055–1085` retains each parenthesized Group, so the whole argument remains
inert code until a receiver selects its interface.

`program.rs:414–433,451–509` maps both annotated formals to Computation and
their Names to Execute. `RootCompSchema::from_parameter`, `receiving.rs:21–43`,
accepts each original owner/formal/ground-Int/effect-row combination.
`program.rs:510–566` retains Apply child labels, forwards Groups, clones operation
resolutions and Catch patterns, and maps `arms.iter()` in order. Its SourceSite
copies source_root, expression occurrence and range without replacing them with
the demanding Name's site. `:575–605` schedules main as an Apply computation;
inner/outer Lambda definitions are demand-materialized closure values.

## Exact nested frame and receiving construction

Write stacks bottom to top. `R` is main's Root frame; `RO/RI` are the real
outer/inner ReceiverReturn frames; `HO/HI` their CatchReturn delimiters; `EO/EI`
their RootCompReturn frames. Frames for a tick operation invocation are `RCj`
(OperationResultConsumer) and `RTj` (ReceiverReturn). Literal-payload delay
execution creates no handler. GlobalRead frames used to obtain inner/outer
closures finish before either delayed argument executes, so none intercepts
either request. We do not assert numerical activation/occurrence IDs.

1. Main evaluates outer's callee. `Frame::Callee` (`machine.rs:879–1009`) allocates
   an inert Delay of the complete `inner (tick 7)` argument, creates fresh outer
   invocation `o`, pushes `RO`, and enters the original outer formal. The delay
   has no direct-formal inherited root because its code is a Group/Apply, not a
   direct formal Name (`direct_formal_root`, `:1477–1490`). Nevertheless
   `Receiving::enter` adds authentic boundary `o`, image `Io`, view `Vo` and an
   original-formal entry receipt. Unknown older coverage remains unknown.
2. Evaluating outer's Catch (`:707–737`) pushes `HO`, installed by active `o`.
   Executing its formal Name (`consume`, `:1858–1888`) creates an owner-`o`
   receipt for `Vo`, starts execution `eo` and pushes `EO`. Executing the Delay
   now evaluates the inner application. Its callee closure is fetched normally.
3. Inner's Comp entry similarly allocates a fresh inert Delay of `tick 7`,
   invocation `i`, `RI`, boundary/image/view `Ii/Vi` and original-formal receipt.
   Its argument also is not a direct formal Name; `Vi` need not inherit `Vo`.
   `HI` is installed by `i`. Its formal Name starts execution `ei` and pushes
   `EI`. Executing `tick 7` uses the authentic Int argument interface, creates
   a real operation invocation, evaluates the payload, builds a Request carrier
   and executes it (`:1013–1069,1790–1802,1929–1958`). The first event is `q7`.

At `q7`, the significant live stack is:

```text
R, RO, HO, EO, RI, HI, EI, RC7
```

The operation's own `RT7` has returned before `RC7` executes its Request
carrier. Current owner is `i`; executing views are `[eo, ei]`. The carrier's
source is main's tick-argument Apply, not either formal Name. `execute` mints
a fresh event and authentic observations of both live executions.

4. `propagate_request` (`:1531–1760`) moves `RC7` into q7's suffix and then
   moves `EI`, ending only `ei`. Now the stack ends in `HI`; current owner `i`
   is still active and equals HI's installer (`validate_handler_installation`).
   The first retained tick arm has the exact operation ID. `local_grant`
   (`receiving.rs:228–320`) succeeds constructively: q7's authentic ei
   observation joins the genuine owner-i receipt of exact `Vi`; its image
   contains boundary i, whose original annotation contains F. Unknown inherited
   coverage is not interpreted as a negative fact. Int compatibility and the
   single payload binder hold. Wildcard continuation means no capture template.
5. After all those premises succeed, `machine.rs:1633–1640` pops HI, abandons
   q7's raw suffix, binds that arm's own payload binder and sets Evaluate to its
   body. This occurs before arm-body evaluation. The resulting stack is:

```text
R, RO, HO, EO, RI
```

Current owner remains `i`. HI is absent, HO remains live, and execution eo is
still live; abandoning `[RC7, EI]` does not remove EO. This proves shallow pop
from the actual transition, without assuming a handler-stack slogan.

6. The selected body evaluates its distinct tick Apply with literal `x`, where
   x=11 in A/C and x=23 in B. It creates and returns its own operation payload
   carrier, then its OperationResultConsumer executes it. The fresh request `qx`
   has a newly minted event, payload x and inner-arm source; it is not q7
   forwarded with a new payload. At emission the significant stack is:

```text
R, RO, HO, EO, RI, RCx
```

Current owner is i and the sole observing execution is eo. The inner Catch
cannot select qx: it was removed before this body started.

7. Forwarding qx first moves RCx, then RI, leaving invocation i and restoring
   owner o (`leave_owner`, `:1272–1309`). It then moves EO, ending execution eo.
   The remaining stack ends in HO:

```text
R, RO, HO
```

HO's installer is the current still-active owner o. qx retains its authentic
historical eo observation despite eo having ended. `local_grant` expressly
allows historical observers: owner o's original/formal-Name receipt is indexed
for exact Vo; Vo's image contains boundary o and that boundary's annotation
contains F. Thus the outer grant is established without inventing an inherited
Vi-to-Vo image, conflating receipts, or assuming every same-family arm is eligible.

## Apply the construction to all three predictions

| Cell | Inner selection for q7 | New event | Outer action and predicted result |
| --- | --- | --- | --- |
| A | First tick arm, body tick 11 | q11, distinct event and source from q7 | Exact tick identity and positive outer grant select; bind outer p to q11 payload, return integer 11. |
| B | First tick arm after swap, body tick 23 | q23, distinct event and source from q7 | Same outer construction selects and returns integer 23. |
| C | First tick arm, body tick 11 | q11, distinct event and source from q7 | Outer other identity differs; skip that arm and forward q11 unchanged to UnhandledRequest. |

For A/B, outer selection pops HO and discards qx's suffix, including the already
unwound inner invocation and EO. Outer `p` resolves to its exact arm binder;
its Observe consumption returns the ground payload. RO then leaves o, R
publishes main's result, and normal schedule completion yields Completed with
that integer (`return_value`, `begin_root`, `:1805–1858`). No earlier 7 can be
returned through the discarded suffix. No second inner arm is evaluated.

For C, the declaration-ID mismatch branch (`:1570–1575`) skips before asking
for Grant; it proves no negative protection fact. HO forwards as a saved handler
boundary, RO leaves o and R forwards to exhaustion. `stop_unhandled_request`
(`:1763–1777`) copies q11's source, op_tick ID, payload and event to the outcome;
it saves the residual frames/observations as an opaque continuation. It does
not consume q11 or restore q7. No raw continuation is resumed in any cell.

## SourceSite lineage and exact falsifiers

Let `Ai11` be the Apply built from the MlArgument tail of the first inner arm's
`io::tick 11` in A/C. Its source is `(Ri, occurrence(Ai11), range(Ai11))`, using
`Builder::set`, `local_source.rs:818–844`, then `program.rs:555–566`.
The Apply range is the actual argument-tail range; this derivation never
asserts that slicing that range yields the whole text `io::tick 11`.

The operation call stores that exact Apply site in OperationPayload and
OperationResultConsumer. `make_request_carrier` stores it in ExecutableValue::Request;
`execute` copies it into PendingRequest; forwarding never changes it;
`stop_unhandled_request` copies it to UnhandledRequest. Therefore, conditional
on ENTRY's authentic CST/key/range lineage, C's outward source is exactly
Ai11's site. The initial call's Apply is in main's distinct root Rm, so its
SourceSite cannot be this inner-root site even if numerical ranges/ordinals
were confused. An operation PathTail site or the outer Name site is also not
the required Apply occurrence. B uses the corresponding inner-arm Ai23.

Falsifiers are a different CST/group/arm order, declaration or original-formal
identity; missing owner-i or owner-o authentic positive grant; HI surviving
selection; qx reusing q7's event/site; C consuming tick at its other pattern;
or outward source differing from the selected inner-arm Apply root/occurrence/range.
No source/runtime mismatch has been observed: no executable check was run.

## Remaining work, evidence and writer stop

`R101-ENTRY-1`: Luna owns the missing exact-source parser/module/declaration
formation and candidate/preparation premise. Exact owning locators supplied by
R88 include `parse_file`/root and binding parsing, `case_like` Catch/arm parsing,
`operator_chain`/ML argument and parenthesized expression parsing,
`module.rs` original-formal admission, and `source_annotation.rs` authentic
family/member registration. Candidate admission is owned by
`CandidateInference::solve`; primitive decoding by runtime `literal::integer`.
They were not added as dependencies or inspected here. A versioned contract and
reviewed additional pins are needed for that source audit. An execution result
can establish the three runnable cells, but cannot alone discharge these producer
constructors. Exact falsifier: any constructor output differs from ENTRY above.

`R101-REVIEW-1`: Luna appoints a fresh reviewer of these frozen bytes and pins.
The producer cannot certify this result. Review must check the historical outer
observation/receipt join, actual owner restoration and SourceSite tail lineage.
`R101-RUN-1`: only Luna may use the contract's one command after its required
freeze/review gates. The implementation lane owns exact fixture deltas and
assertions. Neither a green test nor this candidate closes R101-ENTRY-1.

No production implementation TODO follows. There is no authorized production
edit, semantic change, native instrumentation or inference weakening. Native
supplier/consumer and residual/provider/witness obligations retain their owners
and independent quantifiers; none is discharged by either local frame action.
R50/withdrawn bypasses, R85 semantics, arbitrary foreign continuation arguments
and R100's unrelated obligations are unused. The method changed from R88's
single-Catch consumer reuse to direct nested-frame/receiving construction.

All ten hashes (contract and nine dependencies) were checked and matched their
rev2 pins. Direct dependencies and SHA-256 values are listed in the companion
handoff. R88 proof author is `/root/r88_proof`; R88 closeout is Luna's reviewed
integration receipt. This note's only author is `/root/r101_nested_handler_proof`;
no coauthors or descendants. Other pinned source authors were not investigated
through Git and remain UNKNOWN in this receipt.

Checks: bounded read-only text/branch inspection and SHA-256 only. No parser,
candidate solver, compiler, runtime, test, build, formatter, CLI, network or Git
execution. No concrete source keys, receiving IDs, runtime events or residuals
were observed. Requested model/effort Sol/high; effective observed model/effort
UNKNOWN/UNKNOWN. Budget 600 seconds reserved, no renewal; exact active elapsed
unmeasured. No execution resource was used. The only new paths are this note and
`tasks/agent-loop/inbox/20261019-r101-proof.md`; scratch/generated paths: none.
After handoff freeze, writes stop with no descendants or unresolved child leases.
Next in-envelope step: none; stop condition is handoff freeze. Luna owns intake,
review, any contract revision, verification and integration. Parent remains open.
