# R78 annotated relay: receiving and ordered selection certificate candidate

Date: 2026-10-19. Revision: 1. Author: `/root/r78_proof`.
Status: **OPEN / UNFINISHED; frozen candidate source-linked runtime derivation**.
Independent review: pending Luna assignment; the author does not certify this result.
Sprint: `effect-hygiene-executable-method-role-20261019-r78`, contract revision 1,
SHA-256 `bf68454c19a7b4cfe5168355e0e5fb73beec069ad57dd53678258a66f26dfcab`.
Baseline named by contract: `af3ccf2d63ba7f87e0359e183568db548ea53307`.
No Git operation was used to independently observe the branch or baseline.

## 1. Parent, scope and first missing premise

The parent remains the original effect-hygiene/source-native obligation under
the unchanged Simple-sub and evaluator/A-B contracts: preserve the original
provider, annotation position, receiver, request, residual and witness lineages
under one joint assignment `xi=(nu,K,D)`; authorize local handling only through
the actual applicable receiving/selection evidence; preserve independent
outward contributions. Soundness, natural inference, complete Call and original
universal quantifiers remain OPEN 0→0; R50 remains NOT_ADOPTED. This note neither
replaces the parent with a three-example theorem nor discharges F1, FK1 or any
foreign-continuation quantifier.

Authority: annotation integration §§1–1.2 distinguishes permission, inflow and
residual; charter §21 fixes the outer-annotation Computation role and whole
inert argument; directional addendum §§2–2.2 preserves the distinct inferred
upper-use and provider-lower provenance. Top-level inference principles retain
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization. No special solved-row test, cap or execution analysis is
introduced.

**First unaudited authentic constructor seam:** the named test helper calls
`parse_file` and `lower_module_with_local_source`, but their implementations are
outside this leaf's pinned runtime inputs. Inspecting that helper does not prove
that those constructors emit the expected original Lambda/formal annotation,
resolved Parameter Name, resolved operation and ordered Catch patterns for
these exact strings. Their occurrence/annotation/arm correspondence is therefore
an explicit premise below, not a theorem obtained from asserted test outcomes.
The bounded proof stops at this seam. The remaining sections preserve the
useful runtime-consumer derivation for Luna rather than silently assuming this
seam closed. No broader source search, new dependency or production edit follows.

There is a separate later seam: even an authentic HIR-to-runtime trace does
not establish native inference's source-derived profile/permission supplier,
joint `K,D`, actual mapped-bound admission and all relevant consumers, or a
constraint-derived residual type. Both seams remain OPEN with distinct owners
in §7.

## 2. Exact three source occurrences

These are the activation strings in `current.json`; UTF-8 bytes have no trailing
newline. Source offsets below are text anchors only, not invented HIR IDs or
runtime ordinals. Each runtime identity is whatever the authentic constructor
allocates at the named occurrence.

### U: unit payload

```yu
act signal:
    our ping: () -> int
my relay (thunk:[signal] int) = catch thunk { signal::ping(), _ -> 1 }
my main = relay (signal::ping())
```

139 bytes; SHA-256 `d9f97c3a73925e86e1220011adbfd961679a786b0eec6cd39abc12163e761ed4`.
Formal `thunk:` starts at byte 46; consumed `thunk` at 74; `my main` at 107.
Named test: `unit_payload_empty_call_pattern_selects_its_arm`,
`runtime_receiving.rs:152`; its source assertion expects Integer `1`.

### O: exact operation after another arm

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::other(p), _ -> 99, io::tick(p), _ -> p }
my main = relay (io::tick 7)
```

174 bytes; SHA-256 `31adb9c858d845582fda0005437821af6d67ede26b824b1e0d089d4baebbcb1b`.
Formal starts at 69; consumed Name at 93; `my main` at 146.
Named test: `a_different_operation_arm_does_not_preempt_the_exact_operation`,
`:91`; its source assertion expects Integer `7`.

### S: selected arm requests outside its handler

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::other p, io::other(p), _ -> 99 }
my main = relay (io::tick 7)
```

184 bytes; SHA-256 `e0a1037879571d4360201fb66289b60102e3ef3aaf37719ee1ace9b14df939cb`.
Formal starts at 69; consumed Name at 93; `my main` at 156.
Named test: `selected_operation_arm_runs_outside_its_shallow_handler`,
`:101`; its source assertion expects UnhandledRequest for resolved `other`
with Integer payload `7`. These assertions were read, not executed here.

For each fixture separately, let `L,t,a,n,h` denote its original relay Lambda,
formal, outer annotation, consumed Name and Catch source occurrence. Let `u`
be that call's newly allocated receiver; `T` its whole Delay; `V` the entry
view; `b` its boundary; `r_n` its actual Name-read receipt; and `q` the initial
request event. These symbols do not identify the three distinct programs with
one another. Nor do they identify a native type endpoint with `u`, a static
occurrence with a dynamic event, or provider evidence with receiving evidence.

## 3. What the pinned constructors and consumers actually establish

Assume an authentic LocalSource projection of the exact fixture, retaining the
original forms and resolutions just named. The following joins are inspected
code facts, rather than transitions postulated in a checker.

| Stage | Actual source owner and bounded consequence |
| --- | --- |
| Original identity to code | `RuntimeProgram::from_hir`, `program.rs:277–330,451–566`, fetches the original local source by source root, validates child indices, retains each expression's `SourceSite {source_root, occurrence, range}`, original parameter ID, resolved operation declaration and arm source/range. Catch arms are collected in original vector order. This consumes HIR; it does not prove raw-source emission. |
| Role, permission schema and Name consumer | `program.rs:414–433,488–509` chooses Execute for the explicit-outer-effects formal and Computation for that Lambda; `receiving.rs:21–43`, `RootCompSchema::from_parameter`, requires original formal/annotation ownership, explicit outer effects and a ground value tag. All three result tags are Int. The retained schema contains the original formal and row; it is neither actual inflow nor a residual. |
| Whole argument and authentic entry | `machine.rs:879–1009`, Frame::Callee, allocates one inert Delay before the Computation-role branch, then `new_invocation` at `:1248–1268` allocates a fresh active receiver with original call/provider sites. `Receiving::enter` at `receiving.rs:128–168` adds `b=(u,schema)` to this view's inherited image; entry receipt and `Binder::Parameter(t)` bind the same Delay/view. No argument prefix runs at this Comp entry. |
| Catch owner and actual read | `machine.rs:707–737` installs this Catch with its fresh occurrence and actual current owner `u` before evaluating `n`. Name lookup at `:557–629` resolves the original parameter cell. `consume`, `:1854–1889`, validates the same underlying value/view, makes a genuine read receipt, opens an execution of this view/receipt, installs RootCompReturn and executes `T`. No row/family equality substitutes for that receipt. |
| Actual request, not permission-as-inflow | Operation evaluation/Apply at `:681–706,1011–1069` obtains the retained declaration and declared payload consumer, creates its request carrier, and executes it at the declaration's result consumer. `execute`, `:1929–1962`, allocates fresh event `q` and authentic observations of currently executing views. The operation expression in the actual Delay supplies the request; the annotation supplies no request. |
| Local permission query | `Receiving::local_grant`, `receiving.rs:232–326`, requires this candidate owner's active invocation, exact original boundary, annotation-row concrete resolved family, authentic event/execution/observation, and a genuine candidate-owner receipt of this same view/formal route. The Name-read receipt is such a witness. The boundary image reaches `b`. U grants the resolved signal family; O/S grant io. Unknown inherited coverage stays unknown. |
| Candidate selection | `propagate_request`, `machine.rs:1550–1687`, validates the actual still-installed candidate, compares full resolved operation IDs in arm order, then requires positive local grant unless the separate closed-primitive certificate applies. The positive grant above suffices without assuming that independent certificate. It also checks declaration shape, one payload pattern and actual primitive payload compatibility before committing selection. |

The execution view's original observation survives request unwind even though
RootCompReturn is removed from current execution before the handler query
(`machine.rs:1720–1723`). `local_grant` authenticates its historical execution
and event; it separately checks the still-live original receiver. The observing
receipt is not replaced by a new owner or inferred from current stack shape.

Application to parent: the receiving/local-selection portion has an explicit
consumer chain **conditional on authentic HIR**. This is stronger evidence than
permission alone or a generic assumed-transition model. It establishes neither
all-source acceptance nor the inference endpoint/constraint chain.

## 4. Ordered operation and payload conclusions

U: the actual request is resolved `signal::ping` with Unit payload. The matching
arm's empty-call pattern is consumed as a wildcard/Unit pattern after the
declaration's Unit payload check (`machine.rs:1593–1606,1641–1658`). The runtime
comment says empty-call syntax lowers to wildcard; that comment is not a fresh
proof of the outside-packet HIR pattern producer. Under the authentic pattern
premise, the single arm is selected and its ground `1` returned.

O: `io::other` and `io::tick` have different operation IDs despite a common
family. The first arm's ID mismatch takes the explicit `continue` before any
selection of its body. The next arm's tick ID matches; declared Int payload `7`
passes `primitive_matches` (`machine.rs:1237–1247`) and binds that exact request
payload to its original Catch binder `p`. Returning `p` yields the same Integer
`7`. There is one matching operation arm in this fixture. This is ordered exact
ID selection, not a general ambiguity or pattern-exhaustiveness theorem.

S: the first tick arm selects and binds the same `7` payload. Its second other
arm is a later arm in the consumed handler, not an enclosing handler. The fresh
request described in §5 cannot return to that arm.

Parent application: a local family permission does not allow a different
operation to preempt the exact request. Each actual selected transition still
depends on its independent declaration/payload/handler evidence; family
membership by itself does not constitute a selection certificate.

## 5. Continuation and outward runtime request

All three selected arms have continuation pattern `_`. The implementation only
captures a raw template when that pattern is a Binder. Here `captured=None`;
it pops the selected Catch delimiter and calls `abandon_suffix` before entering
the arm (`machine.rs:1607–1687,1777–1789`). Thus none of these three occurrences
invokes, resumes or proves anything about a captured continuation. Discarding
an unexecuted suffix is source control allowed by the reviewed forwarding
theorem. No foreign continuation or arbitrary resumption case is discharged.

In S, arm code runs after the exact CatchReturn was popped. Its `io::other p`
uses a new operation application, the actual bound `p=7`, and a fresh request
event `q2`, distinct from the selected tick event `q`. The executing-view stack
for the abandoned thunk has already been unwound. A same-family annotation
does not fabricate an observation/receipt path for `q2`. With no enclosing
Catch in this fixture, propagation saves the real remaining suffix and ends in
`stop_unhandled_request` (`machine.rs:1706–1775`), retaining operation, payload,
event, source and continuation handle. The second arm in the consumed Catch is
unavailable. The outward result is therefore a runtime other-request under the
authentic HIR premise, matching the test's written assertion.

This outward event is produced by selected arm code, not an additional write
contribution in the original supplied thunk. These three fixtures contain no
signal-plus-write input and no blocked protected sibling request. They give no
new occurrence-specific runtime evidence for those missing cases. Reviewed
forwarding and typed-boundary preservation retain their conditional guarantee
for independently matching protected/unmatched contributions; no whole-family
deletion or static residual-row equality follows from this trace. In particular,
normal ground results in U/O do not prove a statically empty residual; outward
runtime forwarding in S does not prove a specific native residual type.

## 6. Scoped reuse and rejected shortcuts

* Forwarding preservation §§1–5 supplies the source-derived explicit-root local
  preservation result under its original monomorphic typing, shared `xi`,
  ordinary OpCompat/control and actual receiving/map premises. Its arbitrary
  finite chains and finite raw-use prefixes remain quantified as originally
  stated. Here the immediate relay has no additional formal-Name forwarding
  edge. Its raw-use cases are not established by these discard occurrences.
* Primitive-root receiving §§1–4,8 supplies the reviewed ground schema/root
  consumer result, including actual widened matcher correspondence. Instantiate
  at Int only. It expressly retains raw HIR/source typing, source-runtime and
  native residual premises, and notes that this runtime represents only the
  root projection, not the complete `K,D` ledger.
* Typed-boundary §6 transport/lifetime clauses preserve indexed source witnesses,
  original boundary/receiver identity, `K`, matching `D` paths and lineage under
  supplied valid correspondences and current-scope filtering. Identity binding
  and consumed ground-result projection apply at their actual matching paths.
  The package does not invent profiles, arbitrary raw-source maps or reentry
  ownership. Runtime view records are not relabeled as a full native ledger.

Rejected: annotation as closed input cap or effect occurrence; static residual
from runtime success; empty context word as empty residual; same family as same
operation/view/receiver; selected-arm discard as continuation resumption; source
test assertions as actual constructor emission; forwarded root theorem as
all-source hygiene. The retracted annotation example is unused. R77,
storage/fiber/C1 work, unadopted new source laws and withdrawn bypasses are unused.

## 7. Exact open premises and mutual TODOs

| Stable request / owner | Required evidence and falsifier |
| --- | --- |
| `R78-SOURCE-HIR-1`; Luna routes to authentic LocalSource producers (`parse_file`, `lower_module_with_local_source`, original annotation/Name/operation/Catch projection) | Read-only audit on newly pinned producer paths must join each literal's original Lambda/formal/annotation/row, resolved Name and operation IDs, arm order and payload/continuation patterns to the runtime inputs in §3. Required inputs: exact fixture hashes and original source occurrences. Proposed output: a bounded source projection receipt or exact missing source law. Falsifier: a claimed annotation, identity, arm order or pattern is not emitted at its actual occurrence, or the audit substitutes successful tests for producer evidence. This packet has no expanded read/write lease. |
| `R78-NATIVE-HYGIENE-1`; Luna, source annotation/formal and native lifecycle/consumer owners | After authentic source projection, derive the source-licensed received entry profile/permission and actual constraint-derived inflow/residual, preserving original carrier/positions and joint `K,D`. The existing forwarding §6–7 names FormalRegistrationInput/FormalEntry, candidate_source formal/Name, candidate_effect, FreshUse/candidate_scheme, shadow_apply and Catch output as owners; those current native files were not inspected here. Required evidence includes one authentic per-use map with mapped original bounds actually admitted at each relevant consumer, plus lifecycle coverage where the original parent requires it. Falsifier: the derivation guesses inflow from permission, uses original endpoints in place of a FreshUse copy, loses ordinary constraints/provider or witness lineage, or drops an independent surviving same-point contribution. |
| `R78-UNIVERSAL-1`; Luna, original hygiene/complete-Call/continuation parent owners | Apply reviewed local clauses only after their source/native premises are established. Supply remaining inferred/unknown/function profiles, supported source and lifecycle cases, protected/unmatched contribution cases and independent continuation quantifiers at their own original scopes. Falsifier: a local ground discard trace is offered as evidence for an arbitrary foreign continuation, all-model property or unobserved source constructor. |

The minimal next evidence request is the first row, not an implementation
change. If code evidence later becomes necessary, Luna must separately grant
the smallest provisional constructor-to-consumer observation cut with the same
identity/row/lineage falsifier; no production TODO is authorized by this note.
Luna also owns fresh independent review, intake/status integration and any lease
change. The author has reached the stop condition and has no remaining active
in-envelope successor.

## 8. Frozen dependencies and resource receipt

All direct source/semantic hashes below were observed with `sha256sum` and match
the activation pins. Historical hashes inside reused notes retain their original
baselines and are not asserted to be hashes of current native files.

| Direct dependency | SHA-256 |
| --- | --- |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| annotation-effect hygiene integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| directional protection addendum | `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73` |
| charter §21 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| computation-forwarding preservation | `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79` |
| primitive computation-root receiving | `a043c69eb9fd82127bb7ad59d797abf3f10c5edf83bd80316183074f48c28606` |
| typed-boundary §6 | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| runtime program.rs | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| runtime receiving.rs | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| runtime machine.rs | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| runtime_receiving.rs | `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf` |

Current author and sole writer: `/root/r78_proof`; no coauthors or descendants.
Prior reviewed producers/reviewers are credited by their pinned documents;
individual effective model identities there are not reconstructed here.
Requested routing: contract's configured Sol/high; exact spawn API model/effort
is UNKNOWN to this leaf. Observed effective model/effort: UNKNOWN/UNKNOWN.
Session: `current-conversation-2026-10-19-r78`; live assignment message received
from `/root`. No in-place model change or independent certification claimed.

Budget: 900 seconds maximum, one static source/consumer audit stage followed by
freeze at the first authentic source-projection gap. No probes, tests, builds,
Oracle execution, network, Git, delegation or measurements. Static fixture byte
hash/anchor inspection used Python 3 after the unversioned `python` command was
unavailable; neither invocation executed compiler/runtime semantics or wrote a
file. SHA/source reads and artifact formatting inspection are the only checks.
No concrete HIR IDs, runtime event ordinals, fresh test outcomes, inferred schemes
or machine traces were observed. Exact wall-time receipt is in the handoff.

Only new paths: this artifact and
`tasks/agent-loop/inbox/20261019-r78-proof.md`. Scratch paths: none.
After frozen handoff submission, writes are stopped; no descendants or unresolved
descendant leases. Research preservation/review pending Luna; theorem and
production authority are unchanged.
