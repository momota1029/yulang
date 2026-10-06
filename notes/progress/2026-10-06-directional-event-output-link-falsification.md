# Static output identity does not supply event incidence

Date: 2026-10-06
Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Status: frozen conditional research result; compiler-referee delta review passed with no findings
Method: conditional decorated derivation attacking one static shortcut
Claim class: conditional discriminator; precise unresolved source premise
Authority: no semantic decision, source-acceptance claim or implementation permission
Exclusive lease: this note only

## Objective and governing premises

Test whether `ElimOrigin`, the captured formal identity and equal/included
effect endpoints determine which concrete events use the newly protected
upper output occurrence. The input source remains exactly

```text
my apply f = { my step x = f x; step }
```

Governing pinned sections:

- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§1–6: protect the original upper occurrence, retain the lower/provider,
  and require separate event contribution/receipt/live-receiver evidence.
- [Source-call construction](2026-10-06-source-call-generation-construction.md)
  §7 P; §§4.2 and 4.4 identify the available static records and capture schema.
- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§2–3: return `step`, resolve its body to the same outer `f`, preserve capture,
  and make no handler/effect-execution decision.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §9: complete invocation includes actual entry/body/result consumer;
  explicit force does not recursively execute a latent returned value.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §§4 and 6: all enclosing executing observation occurrences, distinct typed
  ports, packet transport, actual receipt and current activation filtering.
- [Apply bridge](2026-10-06-directional-apply-output-bridge-attempt.md), pinned
  unreviewed snapshot: the conditional static conclusion is `NewProtection`,
  and its inversion stops before P and operational incidence.

Fix original `beta=(d_f,R_f)`, scope `sigma`, `c=Apply(u_f,u_x)`, and one whole
`xi=(nu,K,D)`. Keep the same captured `A_f`, generated `F_c`, `p_0`, and
`p_out(c)` throughout. The seed-at-exposure witness `k` is supplied exactly as
in the bridge. The established static result supplies
`NewProtection(k,beta,u_c,sigma,p_0)`; it does not supply a boundary instance,
packet, receipt, observation or event-contribution classification.

## Explicit conditional hypotheses

The following are additional *decorated witness premises*, not a source P
constructor or accepted interpretation of further raw source:

1. A single well-formed realization at this same `xi` has two distinct typed
   occurrences `p_0=call.effect` and `p_L=result.latent.effect`. A result
   projection maps `p_L` to `latent.effect` of the returned thunk. It does not
   map `p_0` there. Endpoint rows may both denote `[E]`; occurrences stay distinct.
2. P's still-unproved operational completion maps this exact new protection
   witness to a boundary profile instance `b` at `p_0`. This is the precise
   unresolved source premise. It says nothing about the existence or absence
   of other original or inherited result slots.
3. Typed packet transport supplies the matching identity/call correspondence
   to the executing view `v_c`, and an actual receipt
   `Receive(u,slot,v_c,matching-path)`. A profile at an unrelated alias is not
   substituted for this receipt. These are supplied typed derivations.
4. A complete decorated execution at this `xi` exposes request `q_0` of `E`
   during `c`, then returns an unexecuted thunk. A later explicit force exposes
   request `q_L` of `E` from that thunk after `c` has returned. Each event has
   its own fresh identity and retained source origin/lineage. No new `nu`,
   provider, continuation or predicate ledger is chosen between the events.
   The supplied observations include `Observe(q_0,v_c,p_0)` and
   `Observe(q_L,v_L,latent.effect)`; these are not exhaustive observation lists.
5. For this exact witness `(k,b,p_0)`, every applicable observation occurrence
   of `q_L` is excluded from a matching flow/receipt join: for every executing
   view `v`, effect port `r` and occurrence `o` with
   `Observe(q_L,v,r,o)`, and every receipt
   `Receive(u,slot,v,rho)` for that same view, no typed-flow chain from the
   profile `(b,p_0)` to `(v,r)` matches the receipt correspondence `rho`.
   This quantifies over the latent view **and every other enclosing executing
   view**, including all recorded observations retained for this event.
   Independent result/provider profiles remain available at their own
   positions; this premise excludes only the join for this exact `(u,b,p_0)`.

Hypothesis 5 is strengthened to supply the full negative premise. It does not
follow from the absent ordinary `p_0`-to-latent result projection, nor from
completion of `v_c`: typed-boundary §4 permits additional enclosing `Observe`
witnesses. No exhaustive decorated history or observation/receipt inventory
is constructed here, and no raw-source derivation of hypothesis 5 is claimed.

A supplied core provider can have the outline “emit `E`; return a delayed
computation that emits `E`”. Entry of the exact inner Name argument `J_x`
still returns its already rebound value; this witness does not replace it by
an arbitrary effectful carrier. The outline describes the supplied decorated
execution in hypothesis 4, not newly approved surface syntax or an established
admissible source context. In particular, no live receiver is identified with
the outer `apply` activation merely because `beta` names its formal.

## Small discriminator and derivation

Consider the projection available to the shortcut: generated output address,
original captured formal/root, upper/lower endpoint values, scope and whole
assignment. It omits event-specific executing ports, typed receipts and
source observation paths. Its values are unchanged for these two events;
even their effect-family and solved row values agree.

| Event | Displayed typed observation | Matching join for this exact witness? |
| --- | --- | --- |
| `q_0` | `Observe(q_0,v_c,p_0)` | yes, by hypotheses 3 and 4 |
| `q_L` | `Observe(q_L,v_L,latent.effect)` | none at any applicable observation, by hypothesis 5 |

Typed-core §9 gives the complete-call observation for the first event.
Explicit later force opens the returned latent view for the second, without
keeping the completed `CallView` active. Typed-boundary §6 gives the result
projection and explicitly forbids reusing the completed call's observation
edge for a later latent event. These facts alone do not exclude an observation
of `q_L` at another enclosing executing view.

Expand `Path(q,u,b,p_0)` in typed-boundary §6. For `q_0`, the profile, matching
typed-flow route, applicable `Observe`, and actual same-view receipt are all
present; therefore `Path(q_0,u,b,p_0)` holds. For the negative case, suppose
`Path(q_L,u,b,p_0)` holds. Its existential definition supplies some executing
view `v` and port `r`, an applicable `Observe(q_L,v,r)` occurrence, a typed-flow
chain from `(b,p_0)` to `(v,r)`, and a same-view receipt by `u` with matching
correspondence. Hypothesis 5 excludes that matching chain for every such
observation/receipt pair, giving a contradiction. Consequently
`Path(q_L,u,b,p_0)` fails under the strengthened hypothesis, regardless of
equality of the endpoint rows. The ordinary result projection is only one
excluded route; it is not the proof of this universal negative.

Thus no function of that static projection alone computes this exact
event-path incidence over the supplied decorated witness domain: its inputs
agree but its required Boolean outputs differ. With an actual candidate
handler `h` owned by `u` and all required activations live,
`Inc_C(q_0,h,b,p_0)` holds and `Inc_C(q_L,h,b,p_0)` fails. These activation
premises are separate, not inferred from capture. Expiring `b.receiver`
would also remove the first incidence while leaving the static records intact.

This is a small conditional discriminator schema: two distinguished
observation ports and two events display the required difference, with one
boundary witness and a supplied positive receipt. It does not establish that
there are only two applicable observation ports or construct a complete finite
history satisfying hypothesis 5. It is not a proved cardinal-minimum
raw-source program or an established source counterexample. It refutes the
decorated incidence shortcut only over realizations satisfying all supplied
hypotheses; it does not establish `Contributes_original(q_0,beta,p_0)` from
raw source.

## Precise source stop and failure conditions

The source-level falsification remains blocked at hypothesis 2. Source-call
§7 P must derive the original contribution/path interpretation and its
seed-to-refined receiving-view normalization, including how the static new
protection becomes the actual typed profile for this use. Hypotheses 3–4
also need a source admission/realization derivation for the surrounding
receipt and history. The supplied decorated Call certificate retains those
premises; it does not construct them from the source bytes.
Hypothesis 5 additionally requires a complete observation/receipt analysis of
an independently admitted history; its universal exclusion is supplied here
and remains unproved from source.

If P or independent admission excludes this realization, this is not a
source-valid counterexample. If any applicable observation of `q_L`, whether
at the latent port or another enclosing view, has both a matching typed-flow
chain for this exact witness and a same-view receipt by `u`, hypothesis 5 fails
and the second negative conclusion cannot be used. Establishing only the
absent latent projection leaves hypothesis 5 unproved. If the receiver or
candidate owner has expired, the positive `Inc_C` conclusion fails while the
raw `Path` derivation can persist. If the initial call is unsatisfiable, its
static output address still exists but neither executable event follows.

Known provider origin, lexical capture, equal rows, `VIncl` success and
`ElimOrigin` cannot replace these premises. The selected directional rule
also gives no reverse protection of the provider's lower effect. This note
does not choose a singleton full `Slots_original`, forbid independently
protected latent slots, or protect every event from a known provider.

## Checks, independence, resources and frozen handoff

Reads used `git show e12738d4f1452d87883516dfa5b709a4a5c38230:<path>` for the
governing construction/transport sections and bridge. Initial policy and
locator reads used the clean working tree at that same HEAD. A narrow
dependency diff and SHA-256 check followed. The bridge subsequently acquired
review metadata and an appended review report; its derivation was unchanged.
This argument continues to depend on its pinned unreviewed snapshot.

No executable reference or checker, Oracle, mutation run, random seed,
enumerated range, build, compiler test or performance measurement was used.
There was one derivation, not repeated variants of a toy transition system.
The named shortcut mutations are conceptual: replacing event observation by
address/capture lookup, collapsing equal effect endpoints, reusing a completed
call observation, or treating static capture as receipt. Only the conditional
path derivation above is evidence; no mutation execution is claimed.

There is no independent semantic oracle here. The argument shares the supplied
decorated transport and execution premises with the governing packages. It
does not validate source P by assuming P, nor independently review its own
output. Coverage is a conditional schema with two displayed event/port
witnesses; the universal exclusion in hypothesis 5 is supplied, not
exhaustively checked. Raw-source adequacy, original contribution, admission,
arbitrary result shapes, recursion, State, resumption/re-entry and
production behavior were not verified. Lightweight document reads ran in
small batches; no heavyweight processes ran. CPU/RAM and total wall time were
not measured. Some broad initial read captures were truncated; relevant
governing sections were reread narrowly. No exhaustive search was attempted.

Repair checks: typed-boundary §§4 and 6 were read at the pinned baseline;
the strengthened hypothesis and existential contradiction were edited only
in this leased note. Focused local-link/section locator and note-only
whitespace checks passed. No source experiment, exhaustive observation search
or independent review was performed for this repair.

Recommended next action: derive P and independent admission for a complete
source history, including the full observation/receipt exclusion. Do not
reuse this supplied conditional hypothesis as a source rule.

## Independent delta review

A fresh compiler referee reviewed the strengthened H5, the negative `Path`
derivation and typed-boundary §§4/6. No blocking, major or minor findings
remain. The quantified premise now excludes a matching typed-flow/observation/
receipt join for every applicable observation occurrence of `q_L`, including
enclosing or re-entered views, so it suffices against the existential `Path`
definition. H5 remains explicitly supplied and unproved from source; no
accepted-source counterexample or complete admitted history is claimed.
Original `beta`, scope, whole `xi`, selected one-way direction and independent
provider evidence remain unchanged. Source P, admission, receipt/history
realization and production behavior were outside this delta review.

Commit packet: exact leased path
`notes/progress/2026-10-06-directional-event-output-link-falsification.md`;
baseline `e12738d4f1452d87883516dfa5b709a4a5c38230`; changed dependency:
Apply bridge review metadata/report only (live SHA-256
`89f8b4c5522d799be0ef7e0dc7723549b91b232c6092bbc300133a2bf0077708`;
pinned SHA-256
`eb769fc97930d6da23785c7c01102bc83a29daeb26186aae1c5374ca1da410ea`);
other governing dependencies unchanged. Review status: fresh compiler-referee
delta review passed with no findings; accepted major finding is closed only
for the conditional quantified exclusion, not source derivation.
Checks: pinned section inspection, narrow dependency diff/hash and note-only
link/whitespace check. Proposed message:
`research: strengthen conditional event path exclusion across all observations`.
Shared-record deltas intentionally left for primary/curator: record the
strengthened conditional discriminator and exact P/admission/exclusion stop
without claiming source counterexample, full profile closure or production
authority. No shared records, question bundles, compiler files or Git state
were mutated.
