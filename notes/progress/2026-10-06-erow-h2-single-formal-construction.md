# EBRIDGE H2 for one known annotated callback formal

Date: 2026-10-06
Status: Frozen research-only conditional factorization and bounded obstruction; unreviewed
Baseline assigned by primary: `76e585112` (primary-supplied revision identifier)
Exclusive lease: this file only
Method: constructive factorization through existing typed interaction and transport rules
Implementation authority: none

## Objective and result

Try to construct H2 of the prior EROW source-profile construction for one
known, instantiated, annotated callback formal. Keep the immediate call
effect and the effect of calling a returned function distinct. No inference
of an unknown formal, operational handler-image proof, source/code audit,
or executable transition probe is repeated here.

**Conditional result:** after a source derivation supplies the occurrence's
exact completed typed position and its original profile clause, port
polarization and result-path transport follow from existing rules. The
same original `(nu,K,D)` suffices; no fresh polarity assignment or carrier
is needed. **Bounded obstruction:** the known formal, its role, and the
interaction directions do not themselves supply that source derivation or
the profile's explicit concrete-admission clause. Even for this single
formal, complete H2 cannot be derived from the inspected contracts.

This is a factorization of the missing premise, not a source theorem or a
newly selected annotation rule. The prior annotation audit already found
the producer gap. The additional calculation here determines exactly what
the existing direction/transport rules can discharge after fixing a known
formal, and why adding a polarity label does not close that gap.

## Governing sources and retained decisions

The requested `2026-10-05-concrete-function-effect-compatibility.md` is absent.
The governing compatibility document located through INDEX is
`2026-10-03-concrete-compatibility-boundary.md`.

| Source and exact section | Authority and use |
| --- | --- |
| Approved effect-row answer q1/d1, decisions 2–6 and approval provenance; receipt, Validation and Outcome | User-approved polarity-sensitive fragment: covariant allowance; contravariant compatible matching, with example `int <: 'a`; targeted removal in the deep case. Role/typed port precedes interpretation at one joint `(nu,K,D)`. Concrete membership and source evidence remain open. |
| Concrete compatibility §1, “User-directed Function effect comparison” and “Role-first source elaboration”; §9 | Draft containing scoped user-directed decisions. Ports are coupled; the row/component-to-existing-evidence bridge remains open. §9 does not define annotation-to-port occurrence rules. |
| Inferred Function call views §§1.1, 2, 4, 5.1/5.3/5.4 | Authoritative direction, explicitly incomplete rules. Written annotation, public inferred type, and internal view differ. Original slot, occurrence, scope and joint assignment survive. The pending comparison Q creates none of them. |
| Callback context delivery §§1, 2–2.1, 3–4 | Authoritative bounded B contract. Known `F_cb`, `beta`, `Slots(beta)` are supplied; context selects Handler before literal body generation; endpoints are independent and checked once by `F_lit <: F_cb`. Actual role/entry of an existing value is preserved. |
| Typed computation core §6, “Source interface and one normalization” and “Source parameter-role generation”; §9, “Entry is part of the interface,” “Derive directions,” and “Finite classification” | Reviewed Draft results conditional on typed input. Admitted annotations and known computation ports are premises. Complete invocation differs from body result. Directions are derived on revealed typed paths, retain `K,D`, and create no profile or grant. |
| Typed boundary §2, “Latent values after the complete CallView returns”; §4, “Typed value flow and computation observation”; §6, introductions, transport, receiving ownership, and proof boundary | User-selected typed-value transport with reviewed Draft realization. Profiles come from source elaboration. Immediate and latent positions are distinct. Result transport follows corresponding typed paths; later execution has its own Observe edge. Source profile construction remains open. |

The previous construction's H2 and the reviewed annotation-occurrence audit
are prior research dependencies, not extra semantic authority. Their open
producer premise is retained. The call-view clarification in §1.1 is consumed
directly from the current inspected source, rather than relying on the older
audit's pre-clarification dependency hash.

The `[io]` permission is not identified with explicit concrete capture
admission, actual subtraction, or `'e?`. The mixed-row answer likewise does
not let the word `write` allocate an owner, an event incidence, or a grant.
No tentative shallow principal type or legacy stack-pop rule is used.

## Fixed input and the reduced H2 obligation

Fix one finite completed typed interface graph `G` for a resolved receiver
offered to its context, one known `Value(F_cb)` formal, its original static
`beta` and `Slots(beta)`, and one nonempty jointly well-formed source fiber
`xi=(nu,K,D)`. These are supplied hypotheses. Choosing this envelope removes
unknown declaration lookup and whole-contract inference from this attempt.

The formal returns a function value. Distinguish the formal-local positions

```text
p0 = call.effect
p1 = result.function.call.effect       p0 != p1
```

Their occurrences in the offered receiver are `arg.p0` and `arg.p1`.
The formal's written contract contains a concrete row occurrence `sigma`
and an abstract occurrence `epsilon`; their syntax identity, scope and
source component are fixed. Whether sigma governs p0 or p1 must come from
its admitted typed annotation derivation, not an arbitrary choice here.
Any additional occurrence of the shared abstract component retains the same
component identity and original fiber. No standalone meaning is assigned
to the component independently of these completed views.

Three proof obligations separate what “annotation to polarized profile” needs:

1. **T: typed source correspondence.** An admitted annotation derivation links
   `sigma,epsilon` and their source scope to a specific original effect path
   `p` of `G`, preserving the local boundary realization, predecessor evidence,
   and the completed view's source tags under xi.
2. **S: structural direction.** The root-to-p interaction path gives the sign
   of that completed occurrence in the offered receiver.
3. **A: original profile clause.** At p, the original profile supplies the
   source-supported protection and explicit operation-admission predicate
   needed by H2, including the component interpretation and correlations.
   This is stronger than knowing that the profile exists or that the
   operation's name is written in a row.

T and A describe evidence required in existing carriers. Their names are
proof placeholders, not new adopted judgments or stored maps. H2 requires
T and A as well as S. The established interaction theorem supplies S once T
identifies a typed path; it does not supply T or A.

## Conditional derivation

**1. Derive signs without reading the row as a role.** Mark the offered
receiver root `+`. Its received callback carrier is `-`. A callable's
complete call effect preserves that direction, so `arg.p0` is negative.
A returned value preserves direction; the returned function's complete call
effect also preserves it. Therefore `arg.p1` is negative too:

```text
receiver (+) -- receive callback --> F_cb (-) -- call effect --> arg.p0 (-)
receiver (+) -- receive callback --> F_cb (-)
            -- returned function --> returned view (-) -- call effect --> arg.p1 (-)
```

This is induction over the typed-core §9 interaction clauses. The functions'
own argument carriers would reverse direction again; neither p0 nor p1 is
such an argument carrier. Receiver role is fixed before this calculation;
parameter entry remains separately fixed by syntax. Role bits do not
compute the complete image or replace T.

**2. Attach a supplied annotation clause only at its supplied position.**
Assume T identifies `p=p0` and A supplies the original clause there. Reading
that clause at `arg.p0` gives the negatively polarized input occurrence in
the offered receiver. If instead T identifies `p=p1`, the same sign theorem
gives a negatively polarized returned-function occurrence. This conditional
case split does not select which source annotation maps to either position.
Any covariant correlated view required by the selected mixed fragment must
be independently present in G/T at the same xi; the two negative signs here
do not manufacture it or prove its post-handler residual.

**3. Derive the returned profile projection.** In the supplied typed graph,
ordinary result transport removes the corresponding `result.function`
prefix for the returned function view. Its relevant correspondence is

```text
M_result(p1, returned.call.effect)
p0 is not in dom(M_result) at these two effect positions.
```

The second line is justified by the disjoint immediate/result typed paths
and this structural result projection, not by equal family names. For the
single supplied source packet, typed-boundary §6 gives

```text
chi_returned = (M_result)_* chi_source
D_returned   = (M_result)_* D_source
K_returned   = K                       under the original nu
```

Consequently an original p1 clause reaches `returned.call.effect`; a p0
clause cannot reach it through this projection. This is a local statement
about that source packet and M_result. Another actual-value or independently
annotated result packet can contribute its own corresponding clause through
the general multi-input transport rule. No absence claim about all such
packets follows.

**4. Keep later observation separate.** A later call of the returned function
has its own complete executing view and `Observe(q,v_returned,call.effect)`.
The completed earlier callback call contributes no new Observe edge to that
later event. While the original receiver is active, transported profile,
matching receipt/Flow, and the new event observation can be inputs to Path.
Current owner/receiver/handler activity and explicit admission are additional
inputs to Grant. Expiry disables their authority. None follows merely from
the static sign or from returning the value.

These four steps establish a **conditional factorization theorem for this
finite supplied graph**: T+A allow source-position-indexed polarization and
the stated result projection at xi. They do not establish T+A, actual
removal, all mixed membership, or production acceptance.

## Why fixing a known formal still leaves a source hole

Callback B §2 explicitly receives `F_cb`, `beta`, and `Slots(beta)` already
instantiated. Its role selection cannot be used as a constructor for the
profile it takes as input. The annotated *formal* here is distinct from
an explicitly annotated callback *literal*; no annotation/literal-context
overlap is added to B's envelope.

The admitted-annotation premise in core §6 can provide source endpoint
checking, but that section does not give its derivation to the complete
call observation path. In particular `J_body` and `J_call` differ even for
Value entry with a pure body. Equating an arrow's written RHS with an
already solved invocation profile would assume the missing connection.

Core §9 supplies S for every revealed typed path. Boundary §6 transports
profiles already attached to those paths. Neither rule mentions sigma as
an input from which to construct T or A. Inferred-call-view §§4–5 and
compatibility §9 expressly retain this obligation.

A useful obstruction particular to the calculation is that p0 and p1 have
**the same sign**. Forgetting their typed paths leaves one common negative
direction, so polarity plus a family/type point cannot recover the original
position. This is an information-loss statement about that projection; it
does not propose alternate valid language meanings. The minimum structural
graph exhibiting this ambiguity has two effect positions and one returned
callable edge. With only one effect position, same-sign ambiguity cannot be
exhibited. No source program or executed mutant is claimed.

The exact remaining local judgment is therefore:

```text
admitted annotation occurrence(sigma,epsilon,scope,local evidence; xi)
known completed formal(G,F_cb,beta,Slots(beta); xi)
    -- missing source derivation -->
the corresponding original effect position p and its source-supported
profile clause, with component interpretation and all original identities
and correlations retained at xi, independently of pending Q.
```

T must establish which typed position corresponds; A must establish what
that original clause admits. Even granting T alone would not derive H2's
explicit compatible `write int` admission. Existing Grant consumes that
admission predicate; it cannot prove how source syntax generated it.
This bounded inspection proves neither that another repository source
cannot supply the judgment nor that the existing carrier is insufficient.

Recommended next action: adjudicate T+A for this known two-position formal
as one narrow source-formation gate before another operational probe. If no
approved source rule supplies the clauses, seek a scoped design decision
through the primary; do not adopt this proof interface as semantics.

## Independence, failures, omissions and resource record

No execution oracle was used. The direction induction and transport projection
use the inspected Draft packages' rules; they share the completed graph,
typed paths, xi, T and A hypotheses. They are consequences conditional on
those rules, not independent validation of their raw-source adequacy. A
checker supplied with T/A or the same transition rules would leave the
producer premise untouched. No equivalent toy probe was attempted.

Failure conditions include empty/incoherent xi, using independent assignments
for p0/p1, a missing admitted annotation, fabricated path correspondence,
creating profile admission after Q succeeds, confusing body and invocation
ports, copying p0 onto returned-call paths, or treating transported protection
as a current grant. Changing the structural result correspondence invalidates
step 3 and requires a new typed derivation. Shared/recursive occurrences can
receive both signs; this one-path finite instance does not establish a unique
sign for arbitrary alias graphs.

Unverified: raw grammar or compiler acceptance, generalization/instantiation
preservation, completed-contract principality, arbitrary mixed membership,
production Option A/Option 2 conformance, event attachment, handler selection,
complete deep image, residual normalization, State/reference behavior,
unknown interfaces, open clients and re-entry ownership. Seeds, numeric
ranges, samples and executable mutations: none.

Commands: bounded `cat`, `sed`, `rg`/`rg --files`, one read-only Python SHA-256
inventory, leased-file creation, and final read-only dependency/file integrity
check. Some combined routing/read captures were truncated; exact semantic
clauses were subsequently read in narrow excerpts. No exhaustive source
search is claimed. No tests, builds, probes, formatters, Git operations,
children, shared-record edits or scratch output files were used.

Commands were sequential lightweight processes; no heavyweight process ran.
CPU time, peak RAM and elapsed wall time were not measured, and the packet
specified no numerical resource limit. The only output is the leased note.
The primary owns byte comparison to the assigned baseline; the packet forbade
Git operations, so these are observed filesystem hashes, not worker-certified
baseline bytes. The initial and final dependency inventories must match
before freeze; integration must check them against the pinned revision.

| Direct input | Observed SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` | `032849b8bc8e9398889ed589be9e7598252f53924346de31175538e533bee997` |
| `questions/2026-10-05-function-effect-row-denotation/receipt.md` | `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-erow-source-profile-construction.md` | `a696636d2587e55955fe6deb6ab0d841f9bd63131e9f4d992beab4abe0272d22` |
| `notes/progress/2026-10-06-annotation-occurrence-profile-bridge.md` | `2ace5a896d205d14a75cf90b582802ffc8477800d87e5f1e9da678a369237a46` |

## Commit packet

- Exact lease: `notes/progress/2026-10-06-erow-h2-single-formal-construction.md`.
- Baseline: primary-assigned `76e585112`; full commit identity and baseline
  byte verification remain primary-owned under this no-Git packet.
- Dependency changes: no worker changes; start/end filesystem hash equality
  reported in the return packet. Differences from pinned baseline are not
  determined by this worker. The older annotation audit's call-view hash
  predates the directly read §1.1 clarification and is not used as authority.
- Review status: frozen, unreviewed conditional factorization and bounded
  obstruction. No independent certification, source theorem or gate closure.
- Checks already run: governing-section inspection and SHA-256 integrity
  checks; no semantic executable checks, tests or builds.
- Proposed commit: `research: factor known-formal H2 into source correspondence and profile admission`.
- Shared-record deltas left for primary/curator: if accepted, record that
  structural direction and result transport are downstream conditional
  consequences while H2's T+A source producer remains open. Preserve EBRIDGE
  as open; no authority promotion, code/test change, or question-bundle edit.
