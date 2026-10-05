# Release discriminator: existing output delimiter and missing marker association

Date: 2026-10-06
Status: frozen, unreviewed research; conditional candidate and precise source-premise reduction
Baseline: `885939a8202190fb2d0d8ffe20cea16a17d16d56`
Lease: this file only
Implementation authority: none

## Objective, method and result

Find a smallest outward-crossing candidate whose next handler query can
distinguish protection before and after the approved release. Method:
instantiate the existing non-covering shallow-forward rule and inspect the
existing source-realization output-observation instruction. Audit whether
original slot and Force-origin coordinates supply the public marker's missing
association. The prior false-guard example is only a locator; its derivation
and same-owner/grant assumptions are not reused.

**Reduced premise:** source-realization §7 already records an output
observation when an original request crosses a particular invocation, force
or handler output delimiter. It preserves the packet/suffix and distinguishes
this local crossing from later outside handling. Thus ordinary outward
evidence need not be reconstructed from pre-dispatch `Observe` or the final
handler image.

**Conditional query candidate:** one original event, one protected received
view, one live receiver, and an outer covering handler with no capture grant
give a protection-dependent query. If an inner handler-processing step is
required, a non-covering inner handler forwards the same event without
requiring a second owner or introducing an inner capture grant.

**No complete source-derived marked discriminator was established.** Existing
clauses do not derive the association of the public marker/component with
this exact output delimiter and its full protective witness. The table's
release row is conditional on that association, not an invented transition.
The current query-judgment gap is already being audited in another lane and
is not re-proved here.

## Authority and exact dependency hashes

The committed approved `handler-protection-release-crossing/q1/d1` answer
fixes: release at actual outward source crossing after intervening processing;
same target while its original receiver remains active; no release caused by
consumption without crossing; preservation of attribution, full evidence and
other slots; no selection/capture/consumption/subtraction. It does not prove
the required source judgments or authorize compiler implementation.

All reads use this baseline, which equaled `HEAD` at collection.

| Source | Exact governing sections / baseline lines | Git blob |
|---|---|---|
| `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` | Exact approved decisions 1–7 | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Same directory, `receipt.md` | Validation; Outcome and reason | `154641f508ea224b5e907639e6c685b207cb3a84` |
| `notes/design/2026-10-02-source-realization-and-symbolic-basis.md` | §2, lines 39–81: supplied `Omega`, `Slots(b)`; §3, lines 112–119, 153–164: original admission slot versus observation port; §7, lines 486–511 and 546–587: ordered shallow control and output observations | `7c5fbf64af1cb46c44d612736c28907cadde3fac` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | §2, lines 44–60: source envelope; §3.3, lines 143–174: retained full source witness; §6, lines 313–345: original Force/body contribution occurrences | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §4, lines 388–472: executing view and pre-dispatch observation; §6, lines 669–753, 792–868: supplied profiles, original tags, receipt and query equations | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §3, lines 202–209: Force under current configuration; §4, lines 260–282: ordered search; §5, lines 400–436: shallow forwarding | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | §2, lines 94–114: handlers use current owner; §6, lines 399–448: outside-image equation, original-event forwarding | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| `notes/design/2026-10-02-source-computation-role-elaboration.md` | §8 original annotation coordinates; §10, lines 573–610: receive, retained input, entry Force and same invocation | `10775573537d8b56423f796db3c7ac6bb427e252` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §2 supplied typed derivation; §7 annotation/checking preservation | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-03-callback-context-delivery.md` | §§2–4 original static slot/profile, independently supplied formal, dynamic boundary and invocation view | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md` | Small-step / relational interpretation candidate, lines 89–149: independent attribution, emission and prior protection premises | `0b249e14d1ecb3bea076549b52af121478552491` |

## Concrete ordinary candidate, without claimed surface acceptance

Fix one assignment `nu` and retain its original `K,D`. Let `q` be one request
for `E : Unit -> Unit`, with origin `alpha`, event `epsilon` and a pure raw
suffix `k0`. An already constructed request thunk `t_E` exposes this event
when explicitly forced. A received delayed view `T=(value,position,evidence
root)` has supplied protected profile position `p_b`; its current Force
position is `p`, related by the supplied typed correspondence. There is one
original boundary `b`, with `b.receiver=r`, and no explicit contract admitting
`E` at that position. No independent second protection or grant is present.

The received delayed code may contain an inner handler `H_i` whose operation
coverage excludes `E`:

```text
delayed body of T: H_i[Force(t_E)]
ambient execution: Owner(r, H_o[View_o(T,p, delayed body of T)])
owner(h_i)=owner(h_o)=r
Covers(h_i,E)=false; Covers(h_o,E)=true
```

`View` and `Owner` are existing derivation/control notation. Forcing delayed
code runs under the current invocation; it creates no callee invocation by
itself. Handler installation uses that current owner. The outer handler is
installed by `r` before this explicit Force in its body. This is not an
ordinary Value-entry force moved under a handler installed later: retained
computation input and explicit body elimination preserve their selected order.

The exact boundary profile and typed decoration are supplied source inputs,
not inferred from this pseudocode. No public syntax, admitted marker spelling,
complete Function inequality or successful source checking is asserted.

At emission, the existing context rule records `Observe(q,T,p,o)`. The actual
receipt of this same `T` by `r`, its original protected profile and typed
Flow witness derive `Path(q,r,b,p_b)`. Both active candidates consequently
have a raw incidence. However the first candidate cannot be eligible because
it does not cover `E`. The existing source equation therefore applies:

```text
H_i[Request(q,k0)] = Forward(q, lambda a,Cnow. H_i[k0(a,Cnow)])
                    because q is not eligible at H_i's current boundary.
```

This is forwarding after the inner ordinary eligibility check, not an
accepted inner arm or a false guard. No concrete inner grant is needed, so
none can make the outer query eligible prematurely. Forwarding preserves
`epsilon`, `alpha`, payload and `K,D`; only the ordinary future handler
re-entry wrapper is appended. The original receiver `r` surrounds both
handlers and the Force delimiter, so leaving `h_i` and the Force output
does not end `r`.

## Existing output-observation bridge

Source-realization §7, lines 548–554, states:

> Add an output observation when a request crosses the particular
> invocation/force/handler output delimiter being summarized, or exits the root.

The following clauses distinguish consumption inside from consumption outside
that delimiter and retain the complete packet/suffix. Applied to this supplied
Force computation, the forwarded original `q` contributes a local output
observation at `T`'s Force output, before a later `h_o` image consumes or
forwards it. The inner handler's output is a separate earlier delimiter;
crossing it alone does not identify the marked Force slot.

This is an existing ordinary instruction and its local output projection,
not a new marked-delimiter rule. It is conditional on the resolved decorated
source envelope used by §7. That section does not generate the source
annotation/profile descriptors from arbitrary syntax. Its final `U`/row
projection is not used to decide whether to perform release.

## Owner/view/state table and conditional query arithmetic

Let `A` name independently established `'e` attribution, if such a source
derivation is supplied. Let `M` be the separately established association
between marker `s`, this exact target `T,p`, and the full original protection
witness. `A` and `M` are missing premises, not new machine fields. For the
following **conditional** table assume both, an initially unreleased target,
and no other protection witness. Only the approved crossing row may change
the slot's protection. Without those premises the release cells are unresolved.

| Stage | Active owners / handlers | Target and event evidence | Approved target protection | Outer eligibility calculation |
|---|---|---|---|---|
| Emit original `q` | `r`; `h_o,h_i` | `T,p,o`, `epsilon,alpha`, full Path/receipt, `A` unchanged | Protected; Observe is not crossing | Before-crossing comparison only: `P=1,G=0,Covers=1`, so false; no outer query is scheduled here |
| Test and forward at `h_i` | `r`; first `h_o,h_i`, then `h_o` | Same original event and observations; ordinary wrapper appended | Still protected; inner delimiter is not the supplied marked target | Inner query false because `Covers(h_i,E)=0`; ordered forwarding follows |
| Cross `T`'s Force output | `r`; `h_o` | Existing local output observation retains original packet; `M` identifies this delimiter if derived | **Released only here, conditional on `A,M`** | This is before the next outer query; no selection performed by release |
| Actual next query at `h_o` | `r`; `h_o` | Same `T` target association, `epsilon,alpha`, `A`, full evidence and `nu,K,D` | Released, conditional on preceding valid crossing | Substitution into `Visible`: `P=0,G=0,Covers=1`, so true |

Thus the approved protection behavior would distinguish the outer query
`false -> true` without changing its capture grant. This is evaluation of the
existing visibility formula at the specified protection states. It is not a
claim that the literal unrefined query definition already computes the new
state. That release-conditioned judgment is a separate audited dependency.
No handler selection, consumption, subtraction, attribution erasure or
receiver expiry is used to obtain the difference.

Minimality is conditional on the method: one event and one protective witness
suffice; a grant or an unreleased second witness can destroy the distinction.
One covering outer handler suffices if no intervening handler processing is
required. Retaining such processing adds one non-covering handler and no new
owner. This is a structural count, not a proof of a smallest admitted surface
program. A false-guard candidate with identical covering owners would be an
unnecessary and potentially nondiscriminating addition.

## Where marker association still fails

The new source inspection narrows, rather than repeats, the earlier open
premise. Original `Slots(b)` are explicitly supplied in source-realization
§2, lines 68–74. Section 3 retains the original admission slot while moving
an observation path; lines 157–159 explicitly distinguish that slot from a
marked current observation port. That word “marked” identifies the executing
position in the decorated kernel; it is not an introduction rule for public
postfix `?`.

Source-indexed-callback §6 records original occurrences `d-`, `d+` for the
designated Force-origin contribution and `b+` for body contributions. These
coordinates offer an existing independent source-origin anchor. They do not
identify an arbitrary public binder `'e` or the marker's released witness.
Moreover §2 excludes offered handler-image nodes in its envelope; that
endpoint theorem cannot by itself certify this handler-bearing candidate.

The exact missing clauses are:

1. An admitted annotation/interface derivation tying original component
   binder `'e` and marker occurrence `s` to this Force-output target `T,p`,
   preserving the original annotation/profile occurrence rather than equating
   a family or dynamic event name with the binder.
2. A source contribution derivation tying this original `q` to that component
   and selecting the intended full protection witness, including the actual
   original profile slot, typed Flow and receipt. Force-origin labels alone
   are an anchor, not the required public association.
3. A correspondence showing that the existing local output observation at
   that associated delimiter is the approved actual outward crossing before
   the next outside query. The ordinary output record supplies its source
   side; no additional delimiter transition is invented here.

Only after those clauses are supplied can the approved answer instantiate the
conditional protection row. The query-judgment refinement then consumes that
result. No fully source-derived distinguishing marked instance follows from
the inspected current clauses. Further supplied-predicate probes would leave
this exact association premise untouched, so this lane stops here.

## Checks, limitations, resources and next action

Checks were committed `git show`, `git ls-tree`, `git rev-parse` and bounded
`rg`/`nl`/`sed` source reads, plus an absent-path lease check. One guessed
source-realization filename did not exist; `git ls-tree` located the actual
`2026-10-02-source-realization-and-symbolic-basis.md` before inspection. No
missing source was silently treated as evidence. No dependency changed.

No test, build, executable experiment, random seed, enumeration range,
Git mutation, child delegation or shared-file edit occurred. Oracle
independence: this is a consequence of inspected candidate source equations
under supplied decorations, not an independent semantic oracle or proof of
those inputs. Query arithmetic is conditional on a valid release association;
there is no second checker sharing guessed transition rules.

Textual failure conditions: `h_i` covers/consumes `E`; another protected witness
survives; an explicit outer grant already makes the query true; original `r`
expires; inner output is mistaken for target output; or `'e`/marker attribution
is only family membership. No runnable mutation test was performed. Omitted:
accepted marked syntax, arbitrary role/profile elaboration, Function checking,
latent target continuity, deep/multi-shot histories and production conformance.
Processes were lightweight and sequential; peak CPU/RSS and exact wall time
were not measured.

Recommended next action: derive clauses 1–2 for this immediate Force-output
candidate using original source annotation/profile and contribution witnesses,
then prove clause 3 against the existing output-observation instruction. Do
not add another release-state probe before that source association exists.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-handler-release-query-discriminator.md`.
- Baseline SHA: `885939a8202190fb2d0d8ffe20cea16a17d16d56`.
- Dependency hashes changed: none by this worker; exact committed blobs listed above.
- Review status: frozen, unreviewed research; conditional discriminator and
  reduced source-association premise. No source acceptance, independent
  review, theorem closure or implementation authority claimed.
- Checks already run: committed-source and blob inspection, filename recovery,
  absent-path lease check; no tests/builds/executable experiments.
- Proposed one-line commit message: `research: locate release discriminator at existing force output`.
- Shared-record deltas intentionally left for primary/curator: distinguish the
  existing ordinary output-delimiter observation from missing public marker
  association; link the conditional no-grant/non-covering-inner candidate.
  Keep source acceptance and query refinement open. No shared records changed.
