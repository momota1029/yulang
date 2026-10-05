# Handler release: exact-packet re-entry and result-path transport

Date: 2026-10-06 (assigned artifact date; execution clock 2026-10-05 UTC)
Status: frozen, unreviewed research; conditional source derivation and reduced premise
Objective/method: extract typed-boundary and owner equations for the approved same-target-view release lifetime; structural derivation, no supplied-transition checker
Implementation authority: none
Exclusive lease: this file only
Task baseline: `121c257e78e3633fe86a9c135cd0c8662a6a892e`
Source pin: `659eb05646bb95f10a991bbb9cefdee55721eea1`
Decision pin: `28dddc75fd598faf34dd4d069ffb231cb64a82f1`, handler-protection-release-crossing q1/d1

## Result and claim classes

The pinned decorated source rules derive **exact-packet continuity on raw
re-entry**, including repeated resumption and the embedded raw resume in the
explicit deep expansion. They restore the original typed packet and port
while allocating a fresh execution observer. Executable owner resolution
does not rename the original boundary receiver or evidence roots. Conditional
on an already valid release and that exact original receiver remaining active,
the accepted lifetime therefore applies to this retained target without a
second crossing. This discharges a concrete subcase of the earlier continuity
premise, not marker attribution or crossing construction.

For Return/result projection and Force/result projection the source proves
**tagged protective-witness reachability**, not equality of typed view roots.
It explicitly constructs fresh result views and combines actual-value and
callee-result evidence. The smallest remaining premise is a source judgment
connecting the released marked target to a newly constructed result evidence
root, for one unary result-prefix removal. Boundary identity, path
correspondence, pointer identity and persistent origin do not themselves prove
that judgment. No new language meaning is selected here.

These are conditional results within reviewed Draft source candidates.
Neither this artifact nor its author independently certifies those candidates,
raw-source elaboration, full release realization, safety or principality. No
bounded executable characterization was performed.

## Governing sections and exact dependencies

- Typed-boundary §2, selected typed-value scope; §4, **Operational
  interpretation and proof**, **Typed value flow and computation observation
  are different path sorts**, and **Structural observation before dispatch**;
  §6, **Views, signature positions and introductions**, **One relational
  transport operation**, **Receiving ownership and observation**, **Transport
  and lifetime theorem package**, **Concrete realization and proof boundary**.
- Ordinary computation §2 bind equations; §3 closure/Force/ReturnFromInvocation
  and RebindResultPath; §4 exact current visibility; §5 **Primitive shallow
  image and explicit deep reapplication**.
- Typed-source-owner §§1–4: decorated input envelope, exact owner entry/leave,
  retained-view extension, non-renaming and preservation induction.
- Callback context §§1–4: original static slot/profile versus dynamic boundary,
  independently synthesized literal endpoints, retained Pure-value introduction
  and entry under its use-site view.
- Pinned hygiene notation **Intended reading** and **Small-step / relational
  interpretation candidate**, constrained by accepted q1/d1 clauses 1–7.

The decision fixes actual outward crossing after intervening processing,
same-target lifetime while the original receiver lives, no automatic transfer
to independently fresh targets/receivers, and preservation of attribution,
incidence/path, origin/event, attachment, row support and joint `nu,K,D`.
Release creates no grant, handler selection, capture, consumption or subtraction.

| Dependency | Pinned Git blob |
| --- | --- |
| Typed-boundary realization | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Ordinary computation | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Typed-source-owner realization | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| Callback context | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| Hygiene notation | `0b249e14d1ecb3bea076549b52af121478552491` |
| Approved q1 | `8409d932d27f8f77c0057c5ed85747ab77aff681` |
| Approved d1 draft | `4638f391203e71c33755c488caca33e3868275d3` |
| Approved answer | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Previous constructive attempt, at task baseline | `63cf77a14b0e42330c99f5cadb7cd0c1812fff25` |
| Previous falsifier, at task baseline | `3d92aabb67a44a76d1743038b93e2e183ef2faae` |

All listed dependencies match the task baseline and observed HEAD. The approved
question/draft/answer also match live bytes. Four source files match live bytes;
live hygiene notation differs: pinned SHA-256
`331943d5efb352ce29ee8d76d1d0238485f7d66d69a937e647db601cceab54db`,
live SHA-256 `87c2c39bf41a8b652fb96cb3409cf9e2c5735c96e4ccfc8b7c5b7f8380ba6050`.
Only the pinned notation is used. Previous attempts match baseline/live bytes.
Unrelated staged/worktree work was preserved.

## Extracted transport equations

A typed value view is `T=(v,t,e)`: underlying value, signature position,
evidence root. Its packet carries `(v,t,chi,K,D,L)`. Neither same `v` nor same
signature graph makes two evidence roots equal. An execution observer is a
separate occurrence `o` of `View(T,p,c)`.

For source-tagged input paths `i:p`, §6 defines:

```text
chi_out(p',b) iff exists i,p. chi_i(p,b) and M_i(p,p')
D_out(d,p')   iff exists i,p. D_i(d,p) and M_i(p,p')
K_out = shared input predicate ledger under the same nu
L_out = inherited origin/runtime identities
```

Each union retains its input witness/tag; no pointer-based source union is
allowed. The displayed incidence notation hides those tags, rather than
authorizing their deletion. A source retains its own evidence after transport.

The prose generation rules give these concrete correspondences:

```text
binding at unchanged type:       M_Id(p,p') iff p=p'
projection of component c:       M_c(c.p,p)
returned/forced result:          M_res(result.p,p)
```

`M_res` removes exactly the result prefix in the selected signature. For the
explicit example in §6:

```text
M_res(result.latent.effect, latent.effect)
not M_res(call.effect, latent.effect)
```

These equations concern returned values. A request emitted while calling or
forcing instead obtains an observation at the executing computation port.
For example, ForceThen(Id) from Thunk(E,Unit) to Unit may emit E even though
the returned Unit has no effect port. No result correspondence exists that
can turn that event into output-value protection.

A fresh result packet has two independently tagged input channels:

```text
chi_result = M_actual*chi_actual union M_calleeResult*chi_callee
D_result   = M_actual*D_actual   union M_calleeResult*D_callee
```

The callee channel uses matching result paths; it cannot extend an outer call
annotation to every latent descendant. The actual-value channel remains even
when the callee result contributes no profile. These are not new boundaries;
an actually executed callback boundary introduction allocates its own fresh
`b=(r,a,Gamma,endpoints)` separately.

Requests later exposed in the returned packet require their own current
Observe and a matching Receive for the candidate owner:

```text
chi_initial(p,b) and Flow*(T:p,T_n:p_n)
and Observe(q,T_n,p_n,o_n)
and Receive(u,slot,T_n,matching correspondence)
  => Path(q,u,b,p)
```

Current incidence additionally requires exact activity of `h`, `u=owner(h)`
and `b.receiver`. This implication does not identify `T_n` with `T`, does not
reuse an old event's Observe edge, and does not transfer an old owner receipt
to a new owner without an actual new receipt.

## Derived witness-composition lemma

Fix one decorated finite source execution prefix and one joint `nu,K,D`.
Assume its typed correspondences and original receiver identities are supplied
by the reviewed source input contract. Fix an original tagged profile witness
`alpha=(i_alpha,b,p_alpha)`, where `i_alpha` is its input view root and
`p_alpha` is its particular original profile position. Incidence below retains
the tag for this witness; equal `b` values at another position do not satisfy
membership for `alpha`.

For a chain of actual typed edges `M_1,...,M_n`, define `Reach_alpha(T_n,p_n)`
to mean that this particular input witness has a path through those edges to
the output position. It is a name for an existing evidence derivation, not a
new carrier or a definition of same-target release. Expanding the images gives:

```text
Reach_alpha(T_n,p_n) iff
  alpha is retained in the tagged input incidence at (i_alpha,p_alpha,b)
  and exists p_1,...,p_(n-1).
    M_1(p_alpha,p_1) and ... and M_n(p_(n-1),p_n)
```

Proof: the unary case fixes the selected source witness and applies its
correspondence, so `Reach_alpha(T_1,p_1)` requires both tagged input incidence
for `alpha` at `p_alpha` and `M_1(p_alpha,p_1)`. Substituting the induction
hypothesis into the next image associates the existential witnesses while
keeping this source position fixed. At a multi-input result, retain the source
index and apply the same argument to that branch. No branch or profile
position is inferred from another branch's equal value, boundary or family.
The identical induction transports each `D(d,p)` witness
with its original predicate identity in `K`. Prefix removal and identity are
instances; an absent correspondence produces no witness. This proves
composition, identity and source-union distribution for protective evidence.

Since the original `b.receiver` reference is unchanged, filtering this witness
by the same receiver's activity commutes with its path image at a fixed query
configuration. It does not assert liveness across two different configurations.
No release fact occurs in this proof. Substituting Reach for the approved
same-target premise would be a new, unproved identification.

## Exact-packet raw-resume subtheorem

Hypotheses:

1. A valid outward crossing has already released marked target `T` associated
   with original receiver `r`. Marker/full protective-witness association and
   independent attribution are supplied; neither is reconstructed here.
2. A saved raw suffix contains `View(T,p,K)` crossed by the actual capture.
   The source restores this saved frame without an intervening operation
   constructing a replacement target packet or replaying boundary entry.
3. The exact original receiver `r` is active when the later eligible
   observation is queried. The later contribution independently qualifies
   for the marker; ordinary candidate/path/receipt conditions still apply.

**Conclusion:** restoration enters a fresh `o'` of the exact same `T,p`.
The accepted same-target lifetime applies; a new observer/event does not require
another crossing. The conclusion applies on each finite repeated resume for
which the hypotheses hold.

Derivation by saved-context constructors: Hole supplies the response/current
configuration. Bind appends the saved suffix by the ordinary request-bind
equation. View explicitly restores the original packet/port and allocates
only a fresh executing observer. Owner resolves to its saved live owner or a
fresh execution owner; typed-owner §3 forbids either branch from rewriting
`b.receiver`, profile roots, stored typed views, request data or `K,D`.
ForwardHandler installs its prescribed fresh handler under the resolved owner,
without introducing a callback boundary. No constructor renames `T`. Nested
contexts and ambient resumer views remain separate. Completion removes the
restored observer; it does not rename a packet retained in another binding.

If `r` is the expired owner, owner re-entry can allocate `u'` but cannot revive
`r`; hypothesis 3 fails. If a new source call later executes a fresh boundary
entry, its new witness is separate. Old handler incidence also cannot be
reused by the newly installed handler. These are source-derived distinctions
between a fresh observer, a fresh executable owner, and a fresh boundary.

For explicit deep expansion:

```text
wrap_H(k) = lambda a. D_H[Resume(k,a)]
D_H[c] = S_(H with continuations bound as wrap_H)[c]
```

Unfolding introduces a fresh shallow handler around the resumed computation.
Its embedded Resume uses the theorem above on each retained raw View. The
fresh handler does not rename that packet. Actual wrapper calls or callback
entries can supply additional new views/boundaries; no result here copies
release to them. This is conditional preservation through the exact expansion,
not blanket preservation through every source adapter in a deep helper.

Likewise directly executing a retained latent packet by Force opens that
packet's own force view. Its fresh observer is compatible with the theorem's
identity argument. The value returned by the force uses `M_res`, and therefore
falls under the separate fresh-result premise below. Bare Return/bind passes
the value unchanged; typed ReturnFromInvocation/result rebinding may project
its packet and may end the original receiver. These steps must be distinguished.

## Smallest unresolved premise: one unary result edge

Remove all secondary inputs, handlers, recursion, pointer aliases and extra
receivers. Supply one live `r`, one already released marked target `T_0`, one
original witness `alpha`, and one result correspondence:

```text
T_0 has alpha at result.latent.effect
T_1 is the fresh output result view
M_res(result.latent.effect, latent.effect)
chi_1(latent.effect,b) has the original tagged alpha witness
r remains active
```

Given the supplied initial release and receiver-liveness premises, the source
derives the displayed result-path/profile transport and preserves `b.receiver`,
joint `nu,K,D` and inherited lineage. It does not give a judgment concluding that the
approved released target continues as `T_1`. In particular the view triples
can differ in signature position/evidence root even with the same underlying
value. Literal equality of triples is too strong to discharge general typed
result transport; equality of `b` or Reach is a weaker evidence property whose
equivalence to target continuity has not been proved.

The exact missing premise is:

```text
this marked-target derivation at T_0
  -- this actual result-path source step -->
this target derivation at newly constructed evidence root e_1
preserves the original released target rather than introducing a fresh target
```

It must be proved with the marker occurrence and full protection-witness
association available. A fresh independent marker/slot must remain separate
even when its path or profile matches. For multi-input results, the same
judgment must classify each retained source channel separately; the union law
cannot supply that classification. This is a minimized missing inference,
not a counterexample to the accepted semantics or a claim that retained tags
cannot express it. One unary prefix-removal edge suffices, so enlarging toy
path/filter enumerations cannot settle the premise.

## Independence, scope, checks and resources

Method independence: this derivation reads actual pinned source equations,
including their explicit original-packet re-entry rule. It does not compare
two checkers implementing supplied release transitions. The reference is the
reviewed decorated source candidate; expected lifetime comes separately from
the committed approved answer. Both share supplied source decorations,
marker/witness association, attribution and exact original receiver identity.
Thus oracle independence from raw Yulang elaboration is not established.

Coverage: finite correspondence chains and finite saved-context derivations;
Return/bind, Force execution versus result projection, raw repeated resume,
fresh/borrowed execution owners and explicit deep unfolding. No random seeds,
numeric enumeration ranges, executable mutations or semantic probe processes.
Named shortcuts rejected by the derivation are exact-view equality across all
fresh result packets, treating every Flow as certified target continuity,
owner re-entry renaming old receivers, and fresh observer identity resetting
an unchanged packet. These are logical exclusions, not mutation-test results.

Failure conditions: changed source dependencies; absent corresponding result
path; replaced packet; independently fresh marked target or boundary entry;
expired original receiver; nonqualifying later contribution; missing current
owner receipt; or incomplete marker/full-witness association. Other active
protection remains and can still block a candidate. Nothing here establishes
which source crossing originally triggered release.

Unverified: all raw syntax/profile elaboration, arbitrary inferred/recursive
shape applicability, marker association, source-derived crossing, general
fresh-result target continuity, all multi-input release interactions,
Function membership, attachment/subtraction bridge, finite abstract identity
correlation, compiler behavior, soundness and principality. No incomplete
enumeration/search is represented as complete.

Checks run: read-only pinned `git show` section reads and `rg` locators; Python
byte comparison using `git show`/`git rev-parse` versus baseline, HEAD and live
files; focused note whitespace/lease inspection. Initial large context reads
were output-truncated; substantive proof sections were reread with bounded
section reads. No tests, builds, formatter, benchmark, Git mutation or scratch
artifact. Only this leased note was written. Budget: at most 15 minutes,
text-only lightweight processes; CPU time and peak RSS not instrumented; zero
heavyweight processes and zero performance samples. Writes stopped before
submission for frozen review.

Recommended next action: derive the marked-target continuity judgment for the
single unary `M_res` step above, starting from the original full protective
witness, then extend it by the proved source-tagged composition law. Preserve
the exact-packet raw-resume subcase as already derived within its hypotheses.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-handler-view-transport-proof-attempt.md` only.
- Baseline: `121c257e78e3633fe86a9c135cd0c8662a6a892e`; source/decision pins and blobs above.
- Dependency changes: no committed dependency changed; live notation differs at the recorded SHA-256 and was excluded from authority.
- Claim/review status: frozen unreviewed research; conditional raw-reentry derivation, protective-witness composition and minimal result-target premise; no gate closure or production authority.
- Checks already run: pinned source reads, baseline/HEAD/live blob-byte checks, focused whitespace and lease inspection; no compiler tests/builds.
- Proposed checkpoint message: `research: derive handler exact-packet reentry and isolate result continuity premise`.
- Shared-record deltas left to primary/curator: record exact-packet raw re-entry and embedded deep Resume as derived conditional subcases; retain the one unary result-root continuity premise and marker association/crossing gates; distinguish fresh observers/owners/boundaries; reference this frozen artifact after adjudication. No task, theory, index, authority or question-board file edited.
