# EROW source profile to complete deep image: conditional construction

Date: 2026-10-06
Status: Frozen research-only conditional derivation; unreviewed; EBRIDGE remains open
Baseline: `95d5af37ae71cfeedda1b325159353b4c7b1a386`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: construct one source-indexed proof spine, then reduce its complete handler image
Implementation authority: none

## Objective and result

Connect the selected concrete mixed-row fragment to a role-derived polarized
port, an event-specific typed incidence, its existing attachment witness, and
a complete deep-handler image. The smallest construction uses one concrete
annotation occurrence, one callback receipt, one request, one resumption and
a non-latent Unit result. It assumes the missing annotation elaboration and
attachment premises explicitly. It derives output absence by reducing the
source handler expansion rather than supplying an output-reachability flag.

**Claim class: conditional derivation for that supplied source-core instance.**
The proof does not derive arbitrary mixed-row membership or the missing
annotation producer. The one-request instance also works shallowly; it does
not distinguish shallow from deep handling or establish a general deep row
law. The useful result is the explicit interface between the source producer
and the operational proof, including a separately discharged complete-image
obligation in this instance.

## Governing baseline and selected premises

The semantic inputs are:

- [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md)
  §1, role-first subsection; §7; §9. The document is Draft, with the listed
  user-selected decisions governing their declared scope. §9 selects the
  polarity-sensitive `['e, write int]` fragment and targeted deep removal;
  it explicitly leaves annotation-to-occurrence and complete-image proofs open.
- The committed [row-denotation answer](../../questions/2026-10-05-function-effect-row-denotation/approved-answer.md),
  q1/d1, decisions 2–6; its [receipt](../../questions/2026-10-05-function-effect-row-denotation/receipt.md)
  records integration at `cd7df4c0ef2603e9d566c9b0ec2580cab85ee975`.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§1–2.1, 3–4: known instantiated formal/profile is an input; B selects the
  literal's Handler context before body generation, independently synthesizes
  endpoints, then checks one `F_lit <: F_cb`. Entry remains syntax-directed.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–2: written annotation, inferred public interface and internal view are
  distinct; source position plus its contract supplies the static slot;
  the pending comparison cannot create paths, owners or authority.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §9, “Entry is part of the interface” and “Derive directions”: sign propagation
  on already typed interactions and complete invocation, with result consumer.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6, introductions, indexed transport, receiving ownership/observation and
  proof boundary. This document has no §8; the supplied prior capture note's
  “§§6, 8” locator does not identify an additional governing section here.
- [Ordinary computation](../design/2026-10-02-ordinary-computation-semantics-package.md)
  §§4–5: current-candidate visibility, outside shallow selection and the
  explicit recursive deep expansion. These are reviewed candidate source
  rules, not a completed source adequacy theorem.

The baseline theory dependencies label EROW a scoped contract, CAP conditional
on an established profile, EXE operational, and EBRIDGE open. The
[prior profile derivation](2026-10-05-concrete-capture-profile-derivation.md)
supplies CAP, not the annotation producer. The
[descriptor derivation](2026-10-05-function-effect-descriptor-derivation.md)
supplies the invocation skeleton, not mixed membership. The separate
[registration audit](2026-10-06-source-registration-constructive-derivation.md)
already isolates inferred-formal registration; this construction takes a
known formal and does not repeat that audit.

Selected facts are the role/context order, the scoped row fragment, the shared
assignment requirement, equal eligibility of direct and caller-Force requests
under the same explicit contract/incidence, and the explicit shallow-based
deep expansion. No selected fact says that every concrete row item creates
a capture grant, that the written row equals the inferred scheme, or that
the word “deep” supplies a new owner's grant.

## Smallest indexed instance and hypotheses

All labels below name existing source/evidence objects, not a proposed carrier
or compiler API. Fix one `xi = (nu,K,D)`, original binder scopes, and a nonempty
source solution fiber. `D` here is the dependency incidence, not a fresh
argument computation. Call the received computation `c`.

Take a resolved receiver taking a known `Value(F_cb)` callback formal and
invoking it once. An unannotated literal at this formal receives Handler
context by callback B. Exclude literal-annotation/context overlap. The formal's
written mixed-row occurrence contains abstract occurrence `epsilon` of `'e`
and concrete occurrence `sigma` of `write int`. Its completed inferred view
has the matching typed effect path. The receiver's complete offered interface
is the sign root; the formal argument reverses sign, while the callback call
effect preserves that sign:

```text
offered receiver (+)
  -- receives callback argument --> formal view (-)
  -- callback call effect -------> p_minus = arg.call.effect (-)
receiver complete call effect --> p_plus  = call.effect (+)
```

These are paths in the completed typed interface, not an assertion about raw
parser spelling. The callback's local profile position `p` is `call.effect`;
`p_minus` is its occurrence in the enclosing offered interface. An outer
annotation is not thereby copied to descendant ports.

The hypotheses are deliberately split:

| Premise | Exact content | Status |
| --- | --- | --- |
| H1: completed typed source interface | Resolved declaration/formal/use supplies `F_cb`, static `beta`, original `Slots(beta)`, the displayed paths, literal/body/result derivation and a valid completed B check. Roles precede ports; actual entry is separate. | Known formal and B order are selected; this complete interface construction is supplied, not derived here. |
| H2: annotation elaboration | Before the pending comparison, source evidence links `sigma` and `epsilon` to their corresponding completed port views at the same `xi`. At local `p`, the boundary profile explicitly admits the compatible `write int` operation instances for this scoped contract. The abstract input/output occurrences remain correlated views of the same source component, with all `K,D` and source tags. | Missing producer premise. Neither syntax shape nor row support establishes it. |
| H3: compatibility and attachment | The source operation declaration/instance admits payload `0` and an inhabited response endpoint with witness `a_star`. The matching `write 'a` contribution in the abstract view satisfies the selected example constraint `int <: 'a` at `nu`. Existing occurrence/path/subtraction evidence attaches the targeted contribution to `sigma` and this abstract view; it retains the operation tuple, source occurrence, continuation and ownership. | The required compatibility instance is selected; operation inhabitation and the exact attachment witness are supplied. No general family variance or old weight rule is inferred. |
| H4: exposure and current ownership | One dynamic receiver `r` activates `b=(r,slot,Gamma_b,endpoints)`. Handler occurrence `h` is owned by `r`. The executing callback view `v` has the corresponding profile, `Receive(r,slot,v,M)` and `Observe(q,v,p0)`, with a matching typed route from `p` to `p0`. At original request search, `r,h` are active; `h` is reached in ordered search and covers this operation. | Existing transport/visibility rules explain how to use these facts; their source allocation and observation are supplied. |
| H5: complete finite computation and handler | The complete designated consumer computation is exactly `Request(q,C,k)`, with `k(a_star)` returning Unit in the current resumed configuration. One total pure selector matches `q`, its pure arm invokes the supplied wrapped continuation once with `a_star`, and the pure value arm returns Unit. Matching/arm typing is valid. No other selector, arm, adaptation, consumer, latent result or external future use emits a request. | Restricted source-core instance, independently specified before checking the proposed reversal. It is not a general handler assumption. |

H5 is a complete control description, not “the output row is empty.” It can
be represented using the already displayed `Request`, `Return`, ordinary bind,
raw `Resume` and derived `D_H` terms. Raw Yulang syntax/resolution for this
whole instance is not demonstrated. The `write` response type is not invented:
H3 requires an independently typed declaration/response witness and stops the
instance if none exists.

In H2–H3, a contribution need not have the annotation's generating occurrence
as its event origin. The annotation occurrence identifies the contract and
attachment; `q` keeps its distinct source origin, operation instance and fresh
dynamic event identity. Eligibility and attachment are different conclusions.

## Derivation

**1. Derive the signs, conditional on H1.** Typed-core §9 reverses a callable's
received carrier and preserves its offered complete call effect. Applying
those interaction clauses gives the displayed negative formal call-effect
port and positive receiver call-effect port. The row's surface spelling
does not select a receiver role or generate a sign. H1's B check relates
independently synthesized literal endpoints; none is copied from `F_cb`.

**2. Introduce and transport the established profile.** At actual receipt,
H2 and H4 instantiate the original source profile at fresh dynamic `b`.
For the shortest route, `M` relates `p` to executing `p0` without an intermediate
adapter. Typed-boundary §6 gives

```text
chi_v(p0,b) from chi_source(p,b) and M(p,p0)
D_v = M_*D_source; shared K and nu remain the original ledger/assignment
Path(q,r,b,p) from that route, Observe(q,v,p0), and Receive(r,slot,v,M)
Inc_C(q,h,b,p) from Path and current activity of h, r, b.receiver
```

No value pointer, family label, successful comparison, or unrelated alias
supplies any of these witnesses. This step transports H2; it does not prove H2.

**3. Establish event eligibility, then selection.** H2 admits `q.operation`
at `p` under the same `nu`, and H4 gives `b.receiver=owner(h)=r`.
Typed-boundary §6 therefore supplies `Grant(q,h,C)`. Together with coverage
and activity, its `Visible` clause admits this event even if protected.
H5's selector accepts and its separate selected-arm compatibility holds;
H4 says ordered search reaches `h`. The shallow source rule consequently
selects this arm and passes the original raw `k` after leaving `h`.

Changing only the generating route to caller-owned `Force` would preserve
this eligibility conclusion **if** it supplies the same complete-view
observation, typed receipt/path and current candidate premises. It does not
automatically preserve H3's particular attachment or H5's complete computation.

**4. Reduce the complete deep image rather than assuming its projection.**
Instantiate ordinary-computation §5's capture-avoiding expansion:

```text
wrap_H(k) = lambda a. D_H[Resume(k,a)]
D_H[c]   = S_(H with raw k bound as wrap_H(k))[c]

D_H[Request(q,C,k)]
  -> outside selector/arm receives wrap_H(k)
  -> wrap_H(k)(a_star)
  -> D_H[Resume(k,a_star)]
  -> D_H[Return(Unit,C_resumed)]
  -> outside pure value arm
  -> Return(Unit,C_final)
```

The second shallow occurrence is fresh. Neither the expired `h` nor its grant
is restored. H5 has no request in that resumed suffix, so this minimal reduction
does not need a grant for the fresh occurrence; extending it to a suffix request
would require its own current owner, profile, receipt and observation proof.
The captured continuation is resumed with current state, never a fabricated
snapshot. Selector/arm computation stays outside the respective candidate.

For every admitted initial configuration satisfying H1–H5, these clauses
enumerate all request-producing sites of this finite term. H5's single total
selector has no alternate request branch; the arm's only call is the wrapped
raw suffix; that suffix and the value arm return Unit; the designated consumer
is already included. No output event is generated. Unit has no latent
computation to expose on a later use. Thus the complete output image for this
instance has only these returns and their state/evidence, with empty request
support. This proof is conditional on the displayed reviewed source equations,
not a proof that those equations are adequate for raw source or production.

**5. Relate the removal to the original contribution.** H3 identifies the
consumed `q` contribution as the source-attached target of `sigma`. Step 4
independently rules out every surviving or newly produced request in this
instance, including another request with the same family/type point. These
two facts justify disappearance of this target from the abstract output
view's support. Its covariant representation may be flat without losing the
attachment, path, occurrence or dependent predicates from the full relation.

This is not reassignment of `nu('e)` between polarities or a global set-difference
operation on `'e`. The original source component and its input/output views
stay correlated at one `xi`; the handler image gives the output view. A
predicate in `K` remains wherever `D` still links it to a root, continuation or
other view, even though immediate request support here is empty. The exact
encoding as a witnessed reverse-addition step still needs the source-to-existing-
subtraction-evidence correspondence required by concrete compatibility §1.

## Precise missing producer and stopping boundary

The first unavailable conclusion is H2: from this resolved annotated formal
and its completed role-indexed interface, derive the comparison-independent
link of `sigma,epsilon` to their joint port views and the explicit source
profile at that original position. A fresh label, a concrete family head,
`TypedRow`, or an already supplied decorated source graph is insufficient.
The coupled-core candidate's `occurrences(R,nu)` and `ArgDen_A` start after
the occurrence inventory exists; they do not construct this link.

H3 then needs a distinct conclusion: derive the exact attachment of this
targeted contribution from existing source-owned occurrence/continuation/path
and subtraction evidence, preserving dependent operation arguments. Grant
proves permission to capture this event; it does not prove that attachment.
No missing information has been proved inexpressible by the existing carrier.

The complete-image calculation discharges a third obligation for H5's exact
instance. It leaves that obligation open for arbitrary handlers. In particular,
multiple or retained continuations, selector/arm re-emission, effectful result
consumers, forwarded requests and latent results need their own full images.
The deep expansion alone cannot prove a uniform output absence theorem.

No additional support probe or protection-filter algebra was run. Those
methods supply H2/H3 as inputs and would leave this first missing source premise
unchanged. This attempt stops at that precise producer boundary.

## Evidence quality, failures and unverified scope

No executable oracle, random seed, numeric search range, mutation run or
compiler check is involved. Independence is documentary: user approval fixes
the semantic target; the pre-existing source equations reduce H5 independently
of a proposed support deletion; H2/H3 are explicitly shared assumptions rather
than an independently validated source oracle. A checker implementing these
same equations would add consistency evidence, not prove the source rules.

The proof fails if the producer obtains H2 from the pending comparison,
identifies written and inferred types, uses family equality to create a path,
combines independently instantiated polarity witnesses, or calls event
eligibility an attachment theorem. The complete-image argument fails when
H5 omits an effectful selector/arm/consumer, a latent result, another possible
branch, or a new request after resumption. Extending the proof to a second
suffix event fails without a separately derived fresh re-entry contract;
the expired handler's grant cannot be reused.

Unverified: H1–H4 source producers, raw parsing/HIR acceptance of this schematic
instance, general mixed-component membership/admission, old weight-rule
correspondence, source and production adequacy, unknown/recursive interfaces,
annotation overlap, State/reference rules, arbitrary open clients, whole
Function containment, canonical normalization correctness and principality.
The tentative shallow principal type remains untouched.

Recommended next action: produce and review the H2 clause for this one known
annotated formal, with an exact source-occurrence-to-completed-port witness
and the original shared fiber, before expanding the operational envelope.

## Commands, coverage and resources

Read-only commands used `cat`, targeted `sed`/`rg`, `git show`, `git rev-parse`,
`git branch --show-current`, `git status --short`, `git diff 95d5af37a --` on
the approved answer, and `git ls-tree` on that answer. A sequential Python
hash inventory compared all direct document inputs with their pinned Git
bytes. It did not implement or test a semantic transition system.

The answer is unchanged and committed at the baseline, blob
`77e28d7826634421a98e556a0023b29c762420ad`. Its receipt is unchanged. All direct
semantic/proof/rule inputs below matched their baseline bytes at the inventory.
Live task/theory-map files were concurrently modified; their pinned versions
were used for EROW/EBRIDGE classification. An initial broad task/index capture
was truncated; later narrow pinned searches supplied the cited gate entries.
An attempted `rg --files spec` failed because this worktree has no `spec/`
directory. No exhaustive repository or specification search is claimed.

No tests, builds, probes, formatting, Git mutations, children, temporary output
files or shared-record writes were performed. Commands were lightweight;
independent reads used at most four concurrent command processes, with no
heavy process. CPU time, peak memory and total elapsed wall time were not
measured; no numerical resource budget was supplied. Only this lease was
written. Semantic dependency recheck at integration remains primary-owned.

| Direct pinned input | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d` |
| `notes/progress/2026-10-05-concrete-capture-profile-derivation.md` | `a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79` |
| `notes/progress/2026-10-05-function-effect-descriptor-derivation.md` | `90a48c21b7ec2775557b545eae7d30b4f0fd73e3dfddf4dd6a643627bdc493ae` |
| `notes/progress/2026-10-06-source-registration-constructive-derivation.md` | `b4d15fd017085f0b58836be544c576d1ce94b1f869482496d1c0507eecd24bd9` |
| `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` | `032849b8bc8e9398889ed589be9e7598252f53924346de31175538e533bee997` |
| `questions/2026-10-05-function-effect-row-denotation/receipt.md` | `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-erow-source-profile-construction.md`.
- Baseline SHA: `95d5af37ae71cfeedda1b325159353b4c7b1a386`.
- Changed direct semantic/proof dependency hashes: none at the inventory above.
  Pinned locator files were read independently of their live edits:
  `tasks/current.md` baseline `a323b77dee861026965357580d989be5afc638417296b4c8ed7c604f0d4b6da9`,
  observed live `a0ea6b8c8a9041457651eb86195cac039d63185cbfdb4fa2cc06836c57e26676`;
  `notes/theory/inference-theory-map.md` baseline
  `b600cdec8033d5ec340ba059d27d9a45db07c41c8dc3f560eb4a09c2b8e3bc56`,
  observed live `f0e85bcdf7efc3113c1e437f2ad02ffec8b730b4067b56403165d0cb4e402de8`;
  `notes/theory/inference-theorem-dependencies.md` baseline
  `5ecd639ae33943c86937b7783da97da5471bdc67205b8c9c619ac9ba7edd4f38`,
  observed live `708885dbd29e2677ebb336dbe82cb5ee246409fa4b013444ddcf3faf58170b99`.
- Review status: unreviewed conditional research artifact; producer claims no
  independent review, theorem closure or production conformance; writes stop
  before frozen review.
- Checks already run: committed/unchanged approved-answer verification;
  direct-input baseline byte comparison/SHA-256 inventory; narrow authority,
  port, visibility and deep-expansion source reads. No executable checks.
- Proposed commit message: `research: construct conditional EROW profile-to-deep-image spine`.
- Shared-record deltas left for primary/curator: link this conditional instance
  under EBRIDGE/CAP; retain EBRIDGE open, distinguish missing H2 profile
  elaboration and H3 attachment from the H5 complete-image subcase; record
  no general subtraction, independent review or implementation promotion.
