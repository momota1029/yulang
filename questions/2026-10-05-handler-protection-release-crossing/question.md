# Handler-protection release crossing and lifetime

Question ID: `handler-protection-release-crossing`
Question revision: `q1`
Predecessor/history: none; complements the approved `function-effect-row-denotation` answer and the selected local `?` meaning recorded in the handler-hygiene notation draft
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `dfd49d1b14a9aba922bb0278ca7c1bfac8061058` (the governing source files below are unchanged through `d0a57e847`); the current handler-hygiene draft has uncommitted edits and is not treated as new authority
Task/thread locator: unavailable: this is the active goal to complete Yulang type-inference theory and replace inference
Governing source/section: `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md`, “Intended local reading”, “Small-step / relational interpretation candidate”, “Nested/Shallow/Deep/Pure-value examples”, and “Open questions”; `notes/design/2026-10-02-typed-boundary-realization-draft.md` §§2, 4, 6; `notes/design/2026-10-02-ordinary-computation-semantics-package.md` §§3–5; `notes/design/2026-10-03-callback-context-delivery.md` §§1–4; approved `questions/2026-10-05-function-effect-row-denotation/approved-answer.md` clause 6

## Requested scoped decision

Define (1) the source transition at which a qualifying, already `'e`-attributed contribution leaving the marked slot loses that slot's handler protection, and (2) whether this release applies to later qualifying observations through a transported latent/resumed target view while the original receiver remains active, or only to the specific contribution/execution occurrence that crossed the slot.

The decision changes handler protection only. Preserve provenance, event identity, family/type arguments, row support, typed paths, attachment and the original `(nu,K,D)` relation. It does not select a handler, grant capture authority, consume an event, or subtract row support. Receiver expiry still ends that receiver's protection; release must not revive expired authority.

## Background and current premises

- The existing selected local reading of `'e?` removes the marked slot's handler protection from qualifying `'e`-derived contributions that leave that slot, while retaining provenance. It is not optional membership, a flow edge, handler selection, or subtraction. See the frozen notation draft at the source revision above.
- The approved effect-row answer distinguishes covariant and contravariant meanings and requires role/typed-port selection before interpretation in one `(nu,K,D)` fiber. It does not define the source crossing or the release lifetime.
- Typed-boundary §4 forms `Observe` before handler filtering. Thus an enclosing view may observe an event that an intervening handler consumes; observation alone does not prove an outward crossing. Typed-boundary §6 transports typed paths/profiles but has no marker-specific release equation.
- Ordinary computation §§3–5 define invocation, shallow/deep dispatch and resumption, but do not connect those transitions to the marker's protection state.
- A source audit found no derivation of a unique release point or lifetime from the displayed rules. The existing conditional protection filter works only when a release predicate over the full protective witnesses is independently supplied. The current design gap is summarized in `notes/progress/2026-10-05-handler-protection-release-bridge-derivation.md`.

## Options and consequences

### Transition point

1. **At the marked executing-port emission before handler dispatch.** Once a qualifying contribution is emitted at that typed slot, remove that slot's protection before ordinary active-handler search. An intervening handler may then see an unprotected event even if it later consumes it. This gives `Observe` a candidate role only when a separate source rule also certifies the emission and marked-slot attribution; `Observe` alone remains insufficient.
2. **At an actual outward crossing after intervening computation/handler dispatch.** Remove protection only when the source transition establishes that the contribution has crossed out of the marked slot. An event consumed before that crossing does not trigger release. The rule must identify the crossing without defining it circularly through the post-release handler image.
3. **Another exact transition.** Specify the source state, event/contribution identity, marked slot, order relative to handler selection and outward support, and the evidence proving the transition.

### Lifetime across transport and resumption

A. **Target-view scoped.** Release attaches to the marked target view and remains effective for qualifying later observations through its typed result/latent transport while the same receiver is active. Specify how shallow raw continuations, deep re-entry, and repeated resumption preserve or instantiate that view.
B. **Occurrence scoped.** Release applies only to the qualifying contribution/execution occurrence that crossed the marked slot. A later event from a returned latent view or a fresh resumed execution needs its own qualifying crossing; shared family, lineage or packet identity alone does not carry release.
C. **Another exact lifetime.** State the retained object/evidence, transport rule, receiver-lifetime boundary, and behavior for fresh events created by shallow/deep re-entry or resumption.

The transition and lifetime choices interact. In particular, pre-dispatch release can expose an event to an intervening handler, while an outward-crossing rule cannot release an event that the handler consumes first. A view-scoped lifetime may affect future latent calls; an occurrence-scoped lifetime may leave later calls protected. Choose one item in each subsection or supply a complete alternative that resolves both traces below.

## Distinguishing traces to answer

1. **Intervening handler:** a marked output view encloses a computation that emits `q`, and an inner active handler consumes `q` without re-emitting it. Does the marked slot release protection before that handler's eligibility check, or only after an outward crossing that never occurs? Preserve the pre-dispatch observation and the full protective-witness identity.
2. **Returned latent view and resumption:** a marked result view is transported to a later invocation while the original receiver remains active; that invocation exposes a qualifying `'e`-attributed contribution and may suspend/resume. Does the earlier release affect this observation, or must this execution establish a new crossing? State the corresponding shallow raw-suffix and explicit deep-reentry behavior.

## Affected work

Blocked scope: deriving an executable release predicate from typed-boundary evidence; claims about nested/shallow/deep protection timing, returned latent views, resumption lifetime, complete annotation elaboration, any principality comparison depending on those rules, and production implementation.

Independent authorized work: the production Function-inlet context-domain question and pointwise admission bridge; pure structural/residual work independent of handler release; source/API inventory and other gates that retain explicit supplied release predicates.

Required answer: select the transition point and lifetime (or provide one exact alternative) with the two trace outcomes, preservation invariants, receiver-expiry behavior, and scope exclusions. This selects no family-wide release, new carrier, complete effect membership rule, or compiler implementation.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent authorized work continues on disjoint owned paths.
