# Unannotated callable role resolution: conditional rule skeleton

Date: 2026-10-05
Status: Unreviewed conditional research derivation; stops at an unfilled source rule
Baseline: `61a3651376166346a5baa03ec6679c310b0edbdb`
Lease: this file only
Method: source-indexed derivation and constraint-sharing obligations; no executable model
Authority: no new source semantics, solver algorithm, implementation, soundness or principality claim

## Objective and exact claim class

For `apply f x = f x`, connect the approved internal treatment of unannotated
`f` as a fully protected effect-returning Handler Function with its later
determination as non-Handler from the ordinary value argument `x`. Ask whether
the connection can retain one shared inferred interface without changing the
actual role or entry of a supplied callable.

The answer is **conditionally yes at the level of shared references**. The
necessary connection is an inference judgment about this unresolved formal,
distinct from rewriting an already introduced callable. Its decisive
role-elimination premise is not supplied by the inspected source rules. This
note identifies that hole and does not fill it. The conditional sharing lemma
below is bookkeeping under explicit hypotheses, not a proof that the source
rule exists or that a solver can find a solution.

## Pinned authority and dependencies

Read from the baseline revision, not concurrent edits:

- `questions/2026-10-05-function-call-view-formation/{question.md,answer-draft.md,approved-answer.md}`:
  approved a2 items 1–6, especially ordinary-value evidence in item 2,
  annotation-dependent protection in item 3, and remaining rules in item 6.
- `notes/design/2026-10-03-callback-context-delivery.md` §§1–4:
  role before port interpretation; normative literal B; actual callable role
  and entry preserved under a callback view.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6,9:
  syntax-directed parameter tags, one `Result` normalization, whole argument
  constraint, and complete invocation distinct from body/result support.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2–3,10:
  whole-tuple constrained interpretation, retained incidences and independent
  admission. These are conditional contracts, not selected formation rules.
- `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`
  §§13,16–18,21,24: transport, inert arguments, source tags and receiver-role
  distinction; §24 supersedes §16's universal Handler classification.
- `notes/design/2026-10-02-typed-boundary-realization-draft.md` §6:
  applicable profile positions, no grants from omission/wildcards, typed view
  transport and receipt/observation prerequisites. Its construction is Draft.
- `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md`,
  “Intended reading” and “Small-step / relational interpretation candidate”:
  protection release is separate from membership, attribution and subtraction.
  This optional frame reference supplies no role-elimination premise.

The governing decision selects inference from declarations and uses. It does
not select the detailed generation rules or a unification algorithm. Existing
production membership Option 2, denotation Option A and admission independent
of comparison `Q` remain premises; this note proposes no replacement for them.

## Names and minimum judgments

All names below are metatheoretic labels for obligations, not new compiler
fields, public types, evidence carriers or solver states.

Let `s` be the original declaration/component scope, `a_f` the value endpoint
for parameter `f`, `a_x` the value endpoint for `x`, and `F_f` the single
inferred callable-interface reference attached to `a_f`. Let `c` identify the
source call occurrence `f x`. Keep one original binder tree and
`xi = (nu,K,D)`. The declaration-to-`F_f` link, static slot `beta_f`,
`Slots(beta_f)` and all typed paths are formation obligations, not already
constructed objects.

The minimum obligations are:

```text
Param_s(f) = Value(a_f)        Param_s(x) = Value(a_x)
Gamma_s(f) = Value(a_f)        Gamma_s(x) = Value(a_x)

Lookup_s(f) references the same a_f and F_f
Lookup_s(x) references the same a_x

Seed_s(f,F_f,NoAnnotation,ProtectedHandlerResult)
SourceValueUse_s(c,x,Value(a_x),F_f)

CallableAt_s(a_f,F_f)
ArgumentAt_s(c,F_f,Result(Value(a_x)),typed-path obligations)
InvocationAt_s(c,F_f,Result(Value(a_x)),Comp(e_c,a_c),xi)

EliminateSeed_s(f,c,F_f,SourceValueUse_s(...),xi,NonHandler)  [HOLE]
```

`Seed`, `SourceValueUse` and `EliminateSeed` only name the requested source
obligations. Their meanings and admissible derivations are not defined here.
In particular, `Seed` is not silently an irrevocable equation asserting that
an actual supplied callable has Handler role. `NonHandler` records only the
approved conclusion; this note supplies no complete Function-port rule for it.
The complete source rule must explain the precise relation of that conclusion
to the existing Pure/Handler receiver classifications.

`ArgumentAt` is deliberately a relation to the whole argument computation.
It does not impose equality between `a_x` and a callable input endpoint, or
between the input source tag and the callable's entry role. Ordinary inequality,
checking or adapter evidence must come from the independently specified rule.
`InvocationAt` does not equate `e_c` with a body row, or stipulate a row union.

## Derivation to the first missing rule

1. By charter §21 and core §6, both unannotated binders generate `Value`
   parameters with fresh value endpoints. Their bindings after their owning
   entry rebind are `Gamma_s(f)=Value(a_f)` and `Gamma_s(x)=Value(a_x)`.
   The owning entries and their source tags cannot be revised by later endpoint
   solving. This does not determine the entry of the callable denoted by `f`.
2. The two name occurrences retain their lexical roots. Core §6 gives
   `I_f=Value(a_f)` and `I_x=Value(a_x)`, hence
   `Result(I_f)=Comp(empty,a_f)` and
   `Result(I_x)=Comp(empty,a_x)`. This establishes ordinary-value evidence for
   the occurrence of `x`. It assigns no concrete function value to `f`.
3. Approved a2 item 2 requires the internal protected-Handler treatment of
   unannotated `f`; item 3 fixes absence of annotation as its protection reason.
   Record that requirement against the same `F_f`. Neither item defines how
   that seed is represented or eliminated. Applicable effect positions still
   require source profile formation; “fully protected” supplies neither an
   empty effect endpoint nor blanket protection of every latent descendant.
4. Core §6's application row requires a Function interface at the result of
   `n_f`, relates the whole `Result(I_x)` to its parameter interface, and
   introduces `Computation(e_c,a_c)` under complete invocation obligations.
   The argument is reified inertly. Even this value-tagged name is passed as
   a whole carrier; the actual callable owns its entry demand. The tag
   `Value(a_x)` is static evidence, not force-before-receipt execution.
5. Approved a2 requires that this ordinary-value use makes `f` non-Handler.
   The inspected rules yield step 2's value judgment and step 4's call
   obligations, but supply no inference rule deriving that conclusion for
   this seed. **Stop here.** The missing clause is exactly
   `EliminateSeed_s(f,c,F_f,SourceValueUse_s(...),xi,NonHandler)`.

There is no derivation in this note of a completed `F_f`, its four effect/value
ports, a solved `beta_f` profile, or a final scheme for `apply`.

## Exact sharing and unification obligations

The missing rule must operate on the seed's original `F_f`, not create a second
unrelated interface for `f x`. The binding occurrence, callable constraint,
value-use evidence and eventual exported formal must refer to that same root.
Likewise the argument lookup and argument relation retain the same `a_x`.
Repeated uses inside this component retain the registered references; their
constraints are conjoined at the original scopes.

One legal whole substitution/freshening must act on value endpoints, effect
endpoints, slot/profile references, typed paths, owner/receiver incidences and
every incident `K,D` predicate together. “Shared” does not mean all these
coordinates are equal. It means they retain their original correlations and
witness scopes. An input endpoint relation cannot be replaced by equality
without a source rule or an equivalence proof.

The seed must not freeze the actual receiver role as an ordinary equality
that later endpoint unification purports to reverse. The smallest logical
obstruction is a single root carrying both `role(F_f)=Handler` and
`role(F_f)=NonHandler`, where these classifications exclude one another:
the conjunction is inconsistent. This is a representation-obligation witness,
not a Yulang source counterexample. Choosing a deferral, refinement, elimination
or other solver mechanism to avoid it is outside the assignment.

Existing callable values retain their introduction role and entry. If a
completed inferred formal is later used as a callback slot, the original
actual-value interface and the checked slot view remain distinct operands of
their concrete comparison. Sharing the inferred formal never licenses
assignment of the formal's role to the actual value.

### Conditional sharing lemma

Assume a source formation rule supplies the registered interface root and
original binder/incidence graph. Assume a source-derived elimination rule
discharges only this inference seed on that same root, leaves ordinary
parameter tags and all actual-value role/entry facts unchanged, retains the
annotation-derived protection obligation, and is independent of `Q`. Assume
generalization and use apply one legal uniform transport to all those references.

Then recording the required seed and its discharge against that root does not
require a second inferred interface or a rewrite of an actual callable role.
Proof: every binder/use reference remains incident to the original root;
discharge introduces no replacement endpoint or actual-value role equation;
uniform transport maps each shared reference to the same image and preserves
the unchanged actual-role facts. This proves the stated preservation under
the hypotheses. It proves neither existence of the formation/elimination rules,
satisfiability of their constraints, effective solving, soundness nor principality.

## Dependency order, without selecting a scheduler

The justified partial order is:

```text
resolved binders / annotation presence / original scope
  -> parameter Value tags and shared endpoint references
  -> ordinary-value name evidence and source call obligations

annotation absence + shared unresolved F_f
  -> protected-Handler seed

seed + value-use evidence + missing source elimination clause
  -> non-Handler determination of this inferred formal
  -> completed role-directed F_f / applicable profile formation
  -> any dependent completed-interface comparison
```

This states logical prerequisites. It chooses no propagation order for endpoint
constraints and no policy for solving a recursive component. If the seed is
interpreted using provisional ports, a further proof must show their relation
to the final role-directed interface without deleting solutions or changing
evidence. Protection due to annotation absence must remain accounted for;
the role conclusion alone is no protection-release or subtraction rule.

For a dependent callback literal, first obtain the completed instantiated
expected context with original slot/profile. Then deliver it before body
generation, select Handler for that literal, independently synthesize its
endpoints and compare completed `F_lit <: F_cb`. Any cyclic dependency or early
propagation needs its own B-equivalence justification. The inference seed for
`f` does not turn normative B into endpoint copying or post-body literal role
selection.

## First blocker and discriminating failure conditions

The first blocker is the binder/use-indexed source clause that distinguishes
this unresolved formal's seed from actual Handler introduction. Core §6's
`Value` versus `Computation` tag is available; the rule interpreting that tag
as seed-elimination evidence is not.

A universal rule “ordinary value argument implies Pure receiver” fails the
authority check: callback-delivery §2 selects Handler for an unannotated
callback literal while independently generating ordinary `Value` entry from
parameter syntax. Its §4 `update` anchor even has a pure string body. Thus
ordinary value entry is compatible with an actual Handler introduction. The
new rule needs the inference-seed/formal premises rather than changing that
existing literal rule. This distinguishes the required rule, without selecting
its semantics or running a probe.

Other explicit failure conditions are: using a concrete Pure value assigned
to `f` as the reason for discharge; setting the protected effect endpoint to
empty; changing `x`'s source tag or an actual callable's entry; exporting two
independently solved `F_f` roots; freshening correlated ports separately;
creating a profile, path, receipt or grant after observing `Q` success; or
using non-Handler determination to authorize effect subtraction.

For `apply(f: _ -> [io] _, x) = f x`, the accepted contract permits `io`
removal. It proves no removal executes here and licenses no other family.
The absence-of-annotation seed premise does not apply unchanged to that form;
its annotation formation rule remains outside this derivation.

## Evidence, coverage and resources

No executable checker, oracle, mutations, seeds, enumeration or numeric search
range were used. Independence comes only from reading the committed approved
answer and pre-existing source rules; the conditional lemma shares its listed
premises with any later implementation. A checker implementing `EliminateSeed`
as an assumed transition would validate that transition's consequences, not
prove its source meaning.

Commands used: read-only `cat` of the three required rules; bounded `git show`
of the pinned question/design inputs; sequential `python3` extraction of named
sections, SHA-256 computation and current-file equality checks. Initial combined
captures exceeded output limits; the governing callback/core/contract sections
and the relevant truncated transport paragraph were reread in narrower captures.
Task/index matches were locator context, not a complete repository audit.
All direct inputs except the optional notation frame matched current file bytes
when checked. No builds, tests, probes, formatting, Git mutations or child
agents. At most one lightweight top-level command active; subprocess reads
were sequential. CPU time, peak RSS and total wall time were not measured.

Unverified: source elimination and its role classification; complete annotation
and profile formation; recursive scheduling; generalization/instantiation
correctness; complete production membership/admission; actual Function
inequalities; all source forms beyond this example; protection lifetime and
effect subtraction; soundness/principality. No attempted toy-model loop.

Recommended next action: specify the missing source elimination judgment with
its binder/use premises and retained protection frame, then independently check
it against actual Handler literals with ordinary Value entry before choosing
solver mechanics.

## Commit packet for the primary

- Exact leased path: `notes/progress/2026-10-05-handler-function-role-resolution-skeleton.md`.
- Baseline: `61a3651376166346a5baa03ec6679c310b0edbdb`.
- Claim/review status: frozen unreviewed conditional research skeleton; first
  source rule unresolved; no gate closure or implementation authority.
- Dependency change observed: optional
  `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md` differs
  from baseline SHA-256
  `331943d5efb352ce29ee8d76d1d0238485f7d66d69a937e647db601cceab54db`.
  Current content was not used; primary owns delta revalidation. Other named
  question/design dependencies matched baseline bytes at the check.
- Checks already run: pinned-source extraction and current dependency equality;
  no tests/builds. Primary retains whitespace and artifact hash verification.
- Proposed commit message: `research: record conditional handler-formal role resolution skeleton`.
- Shared-record deltas intentionally deferred: record the binder/use-indexed
  role-elimination hole in the formation gate; preserve protection formation
  and B-equivalence as separate obligations. Primary/curator owns
  `tasks/current.md`, any theory-map status, design index and laboratory queue.
