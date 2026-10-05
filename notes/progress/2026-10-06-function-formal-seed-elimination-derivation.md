# Function-formal seed elimination: bounded source derivation

Date: 2026-10-06
Status: Reviewed conditional research derivation; no semantic or implementation authority
Reviewed-by: `compiler_referee` (bounded semantic derivation review; no findings)
Baseline supplied by primary: `ea7146a5a5ef6edffe56fe258576ec4f15bbc862`
Lease: this file only
Method: one documentary derivation pass; no executable search
Gate: binder/use-indexed discharge of the provisional Handler view for unannotated `f`

## Objective and result

Determine what the approved sources entail about eliminating the provisional
Handler view in `apply f x = f x`, without changing supplied callable roles or
turning an ordinary Value entry into a general Pure classification.

They entail the required outcome for this example, together with preservation
conditions. They do **not** determine a unique binder/use-indexed elimination
rule or its extension to other source shapes. The new bounded result is a
separation between (a) the required example instance, (b) the missing eligibility
and aggregation premise, and (c) three candidate trigger predicates that agree
on that instance but disagree on two minimal use records. These records are
logical witnesses of an unspecified trigger, not accepted/rejected Yulang
programs or complete alternate language models. No candidate is selected.

## Governing sources and dependency snapshot

The assigned sources are:

- `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5: Authoritative
  direction, explicitly incomplete source judgments; especially §3's example
  and §5.2's outstanding two-stage rule.
- `notes/design/2026-10-03-callback-context-delivery.md` §§1–4, including §2.1:
  Authoritative bounded callback B; actual role/entry preservation in §4.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6,9: reviewed
  Draft construction, used below only relative to its lexical/typing premises.
  Its parameter roles are attributed there to charter §21; this assignment
  does not independently audit the charter or all annotations.
- `questions/2026-10-05-function-call-view-formation/{question.md,approved-answer.md}`:
  approved a2 Option 2, especially items 2–6. The primary supplies the validated
  integrated bundle as authority; this worker does not perform question-board
  validation or Git operations.
- `notes/progress/2026-10-05-handler-function-role-resolution-skeleton.md`:
  primary identifies this as the previously reviewed conditional artifact;
  `tasks/current.md` confirms the reviewed audit and its still-open clause.
  Its retained header says unreviewed. Neither that historical header nor this
  derivative note constitutes a new independent review.
- `rules/design-authority.md`, `rules/research-lab.md`, `rules/git-concurrency.md`:
  authority, research-only lease, freeze and primary integration requirements.

The packet incorrectly named `2026-10-02-typed-computation-core.md`, which does
not exist. The primary confirmed the corrected `*-core-elaboration.md` locator.
This is a packet defect, not a semantic dependency change.

Reads used current stable files permitted by the packet, with these whole-file
SHA-256 values. No baseline/current equality is independently claimed: Git
operations are forbidden for this worker, so the primary retains the pinned
revision check. The same bytes were rechecked when this artifact was frozen.

| Dependency | SHA-256 |
|---|---|
| inferred-function-call-views | `2b04b178b08e8f4fbb74988c528eb1c324d89242c9e060e52cbbe2f14c8fd2f8` |
| callback-context-delivery | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| typed-computation-core-elaboration | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| function-call-view-formation/question.md | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| function-call-view-formation/approved-answer.md | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| handler-function-role-resolution-skeleton | `6688077c0214f9ac2da1e49a38430a4ec8c088d500ba3dc271048f550f699602` |
| rules/design-authority.md | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| rules/research-lab.md | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| rules/git-concurrency.md | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |

`tasks/current.md` near the formation gate and the relevant design-index entry
were locator/status context. `tasks/research-lab.md` was read as the startup
seed. They supply no additional elimination premise.

## Derivation and exact hypothesis boundary

Use metatheoretic names, not proposed compiler fields or evidence carriers:

```text
s                  original declaration/use component scope
b                  lexical binder for f
c                  direct call occurrence f x
F_b                one shared inferred callable-interface reference
xi = (nu,K,D)      the original joint assignment and incident constraints
Actual(v)          independently introduced callable role/entry facts
```

`Seed(s,b,F_b)` denotes the approved internal provisional Handler treatment;
`NonHandlerFormal(s,b,F_b)` denotes the approved inferred-formal conclusion.
Neither label identifies that provisional view with `Actual(v)` or equates
non-Handler determination with an effective Pure-port construction.

The documentary derivation is:

1. **Approved direction.** Inferred-call-views §3 and a2 item 2 require
   `Seed(s,b,F_b)` for the unannotated `f` in the example and require that its
   ordinary argument `x` yields `NonHandlerFormal(s,b,F_b)` during inference.
   Item 3 and §4 require the unannotated protection to remain explained by
   annotation absence, not an empty effect row. This is a required result and
   causal direction, not an already defined transition rule.
2. **Conditional source evidence.** Assuming the registered lexical endpoints
   and admitted parameter derivations of core §6, the ordinary parameter `x`
   has `Gamma_s(x)=Value(A_x)`. Its name occurrence synthesizes that same tag,
   hence `Result(I_x)=Comp(empty,A_x)`. This derives the source value evidence
   under the stated core premises. It neither assigns a concrete callable to
   `f` nor determines the entry of the callable represented by `F_b`.
3. **Conditional application obligation.** Core §6 relates the whole
   `Result(I_x)` to the parameter interface of the callable at the result of
   `f`, and creates the symbolic complete invocation relation. It does not
   derive input endpoint equality, an entry mode from the argument tag, or a
   receiver role from that relation. Core §9 retains entry, body and result
   behavior as a joint complete image under original constraints.
4. **Required indexing and sharing.** Inferred-call-views §2 and a2 items 4–5
   require source-resolved binder/use identity, the single interface, original
   static slots and paths, and jointly scoped `xi`. Therefore an admissible
   eventual rule must link the evidence in step 2 to the seed in step 1 by
   that source relationship. A successful pending comparison `Q` may supply
   neither the relationship nor a protection/receipt fact.
5. **First gap.** No inspected rule defines which source evidence is eligible
   to discharge this particular seed or how eligible evidence combines with
   other uses. Core steps 2–3 leave that predicate absent; §3 explicitly leaves
   the provisional-view and role-resolution judgments open; §5.2 explicitly
   requires their exact two-stage rule. The derivation stops before that rule.

Thus, once the source-formation hypotheses have registered the example,
the following is a **required specification instance**, not a proved general
inference rule:

```text
Example(s,b,c,F_b,xi) and Seed(s,b,F_b)
  and OrdinaryFormalNameValue(s,c,x,A_x)
  => required NonHandlerFormal(s,b,F_b)
```

`Example` restricts this statement to the approved source shape, with the
lexical relationship of its `f` and `x`. Writing this implication records the
approved requirement; it is not a construction of a derivation for it. Even
alpha-renaming preservation needs the source-identity transport premise.

## Minimal missing premise

The required local premise is a source judgment, provisionally written

```text
EligibleDischarge(s,b,c,F_b,arg,xi)
```

that connects **this provisional inferred-formal seed** with **this resolved
argument occurrence's ordinary-value evidence**. It must establish the
connection independently of `Q` and specify a discharge of the provisional
view on the same interface rather than a rewrite of an actual callable.
The seed-origin restriction is necessary: actual Handler introduction and
ordinary Value entry are compatible under callback B. No entry-only predicate
can make that distinction.

For the single approved occurrence, the missing premise can be restricted to
that occurrence. To extend it to a complete inferred source contract, one
additional part is indispensable: the rule must say whether one eligible use
suffices, all relevant uses must be eligible, or other source constraints can
block/qualify the conclusion. The scope of those uses and the meaning of their
combination cannot be inferred from the instruction to infer a shared contract.
Shared references demand correlated constraints; they do not select a
quantifier over the evidence.

This is minimal at the role-trigger projection. Completing it does not itself
construct final ports/profiles, establish preservation of provisional port
constraints, or prove a principal solution. Those are further gates.

## Three bounded candidate shapes and distinguishing consequences

All candidates below share these guards: an unannotated unresolved formal has
the approved provisional seed; the callee use resolves to its original binder;
there is one `F_b` and `xi`; argument tags are source-derived; actual callable
roles/entries, original protection and incident constraints are retained;
`Q` does not generate premises. These guards are preservation obligations,
not evidence that the candidates have sound implementations.

For illustration only, let `U_b` be a **supplied complete finite use record**.
The construction and closure of such a record are not proved here. Define
`V(c)` as source synthesis of that call's argument with outer `Value` tag,
not solved endpoint shape or actual callable entry. Record `C(c)` for an outer
`Computation` argument. Let `A(U_b)` recognize exactly the approved one-use
formal/name shape, conditional on consistent binder renaming.

| Candidate trigger | Additional candidate assumption | Consequence outside the approved example |
|---|---|---|
| `R_anchor: A(U_b)` | The approved shape is the only discharge case established by this partial clause. | A Value literal argument supplies no discharge via this clause; other cases remain open. |
| `R_some: exists c in U_b. V(c)` | Every independently synthesized Value argument to this provisional formal is eligible, and one such use suffices. | A Value literal can discharge; another Computation-tagged use does not by itself prevent this trigger. |
| `R_all: U_b nonempty and forall c in U_b. V(c)` | Every relevant use must have ordinary-value evidence before this discharge clause applies. | A Value literal can discharge for a singleton record, but a mixed Value/Computation record does not trigger this clause. |

These are deliberately different **eligibility/aggregation** hypotheses.
The final column says only whether the candidate discharge clause fires.
Failure to fire does not assert that the formal stays Handler, is rejected,
or has no other inference derivation. Each shape agrees with the prescribed
result on the one-use approved example, and none changes supplied callable
facts. The inspected source requirements do not select among them. No claim
is made that any candidate extends to a sound/principal language semantics.

Two minimal distinctions suffice:

```text
W_lit:
  U_b = { c_literal }, argument at c_literal = literal 0
  V(c_literal) = true; A(U_b) = false
  R_anchor = false; R_some = true; R_all = true

W_mixed:
  U_b = { c_x, c_t }
  argument at c_x = ordinary bound name x:Value(A_x)
  argument at c_t = retained name t:Computation(E_t,A_t)
  V(c_x) = true; C(c_t) = true; A(U_b) = false
  R_anchor = false; R_some = true; R_all = false
```

Core §6 supplies the *conditional* source-tag interpretation of literal `0`,
ordinary `x`, and explicitly retained `t`, relative to their admitted bindings.
The use records are source-rule test obligations, not executable source
programs with proven satisfiable joint Function constraints. In particular,
`W_mixed` imposes no assertion that a single actual callable admits both calls.
Nothing here selects entry changes or an adapter to make it do so.

`W_lit` is minimal for distinguishing an anchor-only clause from the two
Value-trigger extensions: one use suffices. `W_mixed` is minimal for
existential versus universal triggering on a nonempty complete record: with
one use they agree, so two uses with opposite source tags are necessary.
These witnesses show nonuniqueness of the **trigger projection under the
inspected requirements**, not nonuniqueness of completed Yulang inference.
No recursive use is needed to expose either distinction.

## Conditional preservation result and failure conditions

Assume a source-formation judgment supplies the original binder/use edges,
interface and constraints. Assume an elimination judgment uses those edges,
discharges only that provisional seed, and leaves `Actual(v)`, source entry
tags, protection facts and original `xi` incidences unchanged. Assume
transport preserves those references uniformly. Then elimination need not
change an actual callable role/entry or break interface sharing: all uses
still point to the transported image of `F_b`, and the actual-value facts
remain unchanged by hypothesis. This is a conditional preservation argument.
It proves neither the elimination rule nor satisfiability, an algorithm,
B-equivalence, or principality.

Named failure conditions for a proposed completion are:

- Its trigger consults only Value entry, or a solved type shape, without the
  inferred-formal seed origin and source use evidence.
- It derives an actual callable's Pure role from this formal's determination,
  or chooses a concrete Pure value as the cause of discharge.
- It treats provisional Handler as an irrevocable actual-role equation and
  then imposes a mutually exclusive non-Handler equation on that same actual
  fact. Ordinary constraint conjunction cannot explain the approved transition.
- It deletes provisional constraints/evidence without proving how the final
  shared interface preserves their relevant consequences and solutions.
- It makes role determination a protection-release operation, forces the
  protected row to empty, or permits arbitrary effect subtraction.
- It uses `Q` success to create a slot, path, receiver, receipt or grant; selects
  separate port witnesses; or replaces callback B with endpoint copying.

The `[io]` annotation example has a different annotation premise. It supplies
permission for its specified contribution, not an alternative role-elimination
proof and not evidence that any effect is actually removed.

## Evidence, resources and omissions

This is one documentary pass, not a search. There is no independent executable
oracle. The approved documents ground the required example and invariants;
the reviewed Draft core supplies explicitly conditional source-tag/call
premises. The candidate predicates all share those premises. A checker that
encodes one of them as a transition would only characterize its consequences,
not derive `EligibleDischarge` from source authority.

Commands run: sequential read-only `cat` of the three rules and assigned
sources; narrow `python3` section/header extraction and SHA-256 computation;
`rg -n` of the formation locators in task/index files; `python3` creation of this
leased note; and a final read-only dependency/hash/whitespace check. The first
combined source capture failed on the wrong core locator and exceeded the
capture limit. The corrected core §§6,9, approved bundle and omitted §9 text
were reread narrowly. No builds, tests, probes, formatting, Git operations or
children. Mutations, seeds and enumeration ranges are not applicable.

At most one lightweight local command was active. No executable searches or
heavyweight processes ran. CPU time, peak RSS and total wall time were not
measured. Dependency changes during this pass: none in the named snapshot;
changes relative to the supplied baseline remain for primary revalidation.

Unverified: full source acceptance for the witness records; existence or
uniqueness of a completed elimination rule; seed representation; final
role-directed ports; annotation/profile formation; recursive use closure and
scheduling; complete admission and Option 2 production conformance;
generalization/use transport; soundness, principality and B-equivalent solving.
There was no second toy attempt; the precise source eligibility/aggregation
blocker is returned directly.

Recommended next action: have the primary resolve a narrowly stated source
elimination premise, including whether Value literal evidence qualifies and
whether a mixed-use component blocks discharge, while retaining seed-origin
and annotation protection. Return unresolved alternatives through the normal
approval gate before implementing a transition.

## Commit packet for the primary

- Exact leased path: `notes/progress/2026-10-06-function-formal-seed-elimination-derivation.md`.
- Baseline: `ea7146a5a5ef6edffe56fe258576ec4f15bbc862`.
- Dependency hashes changed during the pass: none; snapshot values above.
  Baseline equality is not worker-verified; primary must recheck it before
  integration. The core locator correction is recorded as a packet defect.
- Claim/review status: frozen unreviewed research-only derivation and bounded
  trigger underdetermination; no independent review, theorem closure,
  semantic selection or implementation authority.
- Checks already run: exact named source coverage, dependency stability/hash
  check and leased-note whitespace/hash check; no tests/builds/probes.
- Proposed commit message: `research: bound function-formal seed elimination premises`.
- Shared-record deltas intentionally deferred: describe eligibility and
  use-aggregation as the missing source premise in the existing formation
  gate; reference the literal and mixed-use discriminators without selecting
  a rule. Primary/curator owns `tasks/current.md`, theory-map/index and queue
  changes. No question-board bundle changes are proposed by this worker.
