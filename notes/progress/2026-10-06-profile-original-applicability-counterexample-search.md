# Original applicability at the captured outer formal: bounded falsifier search

Date: 2026-10-06
Baseline: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`
Status: frozen on submission; unreviewed research-only search
Claim class: bounded source-introduction audit; no source-valid counterexample found
Scope: P for `my apply f = { my step x = f x; step }` only
Exclusive output: this note
Semantic / implementation authority: none

## 1. Objective, method and result

Search for an additional **original** applicable position or contribution at
the exact unannotated outer formal's shared contract, while retaining the
approved source meaning. The attack is a manual source-origin audit: for
each possible introduction in the selected source, require an actual source
rule connecting that introduction to `beta=(d_f,R_f)`. Descriptor paths,
inherited packets and runtime observation are insufficient witnesses.

No source-valid falsifier was found. The parameter declaration itself remains
the precise unresolved case: it establishes the source formal and its Value
entry, but the governing profile-introduction clause takes the applicable
signature profile as an elaboration input. The current sources prove neither
that this input must contain a second position nor that it contains only
`p_0`. This is a bounded failure to produce a witness, not the universal
converse, source underdetermination, or proof that a user decision is needed.

The earlier P completeness falsification §4 already considered an abstract
inherited-result pair. That attack is not repeated here. No second toy graph,
descriptor pair, event trace or semantics proposal is presented as a source
counterexample.

## 2. Baseline, authority and exact falsifier obligation

Governing sources and retained decisions:

- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §§2–5, with its §1.1 distinction between written annotations and inferred
  views; approved `function-call-view-formation/q1 a2` items 1–6. Form the
  shared contract from relevant source declarations, definitions and uses;
  preserve original scope and joint `xi=(nu,K,D)`; annotation absence causes
  full protection at applicable positions. Ordinary-value evidence refines
  this formal/use relationship without changing a supplied callable's role.
- [Exact nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–4 and approved nested-block answer a1. Sequential binding returns
  `step`; its body captures the same outer `f`; the final Name is not a call.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3/10. The constructor inventory and C-realization theorem are relative
  to independently interpreted decorated inputs and their conformance
  certificate. They do not construct arbitrary raw-source profiles.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6. Boundary introduction receives a signature profile; transport retains
  tagged input witnesses; receipt creates ownership only; observation and
  liveness realize protection. This Draft package is a conditional
  mathematical input, not authority to choose new source rules.
- [P normal-form construction](2026-10-06-profile-source-normal-form-construction.md)
  §§3–6 and [conditional P construction](2026-10-06-profile-P-exact-candidate-construction.md)
  §§3–6. Their least-generated footprint and conditional transport claims
  are retained at their stated scope. The former's source completeness
  converse is the object attacked here.

The reviewed initial construction supplies

```text
C = the exact approved source component
c = the sole application f x
beta = (d_f,R_f)
p_0 = (beta,call.effect)
ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))
```

The proposed converse is

```text
Applicable_original(C,d_f,R_f,p;xi)
  => p = p_0 and ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c)).
```

A position falsifier must derive the left side at an original, jointly
well-formed fiber and exhibit `p != p_0`, using a source introduction
within this same component. A contribution falsifier must exhibit an
original source contribution at this `beta` that the elimination origin
does not account for. An inherited fact can retain the same static `beta`
label from another use/activation; label equality does not make it a fresh
introduction by this source. No disjoint-namespace assumption is made.

The positive initial-address result is an established input from its recorded
independent review. This note adds only a bounded audit. Neither candidate
`Foot-Call` leastness nor full-profile H1/H2/H3 is promoted to an established
source theorem.

## 3. Source introduction cases checked

The exact selected skeleton has two Lambdas, one Bind, three Names, four
Results and one Call. The search checks introductions associated with those
source nodes, including their formal declarations, rather than enumerating
possible solved Function shapes.

| Proposed source of another original fact | Source test | Outcome and limit |
| --- | --- | --- |
| Outer `my apply f` declaration | Does an ordinary Lambda/definition introduce another applicable position at its formal's `beta`? | It registers the Lambda/body/provider and `d_f`. Inferred-call-views §2 allows declarations to contribute constraints but gives no declaration-to-profile inventory rule. No additional fact follows; exclusion is also unproved. |
| Unannotated outer formal `f` | Does parameter syntax itself expose/protect a latent descendant? | Typed-core §6 generates `Value(A_f)`, one entry/rebind skeleton and symbolic endpoints. Its explicit limit is that this outer role does not determine all nested paths. This is the surviving unresolved introduction. |
| Inner formal `x` | Can its parameter introduction create a position at outer `beta`? | It has its own `d_x` and Value endpoint. Its use returns the already rebound value. No source rule joins its parameter contract to a fresh outer-`f` profile position. Equal endpoint shapes would not supply that incidence. |
| Written annotation / concrete capture permission | Is an original annotation occurrence present at `f`, its result or a descendant? | None occurs in the exact source. The explicit `[io]` alternative is a different source. A normalized public inferred type is not a newly written annotation. Absence still requires a rule deciding which positions are applicable. |
| Contextual Handler introduction for either Lambda | Is `apply` or `step` an inline literal in a known callback slot? | Neither occurrence is such an argument literal in the selected tree. Callback delivery §2 requires a supplied expected callback context; §4 preserves an existing callable's actual role. Supplying a new annotated surrounding application is outside this fixed component and needs a separate correspondence argument. |
| Capture, sequential binding, returned `step` | Do these create a fresh source boundary/profile? | The selected rules retain the original roots and transport supplied packets. Capture remains private, and the final Name does not invoke `step`. No new original position is introduced by these operations. Actual packet attachment remains a separate premise. |
| Complete invocation: entry, provider body, designated consumer | Do several possible event origins require several original signature positions? | `Gen-Call-0` designates the complete-invocation effect port. Entry/body/consumer observations can contribute through this same port; distinct events alone do not derive distinct positions. The complete original contribution catalog is still unverified. |
| Primitive / operation / reification / explicit elimination / Handler source introduction | Does such an introducing source node occur here? | None occurs in the exact selected skeleton beyond the sole Function Call. A supplied provider or ambient graph may contain these nodes; its evidence enters as inherited input, not a demonstrated fresh introduction by `C` at `beta`. |

Two details prevent misleading candidate witnesses. First, an effectful
carrier supplied to outer `apply` is forced at `apply`'s Value entry before
its `f` binding is established; that execution is not an extra original
position of the callback value merely because the argument returns `f`.
The returned value may carry its own inherited packet. Second, specializing
`A_f` so the result contains a Thunk or Function creates structural paths
in the dependent descriptor, but typed-boundary §6 requires independent
source applicability at matching result paths. Result projection does not
map `call.effect` to `result.latent.effect`.

These are conditional exclusions of the proposed inference shortcuts under
the named rules. They do not exhaust unspecified raw-source elaboration
rules. In particular, the first two table rows are bounded stops rather than
claims that declarations or formals can never contribute other positions.

## 4. Precise blocker and failure conditions

The strongest remaining candidate is the **implicit source callback
introduction at unannotated `d_f`**, before capture and later invocation.
Typed-boundary §6 introduces

```text
b = (receiver r, callback slot a, signature profile Gamma, type endpoints)
```

where `Gamma` marks exactly the applicable computation positions. Its next
paragraph says profiles are supplied by source elaboration and arbitrary
syntax-to-profile derivation remains open. Core §6 supplies the parameter's
outer Value role; core §9's bounded metadata construction explicitly retains
supplied typed-profile/path entries. Neither supplies the missing map

```text
SourceFormal(C,d_f,NoAnnotation,R_f)
  -> complete original applicability/contribution relation at beta.
```

Consequently the attempt to build a second original position stops before
its first `Applicable_original` judgment. Setting `Gamma` to contain a latent
position would assume the sought witness. Setting it to `{p_0}` would assume
the converse. No current source rule selects either solely from descriptor
reachability, role refinement, annotation absence or a successful comparison.

The search result ceases to apply if the primary supplies a relevant
declaration/formal introduction rule or a certified extension to the source
component. Such a rule must be checked on its actual hypotheses. A receiving
event, an inherited packet, or an abstract descriptor mutation alone does not
invalidate this result because none meets the falsifier obligation in §2.

## 5. Independence, checks, coverage and resources

Oracle independence: no frozen Oracle code, run or inferred output selected
semantics or supplied a witness. The manual audit shares the approved source
meaning and the named conditional typed-core/typed-boundary contracts with
the constructive P lane. It is a different search method, not independent
certification of those contracts or of the author's own note.

Commands used: bounded `cat`, `sed`, `rg`; read-only `git rev-parse HEAD`,
`git status --short`, `git diff <baseline> -- <dependencies>`, and Python
standard-library hashing with `git show <baseline>:<dependency>`. The twelve
direct dependencies in §6 all matched pinned bytes when checked. The exact
leased path was absent before creation. A final metadata check verifies the
note's relative links, final newline, absence of trailing whitespace and
unchanged dependencies. This is document validation, not source-semantic
execution.

Coverage: one exact source tree and the eight source-origin candidates in
§3; no program enumeration, random seeds, numeric ranges or executable
mutations. Conceptual mutations considered are adding a written annotation,
adding a contextual callback application, choosing a latent result shape,
and equating inherited evidence with fresh origin. The first two change the
fixed source/dependency component; the latter two lack source introduction
evidence. No mutated program is asserted accepted or run.

Omitted: arbitrary external declaration/use components, recursive local
groups, all-source annotation elaboration, source acceptance by production,
actual capture/receipt attachment, contribution completeness even at `p_0`,
admission A, all-view principality, and production Option A/2 containment.
The initial broad `tasks/current.md` capture was truncated; only its opening
P/A state was used, with original governing sources subsequently read
directly. No claim rests on its omitted contents.

Resource limits: bounded manual/search only; zero test/build/Oracle/probe
processes and no heavyweight process wave. Short reads and hashing were the
only local processes besides this note write. CPU time, peak RSS and exact
wall time were not instrumented; no numerical allowance was provided.

Recommended next action: have the source-rule constructor lane supply the
implicit unannotated-formal introduction rule and derive its applicability
inverse at this `beta`. Repeating an assumed-profile executable model would
leave exactly this premise untouched. This search alone warrants no semantic
question-board escalation.

## 6. Commit packet

- Exact leased/change path:
  `notes/progress/2026-10-06-profile-original-applicability-counterexample-search.md`.
- Baseline SHA: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`.
- Dependency hashes at baseline/submission: the SHA-256 table below.
- Changed dependency hashes: none observed; primary must recheck before
  integration if HEAD advances.
- Review status: frozen, unreviewed research-only bounded search; no
  independent certification, gate closure or implementation permission.
- Checks already run: original governing-section inspection, source-origin
  audit, pinned-byte checks, output absence check, and final document metadata
  check. No tests/builds/Oracle or Git mutations.
- Proposed commit message:
  `research: audit original applicability falsifiers for captured formal`.
- Shared-record deltas intentionally left for primary/curator: retain P open
  at implicit formal/declaration source introduction; record that no
  source-valid additional position/contribution was found in this bounded
  exact-source audit. Do not promote singleton completeness, source
  underdetermination or a new semantic decision. No task/index/authority,
  theory map or question-board file was edited.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-profile-P-exact-candidate-construction.md` | `ee3a5ed1ba657c2f7828ef409ba3cf052899d709394ce203c9473bcf73ca0358` |
| `notes/progress/2026-10-06-profile-source-normal-form-construction.md` | `74604c54f23efc406d5359cd4e2dfcc946065d8b01071874ea8c0945116fce05` |
| `notes/progress/2026-10-06-profile-P-completeness-falsification.md` | `48addb7eb95ebd704dd05aa578375e54920917fe0cb9a9066ca3885cf41d6b0b` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
