# Call-view source rules: constructive derivation and premise inversion

Date: 2026-10-06
Status: Frozen unreviewed research-only derivation attempt; no implementation authority
Baseline: `38de8cb146ba0f08fd034f8a6657d68879c9a5d4`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: forward source-skeleton derivation paired with backward rule-premise inversion

## Objective and result class

Determine whether the existing source/type/effect introduction and call rules
construct a complete role-indexed callback Function view for unannotated
`apply f x = f x`, including its protected provisional Handler treatment and
ordinary-value determination as non-Handler.

**Bounded negative derivability result:** the inspected displayed source rules
construct a conditional source-tag/result skeleton, but do not discharge the
source registration and decoration premises of a complete call view. The
first missing premise for the complete-view goal occurs before the already
reported seed-elimination hole: registration of the inferred formal's one
shared role-indexed interface with its original static slot/profile, typed
call path and correlated source constraints. This is a dependency audit, not
proof that a suitable rule cannot exist. No complete Function interface,
accepted-program counterexample, soundness result or principality theorem is
claimed.

Earlier notes already identify the missing seed-origin/eligible-use clause and
show that the approved example does not choose eligibility or use aggregation.
This note does not repeat their trigger candidates or toy experiments. Its
additional result is the forward/backward separation below: ordinary-value
source evidence is available without executing `f`, while the conditional
complete-view theorems require independently supplied decorations and cannot
serve as formation rules for those decorations.

## Authority, baseline and stable dependencies

Governing sections:

- Approved formation answer a2 items 1–6 and its integration receipt: Option 2
  source inference; annotations optional; preserved source identity and joint
  scopes; comparison-independent admission.
- Authoritative inferred-call-views §§2–5: source formation direction;
  provisional protected Handler treatment and the required ordinary-value
  conclusion; annotation-dependent protection; concrete judgments still open.
- Authoritative callback-context-delivery §§1–2.1,4: role before port
  interpretation, known instantiated formal as a premise, callback-literal B,
  actual supplied callable role/entry preservation.
- Typed-core §§6,9: **Draft construction**, with independently reviewed
  conditional results; syntax-directed source tags and whole-argument call
  obligations. Its displayed rules are used relative to their lexical and
  typing premises, not as newly approved inference semantics.
- Source-generated theorems §§2.1,3: decorated source kernel and query-independent
  admission certificates are inputs to the conditional theorem.
- Source-contracts/common-allowance §§2.2,3.1–3.3,10: active constrained-root
  hypothesis and decorated emission/admission inventory; production/source
  adequacy remains open.

Option A denotation and production membership Option 2 remain fixed. No
additional members, rejection boundary, receiver role meaning, source syntax,
carrier, scheduler or implementation is selected. In particular, the approved
`io` annotation permits removal of its specified contribution and does not
assert removal or permit unrelated subtraction.

The read-only `git diff --exit-code BASELINE -- <direct dependencies>` returned
0 before writing. These direct dependencies therefore matched the pinned
baseline's tracked bytes. The final hash check checks pass stability; the
primary must recheck them at integration. `tasks/current.md` around the active
formation gate and `notes/design/INDEX.md` were locator/status context, not
proof premises. The packet's numeric “current task §§36–44” does not correspond
to numbered headings in this baseline; the active callback/formation paragraphs
around lines 949–997 were inspected instead. No unrelated pending answer was
consumed.

| Dependency | SHA-256 at freeze |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `2b04b178b08e8f4fbb74988c528eb1c324d89242c9e060e52cbbe2f14c8fd2f8` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-05-handler-function-role-resolution-skeleton.md` | `6688077c0214f9ac2da1e49a38430a4ec8c088d500ba3dc271048f550f699602` |
| `notes/progress/2026-10-06-function-formal-seed-elimination-derivation.md` | `e65825e917b7bebee3f3eec2b4c67d5c359903aa4255966f1a8bf53e745ef0fa` |

## Forward derivation: available evidence and exact hypotheses

Use metatheoretic labels only:

```text
s          original declaration/use scope
b_f, b_x   resolved parameter binders
c          body call occurrence f x
A_f, A_x   fresh value endpoints of those parameters
xi         one original jointly scoped (nu,K,D)
```

Hypotheses H1–H3 are explicit:

1. H1: the ordinary definition/parameter and name occurrences have their
   resolved lexical identities, with the scope and parameter derivations
   admitted by typed-core §6. This note does not construct a raw resolver.
2. H2: the definition body is elaborated using that core's ordinary expression
   rules, with unknown endpoints retained symbolically.
3. H3: if the application row is used, its existing callable, argument-path
   and complete invocation typing obligations are retained as obligations;
   they are not assumed solved by source shape alone.

Under H1–H2, ordinary parameter generation and name lookup give:

```text
P_apply,f = Value(A_f)      Gamma_s(f) = Value(A_f)
P_apply,x = Value(A_x)      Gamma_s(x) = Value(A_x)
I_f = Value(A_f)           I_x = Value(A_x)
n_f = result(name b_f)     n_x = result(name b_x)
Result(I_f) = Comp(empty,A_f)
Result(I_x) = Comp(empty,A_x)
```

The two parameter entries above belong to the enclosing definition. They do
not identify the entry or receiver role of the callable denoted by `f`.
`A_x` may later be latent or recursive without changing `I_x`'s Value tag.
`Comp(empty,A_x)` is the name occurrence's normalized computation; it is not
proof that every incoming carrier to `apply` or every invocation of `f` has
empty effect support.

Under H3, the application rule produces the candidate skeleton:

```text
I_c = Computation(E_c,A_c)
d_c = reify(call(n_f,n_x))
n_c = Normalize(I_c,d_c)
```

with a callable-interface obligation at `A_f`, a relation of the **whole**
`Result(I_x)` carrier to the callable parameter interface, and the complete
invocation relation that determines symbolic `E_c,A_c`. There is no justified
input equality, row union, actual receiver-role equation or slot assignment
in this step. The callable owns its actual entry; the argument remains inert
until that entry demands it.

Thus ordinary-value evidence is a static conclusion at name synthesis, before
any need to execute `f`. It does not depend on a concrete Pure function later
supplied for `f`, `Q` success, successful force, a request observation or runtime
receipt. This removes a possible circular reading of “value is passed”: runtime
execution is not necessary to derive the available Value tag. It does **not**
prove which inference rule consumes that tag.

The protected provisional Handler treatment and its non-Handler determination
are established requirements of the approved example. Taking those requirements
as example axioms yields the desired example conclusions by assumption, but
still supplies neither their source judgments nor a completed profile/view.
They cannot be presented as theorems derived from the core application rule.

## Backward inversion: the first unsupplied complete-view premise

Let the desired result be a complete inferred formal view with original
`F_b`, `beta_b`, `Slots(beta_b)`, source-linked call path, owner/receiver
incidences and one original `xi`. These names describe required objects,
not a proposed compiler representation.

| Attempted last rule | Premises exposed by inversion | Why forward evidence does not discharge them |
| --- | --- | --- |
| Callback-context-delivery §2 | Known callee; already instantiated `F_cb`, original `beta`, `Slots(beta)` | `f x` supplies a callable obligation at symbolic `A_f`; it is not a known callback literal or a supplied completed contract. |
| Typed-core §6 application | Existing typed path/contract obligations and complete invocation relation | The application row introduces those obligations, not their source-to-role/profile solution. |
| Source-generated theorem §2.1 | Decorated owner/view kernel, source witnesses supplied before `Q` | That theorem explicitly does not derive decorations from raw syntax. |
| Source-generated theorem §3 Initial | Locally typed whole carrier with declared result port, profile/path, compatible context and joint `xi` | `Value(A_x)` supplies a source tag/result skeleton only; it does not construct the profile/path or compatible context. |
| Source-contracts §3.2 Name/Lambda/Call | Resolved provider roots; actual role/entry; receiver/receipt/body/consumer and original incidences | The inventory preserves source-supplied data; §3.1 assumes it. It is not a rule for assigning the provisional formal's role or constructing all incidences. |
| Source-contracts §2.2 | Presented active membership/admission/provider clauses interpreted jointly | It interprets retained clauses; it cannot supply missing source clauses or their initial binder links. |

The first missing local formation premise can therefore be named:

```text
RegisterFormalView(s,b_f,c,A_f,NoAnnotation;
                   F_b,beta_b,Slots(beta_b),typed_paths,incidences,xi)
```

This is a hole label, not a defined judgment or extra evidence carrier. It
must explain which relevant source component registers the common interface,
how absence of annotation supplies the protected provisional view, and how
source identities/scopes/correlated constraints reach the call occurrence.
It must be independent of `Q`. A fresh symbolic value endpoint for `f` does
not by itself discharge this judgment. A syntactic location identifies an
occurrence but does not prove its complete effect-profile inventory or receiver
incidences.

After this registration hypothesis is supplied, the earlier notes' separate
hole remains: consume this call's ordinary-value evidence to discharge this
inferred formal's provisional Handler treatment on that same interface,
without changing actual supplied callable roles or losing protection/evidence.
The dependency is therefore:

```text
source binder/name/argument tags                         [conditional core]
source registration + provisional protected formal view  [missing formation rule]
registered view + ordinary-value evidence                [missing discharge rule]
completed role-directed profile and call-view            [further proof obligations]
independent admission and concrete comparison            [later gates]
```

This orders prerequisites, not a solver schedule. Literal B remains normative
once its expected context has been obtained. No early endpoint copying or
post-body literal-role repair is justified.

## Bounded conclusion and discriminating failure conditions

For the displayed rule families inspected here, a derivation using a last rule
in the inversion table must supply that row's existing premises. The forward
skeleton discharges only source tags/results and generates symbolic callable
obligations. None of those displayed conclusions constructs the registration
judgment's complete outputs. Consequently the complete-view goal is not derived
from H1–H3 by these rules alone. This is a finite rule-interface audit, not a
completeness proof for all repository rules or an impossibility theorem about
Yulang.

A proposed completion fails this gate if it:

- calls the conditional decorated-source theorem a derivation of its own
  decoration hypotheses;
- uses pending comparison success to create a slot, path, receipt or grant;
- replaces the whole argument relation by source-tag/entry equality;
- treats the enclosing `apply` parameter's Value tag as the actual entry of
  the callable `f`, or treats Value entry as a generic non-Handler proof;
- makes provisional Handler an immutable actual-role fact and contradicts it
  later, or solves independently chosen ports and combines their witnesses;
- drops full protection on role resolution, equates protection with an empty
  row, or turns the annotated `io` permission into actual/global subtraction.

Actual Handler introduction with ordinary Value entry is already permitted by
callback B; its role selection and parameter syntax are independent. This is
an authoritative compatibility check on any future rule, not a new witness
search. The previous eligibility/aggregation distinctions are retained without
re-running or enlarging them.

## Evidence independence, coverage, resources and omissions

Method: one forward derivation and one backward premise audit against existing
sources. No executable oracle, checker, mutation, seeds, numeric enumeration,
performance experiment, build or test was run. Source authority is independent
of this note; the conditional skeleton shares H1–H3 with a future implementation.
A checker that assumes `RegisterFormalView` or seed discharge as transitions
would test consequences, not prove those source rules. No new toy-model attempt
was made after the prior two derivations left seed eligibility untouched.

Commands: three-rule `cat`; `git rev-parse HEAD`; bounded `cat`/`rg` source
reads; sequential Python section extraction; the explicit baseline dependency
`git diff --exit-code`; Python hash/note creation; final Python hash/whitespace
check. Total budget: 12 lightweight top-level command processes, sequential,
no subprocess experiments, no heavy processes. A few initial locators used the
wrong design dates or receipt filename; they failed and were corrected from
approved source locators. Initial captures were truncated; core §6 was visible,
and the exact theorem §2.1 and contract §§2.2,3.1–3.3 used in the inversion were
reread narrowly. Task/index and earlier-note searches are incomplete repository
searches and provide no global absence claim.

CPU time, peak RSS and elapsed wall time were not measured. No process, memory
or timing measurements are claimed. Only this lease was written. No Git
mutation, compiler edit, test addition, formatter, child agent, interactive
question, shared status change or question-board write occurred.

Unverified: raw declaration/use resolution; recursive component closure;
registration/role-discharge semantics; provisional/final port correspondence;
annotation occurrence/profile mapping; generalization and use-time transport;
complete admission/membership, including Option 2 extras; actual Function
containment; uniqueness/principality; scheduling equivalence; source acceptance
outside this conditional ordinary core; production conformance.

Recommended next action: specify a narrowly scoped source registration judgment
for the approved `apply` component, with explicit outputs and an independently
formed evidence path from `I_x=Value(A_x)` to its provisional formal. Review
that judgment and its distinct discharge premise before using conditional
complete-view theorems or choosing solver mechanics.

## Commit packet for the primary

- Exact leased path: `notes/progress/2026-10-06-call-view-source-rule-derivation-attempt.md`.
- Baseline SHA: `38de8cb146ba0f08fd034f8a6657d68879c9a5d4`.
- Dependency hashes changed: none relative to the pinned direct tracked inputs
  at the baseline check; freeze SHA-256 values above. Primary rechecks at
  integration.
- Review status: frozen unreviewed research-only derivation attempt; no
  independent review, gate closure, new semantics or implementation authority.
- Checks already run: baseline dependency diff exit 0; narrow governing-rule
  and prior-result audit; final dependency hash/lease whitespace check. No
  tests, builds, probes or formatting.
- Proposed commit message: `research: locate call-view source registration premises`.
- Shared-record deltas left for primary/curator: record that static Value-name
  evidence does not require runtime execution, and that complete-view formation
  needs source registration/decoration before the separately open seed-discharge
  clause. Reference this note without promoting the conditional skeleton or
  closing the source-generation/production gate. No authority/index/task or
  question-board change is made here.
