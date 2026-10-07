# Exact recursive singleton: executable-source boundary

Date: 2026-10-07
Status: Authoritative only for the already approved exact q1 executable-source boundary
Scope: only the resolved singleton declaration `my f = f` in question q1
Approved-by: user, through the unchanged q1/d1 handoff linked below
Approved-at: 2026-10-07
Drafted-by: primary (Astra), rule extraction from that handoff
Reviewed-by: independent compiler-referee and spec-auditor; both PASS, primary accepted
Supersedes: the unresolved executable-source disposition of this exact case;
no F4 inference rule or other initializer rule
Implementation: production routing/cutover not authorized by this record

## 1. Governing decision and exact recognition

The integrated [approved answer](../../questions/2026-10-07-recursive-self-initialization/approved-answer.md)
q1/d1 selects deterministic rejection **before initialization execution or
the right-hand-side self-read**, preserves the existing F4 `Never` inference
result, and specifies no diagnostic wording or compiler phase placement.
Its [receipt](../../questions/2026-10-07-recursive-self-initialization/receipt.md)
records integration at `a814bc76aa107f2ffb7aae9cb2e2887c5b078792`.
This document states that decision as a source judgment. It selects no new
runtime behavior, general recursive initialization policy, or representation.

Let `Self_q1(S,b,n)` be a *source-shape* judgment with all of these premises:

1. `S` is the exact single-declaration source case of q1, displayed as
   `my f = f`, with its original declaration binder `b` and RHS occurrence `n`.
2. The declaration has one simple binder, no parameters and no annotation;
   its entire RHS is the direct Name occurrence `n`.
3. Original lexical resolution maps `n` to `b`. The recursive component of
   this case is the singleton containing `b`.

These premises retain original source identity; they are not an endpoint
type equality test. In particular, this rule does not recognize arbitrary
`Never` expressions, aliases to another member, multi-member cycles, a
lambda body containing a self-use, parenthesized/annotated variants, local
recursive groups, or declarations merely having the same spelling. Those
forms require their own source judgments. Renaming bookkeeping identifiers
in a proof transports `b,n` and resolution together; it does not enlarge the
source envelope specified here.

## 2. Source rule and phase separation

Use disjoint outcome constructors `Permit_exec(t)` and
`Reject_exec(SelfInitNoValue,b,n)`. The reason tag is mathematical notation
for the approved reason, not a prescribed public diagnostic or API enum.

The complete rule head for this case is:

```text
Self_q1(S,b,n)
---------------------------------------------------  EXEC-SELF-Q1
ExecBoundary(S) = Reject_exec(SelfInitNoValue,b,n)
```

`ExecBoundary` is the semantic decision to accept the definition as an
execution target. On this case the equation is exclusive: it admits no
`Permit_exec` conclusion. No runtime store, provider value, allocation label,
membership judgment, solved type, or successful comparison is a premise.
The boundary must dominate the start of initialization and its RHS read.
This states a phase ordering, without choosing a compiler pipeline stage.

Type inference is a separate judgment. If `Infer4(S) = I`, retain that same
`I` when recording the boundary result:

```text
Self_q1(S,b,n)     Infer4(S) = I
---------------------------------------------------  ANALYZE-SELF-Q1
Analysis(S) = (I, Reject_exec(SelfInitNoValue,b,n)).
```

`Analysis` here pairs two semantic results, rather than declaring a new
compiler API or an eager inference execution schedule. The rule neither
fails inference because execution is excluded nor permits execution because
inference succeeded. It does not turn inferred `Never` into an execution
permission test for any other source.

## 3. Envelope inversion and non-execution

Define `Executable(S)` to mean that the execution-acceptance boundary has a
`Permit_exec` witness. This is the supported executable envelope, distinct
from the F4 inference-input envelope.

**Theorem SELF-ENVELOPE.** `Self_q1(S,b,n)` implies `not Executable(S)`.

**Proof.** EXEC-SELF-Q1 gives the unique rejecting boundary outcome. An
`Executable(S)` witness would give a permitting outcome at that same
boundary. Disjointness and exclusivity contradict this witness. No property
of the RHS's possible runtime interpretation is needed. QED.

The approved phase rule requires a `Permit_exec` witness before starting
initialization. Consequently:

**Theorem SELF-NOSTART.** No execution admitted through this boundary for
the q1 case has an initialization-start event, a RHS self-read, a provider
publication, or a resumed initializer transition for that declaration.

**Proof.** If an admitted trace has a first initialization-start event, its
boundary must have produced `Permit_exec`, contradicting SELF-ENVELOPE.
The RHS read and subsequent initialization transitions require that start,
so none occurs. The empty execution trace accompanying a boundary rejection
is not a divergent initializer or a runtime uninitialized-read error. QED.

The ordering premise is precisely the approved pre-execution rejection
requirement, not a claim that the current production compiler already
enforces it. An implementation that first performs the lookup and then
reports this reason violates the rule even when its final message matches.

## 4. Inference preservation

The [Authoritative F4 design](2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md)
§§1, 5–8 specifies the unseeded resolved-Name cycle. In the exact singleton,
the internal use produces `root_b <: value_n` and the body produces
`value_n <: root_b`. There is no Integer lower seed. Positive expansion
therefore encounters only these variables and their recursive occurrence;
F4's elimination of positive-only uninformative variables and bottom
simplification produces `ClosedPositiveValue::Bottom`, displayed as `Never`.
The effect facts remain the ordinary empty-effect facts of that Name.

**Theorem SELF-INFER.** Within F4's admitted inference scope, adding
EXEC-SELF-Q1 leaves the inference derivation and its `Never` root result
unchanged.

**Proof.** EXEC-SELF-Q1 has a different judgment head and introduces no F4
constraint, bound, inference failure, or scheme rewrite. The original
derivation is still a derivation of `Infer4(S)`. ANALYZE-SELF-Q1 copies that
same inference result. In particular, no error-to-bottom injection or
filter on generalization is involved. QED.

[Result synthesis §4](2026-10-02-source-result-synthesis-choice.md) also
continues to give `Synth(name f)=Gamma(f)` and
`Result(Value(R_f))=Comp(empty,R_f)`. These interface judgments do not
execute the Name or furnish a runtime provider. The earlier
[conditional first-publication argument](../progress/2026-10-09-rec-init-boundary-attack.md)
is no longer needed to choose a disposition for q1: its inclusion premise
is now false. Its conditional theorem remains valid for its stated
hypotheses and selects no rule for other initializers.

## 5. Source adequacy and production implication

Use a disjoint sum of accepted-source observations and boundary rejections
when discussing the *whole input-processing* correspondence:

```text
SourceOutcome(S) = Reject_exec(reason,b,n)
                | Accepted(source observation at original xi/world).
```

This notation keeps rejection outside the ordinary Return/Request/latent
observation relation. It does not insert a new runtime event into `Rel_C`.

**Theorem SELF-ADEQUACY.** The q1 contribution to this correspondence is
exactly its approved pre-execution rejection. It generates no successful
execution obligation, initial provider-existence obligation, or dynamic
`DescMem` proof obligation for its RHS. The existing inference result is
preserved independently.

**Proof.** EXEC-SELF-Q1 supplies the source outcome and SELF-NOSTART removes
every accepted execution case. SELF-INFER gives the unchanged inference
component. Both directions of the scoped correspondence compare the same
`Reject_exec(SelfInitNoValue,b,n)` and the empty initialization trace. There
is no witness conversion or fixed-point selection. QED.

For an implementation of this case, the sufficient and necessary observable
requirements within the approved scope are:

- recognize the original q1 shape and lexical self-reference correctly;
- retain the already authorized F4 inference result;
- reject at execution acceptance before initialization or RHS read begins;
- preserve that source ownership for the rejection reason.

These are concrete production-conformance obligations, not evidence that
the current compiler meets them. Public diagnostic wording, stage placement,
whole-pipeline implementation, broader source coverage and the successor
cutover remain outside this record. A default-off structural shadow may
carry the exact shape and pending boundary evidence under its existing user
authorization; an unresolved or non-q1 shape is never silently permitted.

## 6. Scope and retirement

Close only the exact q1 subcase of `REC_INIT`, including its boundary
inversion, inference preservation, pre-execution rejection and source
adequacy disposition. The aggregate `REC_INIT` remains open for other
initializers. This is an existing approved decision applied to its source
rule, not a new request for user choice.

Retire these exact old obligations for q1: deciding whether it executes,
choosing the first unavailable-self-read behavior, constructing a provider
for that execution, and proving runtime progress of that RHS. Do not retire
`REC_DESC`, `MEMBER_DISCHARGE`, or `GENERALIZE`: they concern actual admitted
providers and retain their independent obligations.

The next initializer clause is stated separately in the associated
[proof/attack record](../progress/2026-10-07-self-init-and-conformance-round3.md).

## 7. Independent review and authority application

The independent `round3_compiler_referee` and `round3_spec_auditor` reviewed
the frozen rule and its proof/attack record against the unchanged q1/d1
approved bundle and governing F4/source clauses. Both returned PASS without
findings. The primary accepted both conclusions after both reviews completed.
The reviewed rule snapshot has SHA-256
`e38bba12e827c1604665c47ef155b63ffa973f0a3927bf85561f8bd88fc655ed`;
the changes after that snapshot are this review record and status metadata.

Authority comes from the existing approved answer, not from the reviewers or
this status field. The reviews confirm that §§1–6 extract only that decision.
The [round-3 integration record](../progress/2026-10-07-successor-round3-review.md)
records the bundle checks, exact CLOSED subcase and remaining implementation
obligations. No current production execution path is certified or switched.
