# Explicit annotation-boundary sequences: conditional derivation

Date: 2026-10-05
Status: unreviewed conditional mathematical derivation; research checkpoint only
Baseline: `d90ba4425038cf86ff932ed42eb309931e143fd8`
Lease: this file only
Method: induction on a supplied finite source-derivation spine; no executable checker
Implementation authority: none

## Objective and governing scope

The committed user decision
[`source-annotation-boundaries/q1/d1`](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md)
selects binding annotations, parameter annotations and expression `as Type`.
Each boundary queries its current endpoint against its target, exports the
target and its local realization evidence, and preserves earlier evidence.
There is no intermediate concrete adaptation without a source boundary and
no inference of a direct first-to-last query from successful intermediate
concrete queries. The answer expressly does not select a syntax change making
`x as int as str` two expression boundaries.

This note derives the consequence for an already admitted source derivation
graph. It does not construct the missing raw-source annotation elaborator.
The governing sections are concrete-compatibility §1; typed-core §6's
interface/normalization, parameter-role and local-binding rules; charter
§§1–4; and the structural-tails design's `as Type` and “Type exit and
continuation” sections. The committed receipt identifies the approval and
states that source adequacy and production elaboration remain gated.

The existing obstruction note establishes the failure of replacing complete
concrete compatibility by a preorder. The old pure-source and recursive-group
results remain scoped to their genuine-preorder premise. No proof here
extends their unrestricted `Sub` rule to complete concrete compatibility.

## Explicit hypotheses

Write a source-derivation spine as `v0 --b1--> v1 ... --bn--> vn`, where
`n` is finite and the `bi` are distinct annotation occurrences. Nodes and
their supporting derivations may be shared in a finite graph; following this
spine does not unfold recursive source references. This is a proof graph,
not a proposed new source spelling or production data structure.

1. **Admitted source occurrences.** Every `bi` is one of the three selected
   forms and has an admitted target derivation. Its actual incoming source
   interface, role, typed path, profile, environment and scope are supplied.
   No omitted annotation form or bare `Sub` step is inserted. Distinct
   occurrences need not have distinct targets.
2. **Exact forwarding.** Let `ti` be the target of `bi`. The admitted
   form-specific annotation rule identifies a current query endpoint `ai`
   and a resulting interface `Ii`. The forwarding edge to the next boundary
   supplies exactly this exported target as its current endpoint, with the
   permitted lexical/typed-path transport. Thus `a1 = a0` and
   `a(i+1) = ti` on this spine. If a form's intervening consumer or binder
   changes what is queried, this equation is a premise to prove, not an
   endpoint equality to impose. Ordinary value targets can give
   `Ii = Value(ti)`; this note does not guess an analogous rule for all
   computation targets.
3. **Local query rule.** At occurrence `bi`, the one endpoint-dependent
   solver resolves precisely `ai <: ti` in that occurrence's retained
   context and returns local evidence `ri`. A source boundary judgment may
   use that result to export `Ii` and retain `ri`. This is the selected
   export rule instantiated at admitted descriptors; it is not a second
   compatibility relation. A label on a query identifies its source
   occurrence and context, rather than asserting that those alone determine
   all solver behavior.
4. **Joint admissibility.** All endpoints, contexts, targets and evidence
   inhabit one consistent assignment `nu` and well-formed source world `W`,
   including the existing symbolic `K,D` where applicable. Local successes
   under mutually incompatible assignments do not satisfy this premise.
5. **Base correspondence and retained evidence.** The supplied generator
   and source derivation for `v0` correspond exactly at `a0,I0` with evidence
   graph `R0`. Any base constraints are jointly satisfied in `nu,W`.
   The annotation extension retains `R0` and links each new evidence node to
   its predecessor derivation; a bare endpoint lookup after rebinding cannot
   erase the earlier annotated initializer.

These hypotheses separate selected semantics (which query, which export,
evidence preservation and no implicit adaptation) from candidate bridge
assumptions (admitted targets, form-specific role/path/profile mapping, joint
world construction, forwarding and base correspondence). In particular,
typed-core §6 explicitly leaves full annotation checking and admitted
conversion coherence open. A solved representation alone cannot select
`Value` versus `Computation`, insert an introduction, remove value-entry
execution, force a retained parameter or discard its original profile.

## Conditional boundary correspondence theorem

For any spine satisfying hypotheses 1–5, extend the supplied generator by
recording at `bi` exactly the labeled local obligation

```text
qi = (bi, ai <: ti, occurrence's supplied context)
output endpoint = ti
output interface = Ii
retained evidence graph Ri = Ri-1 plus node (bi, qi, ri)
```

The last line denotes a proof-level extension referencing the predecessor;
it prescribes no additional runtime carrier or attachment/provenance table.
After `n` extensions, the generated graph and source boundary derivation
have the same final interface and endpoint, the same ordered boundary spine,
and all original and local evidence nodes. Its new obligations are precisely
`q1,...,qn`, not `a0 <: tn`. Conversely, supplied admissible resolutions of
these exact obligations under `nu,W`, with the form-specific judgments of
hypotheses 1–3, reconstruct this source boundary derivation.

**Proof.** At `n=0`, hypothesis 5 supplies identical base endpoint, interface,
constraints and evidence. Suppose the assertion holds for `k`. Hypotheses
1–2 identify the next occurrence and its actual incoming endpoint: `a0`
when `k=0`, otherwise `tk`. Hypothesis 3 adds exactly the query
`a(k+1) <: t(k+1)` and its local evidence. The selected export clause makes
the new endpoint `t(k+1)` and the supplied admitted rule gives `I(k+1)`.
Hypotheses 4–5 allow this extension in the same world and preserve every
prior node. This proves the assertion for `k+1`. For the converse, perform
the same induction using the supplied local resolution at each occurrence
to apply its source boundary rule. No step obtains another query by
transitivity; no step needs `a0 <: t(k+1)`.

The quantification is over a **supplied finite admitted spine**. It is not
over every parsed term, every inferred assignment or arbitrary solver replay
paths. If the base has `p` obligations, the extension records `p+n`
obligations and `n` new evidence nodes with shared predecessor references.
This is a proof-graph count, not a bound on endpoint solving, descriptor
construction, runtime adaptation or parser costs. The theorem neither
requires nor proves uniqueness of local adapter choices or principality.

## Operational strengthening requires another exact premise

Typing/evidence retention does not prove executable adapter preservation.
For an operational claim, additionally require, at **each actual occurrence**:

> Its local realization rule takes the predecessor's designated incoming
> realization at the supplied role/path/profile and source context, produces
> a realization of the exported interface there, preserves the required
> source observations and joint constraints, and supplies the required
> initial-relatedness/future-use/resumption premises for the next consumer.

Given this premise and an operational base realization, induction also gives
a sequentially realized final interface: apply the local realization theorem
at `b1`, then at `b2`, and so on. This is composition of actual source
derivation steps at distinct boundaries, not evidence that a direct
`a0 <: tn` query succeeds. The premise must cover intermediate observations
and permitted context transport; matching endpoint names or independently
successful comparisons is insufficient. No such complete annotation-local
operational theorem is established by this note. This is the exact remaining
premise if operational source soundness is requested.

## Minimal approved concrete discriminator

Use the committed optional-record witness as **concrete endpoint notation**:

```text
A = {foo?: string}     B = {}     C = {foo?: int}
A <: B succeeds       B <: C succeeds       A <: C fails
```

Choose an admitted pure value base `Gamma(x)=Value(A)` and two distinct
binding-annotation occurrences in the proof graph:

```text
b1: annotated binding of y, target B, initializer Name(x)
    current A; query A <: B; export B; retain r1
b2: annotated binding of z, target C, initializer Name(y)
    current B; query B <: C; export C; retain r1 and r2
```

Binding annotations belong to the approved envelope, so these are two
authorized boundary **forms**. Instantiating the theorem additionally needs
admitted target derivations for `B,C`, the ordinary-value annotation rule
at each initializer, and a binding/lookup link that exports `Value(B)` into
`Gamma(y)` while retaining `b1`'s initializer evidence. Typed-core §6 gives
ordinary result binding into `Value(A_r)`; it does not derive that annotated
initializer rule. Under these exact premises, the two-step graph has local
obligations `{A <: B, B <: C}` and final endpoint `C`. It has no
`A <: C` obligation. This is a conditional proof-level instantiation, not an
assertion that the current compiler accepts the corresponding program.

There is existing parser fixture/source evidence for a typed binding form
`my x: T = value` (`binding_c8_reuses_full_current_pattern_surface_and_exact_equals_stop`).
It was inspected, not executed. It does not establish that the optional-record
notation above is a raw target spelling, that the two-binding program lowers,
or that HIR retains adapter evidence. No raw program using that notation is
claimed here. The prior source-coverage audit records that expression
`as Type` does not reach production query generation. No parser run or
production HIR acceptance result is provided by this note.

Two boundaries are the shortest sequence that exposes the rejected
compression: with one boundary the required query is already first-to-last.
Each adjacent comparison separately gives a successful one-boundary instance
when supplied its corresponding incoming endpoint; the two-boundary sequence
also exposes the failing first-to-last query `A <: C`. This is minimal in
boundary count for this particular discriminator, not a search over all
concrete endpoint domains. Returning the original `A` after `b1` instead would make
`b2` issue `A <: C` and fail; retaining only `r2` would violate the evidence
invariant even if the endpoint happened to be `C`.

The unconditional legacy `Sub` chain on plain `x` is unavailable under the
approved rule: the two successful comparisons must correspond to actual
source boundaries. The rejected claim about `x as int as str` supplies no
alternative instance.

## Evidence quality, failures and omitted scope

This is a symbolic derivation, not a transition checker or independent Oracle
experiment. Query successes in the witness come from the already recorded
concrete observation, shared with the obstruction note. The induction proves
the consequence of the supplied boundary rules; it does not independently
prove their source admission or runtime realization. There is no independent
oracle, enumeration, seed, input range or executed mutation. The three
symbolic failure mutations above attack compression, original-endpoint
retention and evidence deletion respectively; they are mathematical
discriminators, not test-run results.

The theorem fails to apply if a boundary is unadmitted, a target loses its
role/profile/path, forwarding does not supply the prior export, assignments
are inconsistent, evidence is dropped, or the base correspondence is absent.
A failing local query stops the derivation at that boundary; no final export
is derived. Parameter entry, computation-target annotations, Function/effect
conversion, callbacks, handler hygiene, recursive-group synthesis, scheme
instantiation/generalization, principality, source-wide adequacy and production
acceptance are unverified. The old recursive-group transitivity proof is not
repaired by this spine theorem: its body/export obligations still need an
explicit source correspondence rather than an arbitrary hidden adaptation.

Recommended next action: derive the ordinary-value binding-annotation
initializer/lookup rule with retained local realization, at the actual typed
path and source scope. That single missing form-specific bridge would turn
the two-binding conditional instance into a source derivation without
reopening the selected endpoint-export semantics.

## Frozen dependencies and checks

The following Git blob IDs pin direct semantic/proof dependencies at the
baseline (Git blob IDs, not claims of independently reviewed content):

| Path | Baseline blob |
| --- | --- |
| `questions/2026-10-05-source-annotation-boundaries/question.md` | `524c23ebb0b8cb008cf5e5d71ee8c3879431a782` |
| `questions/2026-10-05-source-annotation-boundaries/answer-draft.md` | `2adbf2dd6209bfa1debf915bd5d69cc61917a193` |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `1b87624d94d01aff386f31acb81cc40b2bb3b441` |
| `questions/2026-10-05-source-annotation-boundaries/receipt.md` | `54f566a38c5d1314b800824959e081ff663e2310` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-09-09-successor-expression-structural-tails-draft.md` | `c036c38a959656e12326046a8da57309379e8fa3` |
| `notes/progress/2026-10-05-source-adequacy-concrete-transitivity-obstruction.md` | `e82b4b24eb16440980d66ed95e89658f05d60a9c` |
| `notes/progress/2026-10-05-source-boundary-coverage-audit.md` | `1eece11aed7ed61fd547b10efdfa137e4b23bf14` |
| `notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md` | `45429aa04bf9be265c99b3d2f37ccdf176704633` |
| `notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md` | `73ff4ccccd3eeec7fd86407d317ccf05c876640c` |
| `crates/yu-syntax/src/tests/declaration/binding.rs` (fixture inspection only) | `aae68a8f9b141ceca2a562061acb0921df29192d` |
| `crates/yu-syntax/src/declaration/binding.rs` (source inspection only) | `165ad487cfebde8b40327a4144ac870782fc9acd` |

Checks run: bounded `rg`/`sed`/`cat` reads; `git rev-parse HEAD` (baseline
matched at inspection); `git ls-tree <baseline> -- <dependencies>`; scoped
`git diff <baseline> -- <semantic/proof dependencies>` (empty). Rules
`design-authority`, `research-lab`, `git-concurrency` and `question-board`
were also read. No builds, tests, checker processes, formatters, searches over
semantic inputs or Git mutations. One lightweight command process at a time;
CPU time and peak RSS were not measured. Wall time is not a theorem or
performance result. All writes are restricted to this note.

A final lightweight Python byte check recomputed Git blob identities for all
14 table entries: every current dependency matched its pinned baseline blob.
The note had no trailing whitespace, and HEAD still matched the baseline.
This checks snapshot integrity and text hygiene, not the mathematical theorem.

## Commit packet

- Exact leased paths: `notes/progress/2026-10-05-approved-annotation-boundary-sequence.md`.
- Baseline SHA: `d90ba4425038cf86ff932ed42eb309931e143fd8`.
- Changed dependency hashes: none observed in the scoped semantic/proof comparison;
  primary must revalidate dependency blobs before integration, including the
  fixture-only source inspection paths.
- Claim/review status: conditional derivation with an explicit local-realization
  gap; unreviewed research only; frozen when submitted, no independent review claimed.
- Checks already run: the narrow reads and baseline/dependency checks above;
  no compiler verification requested or run.
- Proposed message: `research: derive explicit annotation boundary sequence correspondence`.
- Shared-record deltas left to primary/curator: link this conditional sequence
  result from source-adequacy tracking; retain full annotation and recursive-group
  adequacy as open; identify the binding initializer/lookup realization rule as
  the next bridge. No edits to tasks, theory maps, design index or receipts.
