# Independent review: guarded regular structural solutions

Revision: r1. Date: 2026-10-26. Reviewer: `/root/call_entry_review`, independent
non-author of this construction and its repairs. Requested model/effort:
inherited; separately observed runtime model/effort metadata: unavailable.
No configured role is claimed as observed runtime execution. Producer-supplied
baseline: `0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`.

## Verdict and frozen scope

**CLEAN for the stated guarded structural graph/certificate model.** No
blocking, major, or minor defect found in this bounded review. The result
constructs the represented regular structural comparisons from executable
finite closure evidence. It does not prove that native inference produces
that evidence, nor that this relation supplies the frozen finite-Term
valuation or the original source judgment.

| Frozen input | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `tasks/agent-loop/inbox/20261026-inference-regular-solutions.md` | `c6153dc97f3bc0f1b4abc8e877c4c8148ec3f383c32670a89508f82502678c81` |
| Frozen direct dependency `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| Transitive dependency `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| Prior `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |

The two assigned hashes matched at intake and completion. The target, Syntax,
and Contracts in the isolated `inference-regular` project have the same hashes
as the inspected repository inputs. Prior Soundness retains the handoff's
frozen hash; it is contextual evidence, not a dependency newly certified here.
Line references below refer to `SimpleSubRegularSolutions.lean` unless a
different path is given.

## Independent semantics and proof meaning

At lines 215–225, `Layer` is defined from actual constructor expansion, `Approx`
recursively interprets finite structural unfolding depth, and `RegularSub`
requires every depth. None of these definitions mentions certificate
membership or checker success. The depth-zero case is deliberately trivial;
depth one already requires actual endpoint lookup and successful expansion.

`coinduction` at 233–241 proves by depth induction that any postfixed relation
is included in this interpretation. Its postfixedness premise is explicit,
and `Layer.mono` supplies exactly the induction step. `regular_unfold` at
243–259 proves the converse unfolding property. In the forward direction it
selects a child list at depth one and uses determinism of `expand` to identify
that same list at every other depth. It does not exchange unrelated witnesses
chosen independently at each depth. These results justify the greatest-fixed-
point description for this particular structural operator.

The finite checker at 273–285 examines actual expansion and membership of
every child in the same finite table. `checkPair_iff` and
`checkCertificate_iff` at 287–297 derive the postfixed relation required by
coinduction. Consequently `certificate_sound` at 299–304 does not take
`RegularSub`, a valuation, a local preservation law, or an unproved closure
proposition as an input disguised as a successful checker branch.

The central application has the actual type:

```lean
YulangClosure.SimpleSub.Regular.accepted_demands_sound :
  ∀ {graph certificate demands},
    accepts graph certificate demands = true →
    ∀ pair, pair ∈ demands → RegularSub graph pair
```

`accepted_all_depths` at 324–327 gives all depths for the same demanded pair.
`accepted_joint_relation` at 329–340 constructs the single relation
`fun pair => pair ∈ certificate`, proves it postfixed, and covers every demand
together. This is shared structural comparison evidence. The code and handoff
correctly avoid identifying it with the original joint source-scoped
Call/effect strategy.

## Validity, guards, and constructor coverage

The two kind-indexed finite tables at 34–53 cannot reinterpret an effect
identity as a value identity. All child edges come from Function, Record,
Tuple, or Variant constructors. There are no alias, variable, union, or
intersection nodes through which a comparison could recurse without crossing
a structural constructor. Whole record/alternative lists are finite; a cycle
can revisit a child node but cannot extend a cyclic row spine into an infinite
list of fields or alternatives.

The actual validator at 60–111 checks all graph nodes, all references at their
declared kind, and uniqueness of record labels and variant tags. This includes
children skipped by an immediate bottom/top comparison. `checkGraph_iff`
proves equivalence with `Graph.Valid`, and `accepted_graph_valid` derives it
from acceptance. In contrast, `certificate_sound` alone intentionally does
not assert whole-graph validity; acceptance includes the additional check.
The dangling example prevents that distinction from being lost.

Constructor expansion at 136–176 is concrete:

| Constructor | Inspected meaning |
| --- | --- |
| Function | Four separate ports, in order argument / argument effect / result effect / result. Child directions are `a' <: a`, `ae' <: ae`, `re <: re'`, `r <: r'`, at the correct kinds. `expand_function` states the exact list. |
| Record | Same whole ordered list shape, exact label and optional bit for each position, and covariant field children. No width/optional-admission completeness is asserted. |
| Tuple | Equal arity, ordered covariant children. |
| Variant | Same ordered tags and payload arities, with each payload compared in order. No complete native variant-admission theorem is asserted. |
| Atom / bottom / top | Atom identity equality, bottom-left and top-right leaves; both graph endpoints must still exist. |

These match the stated structural fragment and the Function variance of the
frozen Syntax relation at `SimpleSubConstraintSyntax.lean:101–104`. They do
not establish semantic equivalence to all of that finite relation: the latter
also has variables, union/intersection, reflexivity/transitivity constructors,
and a finite-Term valuation interface. No such equivalence is claimed.

The cyclic example at 365–389 is substantive: the two distinct Functions
return records; one field follows Tuple/Variant payloads back to the Function
roots and another recurs directly to the records. The six comparison pairs
close under expansion; the reversed argument and two effect obligations use
the required bottom-to-top direction. Kernel-reduced examples reject omission
of the effect pair, reversal of the comparison, optional-bit mismatch, and a
dangling reference even beneath a bottom comparison (391–417). Both effect
ports happen to demand the same effect pair in this example; the general
`expand_function` type independently retains and directs all four ports.

## Original source and actual native boundary

Read the pinned repository paper import
`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md:1–300`, including
the ordinary/unifying coalescing distinction, guarded recursive hypotheses,
and published proof-sketch limitations. Also inspected the original statement
and local valuation premise in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md:16–60,110–167`.
This review uses that pinned import; it does not claim a new full-paper PDF
retrieval or formalization of Fig. 10.

The missing finite-model premise is real:
`SimpleSubConstraintSoundness.lean:288–293` takes a finite `Valuation` and
`final.Satisfied` explicitly. `RegularSub` is not such a valuation. Handoff
lines 233–240 preserve the necessary interpretation/reflection bridge and
the original Call, effect, generalization, principal-coverage, and termination
obligations. `Contracts.lean:127–154` still requires original source judgments,
same-scoped evidence, native realization, and separate algorithmic termination.

Read the relevant actual native return/export code rather than treating an
`Ok` result as semantic success:

- `lib.rs:10667–10694` distinguishes execution completion and candidate
  finalization; unresolved active field-tail selection can still fail.
- `lib.rs:19769–19789,20119–20120,20180–20181` carries solver errors into the
  result and exposes them separately. A successful availability result does
  not establish their absence.
- `shadow_apply.rs:2029–2053` gates graph export on final absence of errors,
  exact root ownership, and the actual retained graph. It does not return this
  Lean certificate or prove its acceptance.
- `shadow_apply.rs:2013–2026,2055–2069` separately checks consumed evidence,
  final errors, and retained-use ownership. A locally drained edge is not a
  successful whole-inference receipt.
- `lib.rs:19601–19608,19655–19662` supplies empty/bottom effect ports in legacy
  Function finalization. It is not silently a faithful decoder of arbitrary
  four-port native Function evidence.

The first application bridge remains: decode the actual successful native
export and original demanded comparisons, preserving identities, kinds,
constructor data, and ports; extract finite closure evidence from its actual
successful constraint history; derive `accepts = true`; then relate this
regular interpretation to the required retained/source judgments. The new
theorem removes a supplied model premise only for its represented finite
graph/certificate input. It neither changes compiler acceptance nor mandates
a new production validator.

## Complete retained audit evidence

Read the complete 1,439-line `audit-05.log`, including all printed theorem
types and axiom results. Display-only namespace abbreviation was used for
readability; a separately fetched middle window covered output truncation.
Programmatic inventory checks confirmed 134 distinct begin/end names in the
same order, 134 matching axiom results, and all 33 authored theorem names
present. The other 101 constants are generated helpers, including private
match equations. Observed totals:

| Axiom set | Theorem constants |
| --- | ---: |
| None | 45 |
| `propext` | 64 |
| `propext`, `Quot.sound` | 25 |

No `Classical.choice`, `sorryAx`, project axiom, error, or warning appears in
the completed audit. The isolated audit source enumerates by actual originating
module index, rejects project axioms, verifies nine required roots, checks
every theorem type, and enforces the standard axiom whitelist. The target and
direct/transitive project sources contain no proof holes or checker bypass.

| Retained evidence | Verified SHA-256 |
| --- | --- |
| `inference-regular/RegularAudit.lean` | `e1ed9c45cc93ea0e772db46903a8d1ff5244c1cc6ffa1c999f5f2e97fdca0474` |
| `inference-regular/audit-05.log` | `6846c750c69cea3dbbf7ab69cc0ddbb0107d8131f8c9b357844fcdfc278e62bb` |
| `inference-regular/check-04.log` | `68b5b94505d9b84d121690da56819bb02cda275be5f9e11bb233b7900626583c` |

The build log records successful completion of four jobs. The handoff reports
exit 0 for that build and the audit, using the pinned Lean 4.35.0 distribution
with `-j1 -M1024`; failed earlier logs retain the dependent-pattern and endpoint
witness elaboration repairs. The final source contains the explicit
kind-indexed expansion and corrected witnesses. Project toolchain/manifest
contents were read. No reviewer checker process or version command was run;
retained logs are the execution evidence, not a claimed independent rerun.

## Severity-tagged findings and remaining boundaries

| Severity | Exact location | Finding / recommended action |
| --- | --- | --- |
| INFO | Source 34–41,136–171; handoff 57–63,233–240 | The accepted fragment excludes aliases, variables, union/intersection, arbitrary row-bound cycles, width/optional admission, and complete contextual effects. Keep these exclusions explicit when describing progress; they do not restrict the original source theorem. |
| INFO | Source 301–304 versus 312–340 | Certificate closure alone proves the independent comparison relation; whole-graph validity comes from `accepts`. Applications requiring a valid regular graph should retain the acceptance premise or separately establish validity. No repair is required for the current theorem types. |
| INFO | Source 16–19; handoff 222–240; native locations above | No native decoder/certificate-production or regular-to-source reflection theorem is supplied. Preserve these as open bridges and do not advertise model checking as full inference soundness. |

## Scope and cessation

Inspected the entire target and handoff, actual Syntax definitions, relevant
Soundness/Contracts and source-authority sections, native completion/export
seams, isolated source hashes, full audit and audit program, successful build
log, and material earlier failure logs. This is not a new review of all
Syntax/Soundness theorems, the full native generalizer, runtime behavior,
production integration, or the whole original paper.

Followed repository instructions and the proof skill. Only this exact leased
review receipt was written. No source, cache, Git, scheduling record, other
receipt, or semantics was changed. No children or checker/test processes were
launched. **Receipt frozen; writes STOPPED.**
