# Qualifying parent/copy equality: a native preservation slice and the first missing bridge

Date: 2026-10-12
Status: frozen unreviewed research; bounded constructive derivation and source obstruction
Original qualifying-equality, soundness and required-principality gate: OPEN
Baseline: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file; proof leaf, no delegation, implementation or Git mutation

## Frozen parent claim

For every supported resolved Yulang source `s`, original environment `Gamma`,
lexical/type/event scopes and binders, required typing `Gamma |- s : tau`, and
lawful native inference/use history, consider the graph at an intrusion cut
**before** the equality under examination. Its vertices are actual Value rows;
its edges are the approved source-owned resolved Name incidences, transported
through actual extrusion and fresh uses. For every actual retained extrusion
pair `(copy,parent,polarity,target)` whose distinct endpoints are in one SCC,
the selected operation equates them in solving and later use.

The required conclusion preserves one joint witness for the original required
typing, all complete interfaces and their dependencies, and the required
principality relation to `tau`; every successful published result remains
sound. Equalities selected together must preserve those witnesses jointly.
Original recursive sharing, level/generalization boundaries, independent lawful
uses, complete Call, annotation authority, attachment/provider/witness identity
and separate residual lineage remain in scope. Native generation, accumulation,
opposite-bound propagation and polarity-specific extrusion remain the algorithm.

Hypotheses supplied by the packet are the original native operations and
retention of actual parents, the approved source-owner clauses, and the selected
SCC/equality operation. **Their actual source/consumer correspondence and
qualified witness preservation are obligations, not assumed facts.** No
precondition that a desired example qualifies, that a reference entails a
subtyping inequality, or that equality preserves a witness is introduced.
An absence of current HIR admission does not shrink the supported-source
quantifier. Excluded from conclusions established here, rather than from that
domain: all-source typing adequacy, let principality, complete Call realization,
hygiene, termination, abnormal publication and F5 cutover.

Method: consume the existing finite native odd/even derivation, directly
eliminate its actual polar-copy parents and use variables by native inequalities
and Function variance, then inspect the owning source/copy/SCC constructors.
Falsifier: a supported-source trace containing an actual qualified pair whose
required joint interface has no preserving equal witness. Stop at that trace,
a complete proof, or the first unavailable source premise. No executable model
is used as a substitute.

## Authority and prior evidence

Governing sources under `notes/design/`:

- `2026-10-11-yulang-inference-top-level-principles.md`, §§1–5, Evaluation and
  Authority and integration;
- `2026-10-10-parent-copy-scc-intrusion.md`, Selected operation, Value-reference
  SCC clarification, Apply-result source-fragment ownership, Nested Apply
  membership and Definition-root Value ownership;
- `2026-10-10-local-self-recursive-binding.md`, Selected source behavior and
  Proposed source-to-solver seam;
- `2026-10-10-annotation-effect-hygiene-integration.md`, §§1–4;
- `2026-10-07-complete-call-contribution-definition.md`, complete Call case and
  retention contract, together with `2026-10-07-original-call-formation-definition.md`,
  §§2–6;
- `2026-10-10-contextual-residual-lineage-selection.md`, Selected policy.

The packet's `2026-10-10-local-recursive-self-initialization.md` locator does
not name the governing file in this checkout; the actual selected source is
the local-self-recursive-binding document above. No alternative policy is adopted.
The proof skill, orchestration/model-routing/proof-delegation rules, research-lab,
design-authority, compiler-engineering, Git-concurrency and orchestration-budget
were read. The primary owns review, adjudication and shared records.

Consumed dependencies, without rerunning their investigations:

1. `2026-10-11-inference-rebuild-native-spec-proof.md`: pure equality-quotient
   algebra, the non-qualified continuation falsifier, and the original joint
   witness/generalization obligation. Its falsifier is not an SCC refutation.
2. `2026-10-12-odd-even-cross-level-typing-proof.md`: exact source admission
   obstruction and conditional level prefix.
3. `2026-10-12-odd-even-parent-copy-scc-derivation.md`: complete finite original
   Simple-sub store for the Call skeleton and actual candidate polar port
   constructors. Its finite derivation has scoped independent review; it is
   not a source-qualified intrusion theorem.
4. `2026-10-12-odd-even-native-extrusion-audit.md`: actual candidate parent roles,
   replay prefix and distinction between extrusion and local-use freshening.

The reference is `simple-sub-reference` at
`9bae772624c23b52a93c1b226157e16898b4d9db`. Its actual
`shared/src/main/scala/simplesub/Typer.scala:48–83,88–159,166–207` owns the
generation, propagation, extrusion and freshening used below. This reference
has no Yulang Value-incidence graph, retained-parent intrusion, or complete Call.

## A direct preservation derivation for the native Call skeleton

This subsection's claim class is **bounded constructive constraint/use
preservation**, pending independent review. It proves a concrete preservation
fact on a native-generated store; it does not assume or conclude SCC eligibility.

Use the previously derived original grammar term, with its binders unchanged:

```text
let rec odd = lambda n_outer.
  let even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

This is the original Simple-sub term, not a translation or admission proof for
the user's conditional/arithmetic Yulang source. `O` is the level-1 open
recursive expectation, `A` the level-1 outer formal, `B` the level-2 inner
formal, `R` the level-2 inner App result. Negative extrusion of the demand
`O <: Function(B,R)` creates `C` at level 1 positively from B and `D` at
level 1 negatively from R. Thus the authentic pairs are `(C,B,+,1)` and
`(D,R,-,1)`. Published `even` has boundary 1 and body `Function(B,R)`;
its one outer use freshens B/R to B'/R' at level 1, retaining C/D. The outer
App result is S at level 1. B'/R' are use images, not extrusion children.

The existing native-rule derivation yields exactly these comparison meanings
at recursive initializer completion, allowing redundant replay obligations:

```text
B <: C                    D <: R
O <: Function(C,D)        Function(A,S) <: O
B' <: C                  D <: R'
A <: B'                  R' <: S
C <: A                   S <: D
D <: S                   [already implied by D <: R' <: S]
```

They follow from the actual generator, wrong-level negative Function
extrusion, ordinary opposite-bound replay and recursive initializer completion.
They are not invented starting constraints. The original reference stores
some comparisons at only one endpoint; the displayed constraints express
their meanings, not an invented bidirectional bound layout.

Let a single valuation `mu` satisfy this whole finite store in the original
subtyping preorder, with Function contravariant in its input and covariant in
its result. Leave O/A/C/D/S unchanged. Jointly set

```text
mu*(B) = mu(C)       mu*(R) = mu(D)
mu*(B') = mu(C)      mu*(R') = mu(D).
```

Verification is direct. B <: C and D <: R become reflexive. A <: B' <: C
becomes A <: C, which holds by transitivity in the old store. D <: R' <: S
becomes D <: S, also an old consequence. Every other comparison uses only
unchanged variables and retains its old truth value. Both actual parents are
equal to their actual copies in **one** replacement valuation. O, A, S and
all common capture coordinates retain their interpretations. No independent
marginal witness is selected for either pair or either Function port.

This also handles the local generalization boundary in this particular store.
After equality with minimum level, B/R become the level-1 anchors C/D and are
no longer freshened at boundary 1. The local body's normalized Function is
`Function(C,D)`. An ordinary direct App demand `Function(A,S)` then produces
precisely A <: C and D <: S. Its old fresh use produced the four comparisons
A <: B', B' <: C, D <: R', R' <: S. Restriction of any joint old witness
satisfies the new two comparisons; extending a new witness by B'=C and R'=D
satisfies all four old comparisons. The same fixed C/D are used in both
directions. Thus losing these two local generic images loses no witness for
this actual direct App demand.

At the local Function observation itself, B <: C and D <: R imply

```text
Function(C,D) <: Function(B,R).
```

The normalized Function can therefore meet every supertype observation of
the old Function at this fixed joint valuation by transitivity. This is the
precise variance reason why this slice does not need to freshen a nongeneric
anchor merely to recover the two eliminated generics. It is not a theorem
about arbitrary required complete Call observations or arbitrary continuations.

The native bound replay is similarly small here. Merging B/C combines empty
lowers with uppers C and A, so creates no nontrivial lower/upper pair. Merging
R/D combines the lower D with upper S; its nontrivial cross obligation is
D <: S, already generated by replay at the outer App. Canonical self bounds
are reflexive. This is the replay calculation the selected equality would
require on this pure store; the original reference implements no merge operation.
It is finite native comparison reasoning, not evidence that
the Rust contextual consumer completely discharges all transported obligations.

Consequently, projected finite-store witnesses on O/A/C/D/S are preserved,
and the actual one-use local Call constraint relation is preserved. The final
outer boundary remains 0, so C/D remain above it; this derivation introduces
no loss of their outer generalization eligibility. It proves neither a
general let-principality theorem nor that all required source typing witnesses
are represented by this store. Those source-adequacy premises remain independent.

The older continuation falsifier adds a conflicting parent upper/copy lower.
Those bounds are absent in this native skeleton. This proof therefore does
not apply to that trace, and that trace does not invalidate this finite proof.
Adding such bounds in an actual source history would require a new direct
analysis; one cannot reuse this replacement map without inspecting them.

## The exact example and source qualification

The original source remains exactly:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

O/E denote its original definition roots; its two n binders remain distinct.
These role letters do not identify a candidate definition row with the
reference term's recursive expectation without a source correspondence.
By the approved definition-root law, O owns the final resolved even reference
and E owns the inner resolved odd reference, giving O → E and E → O across
levels. No level ordering filters these edges. Apply result rows separately
own the resolved Names in their own approved callee/argument fragments.
For the Call skeleton's inner Apply that means incidences to O and B; its
outer Apply has incidences to E and A. These are approved incidences conditional
on those source resolutions, not observed solver edges.

The exact source's ordinary admission is still missing at the responsible
constructors: `yu-hir/src/module.rs:1596–1611` reports an indented body as
UnsupportedExpression; `module/local_source.rs:223–255` requires an OperatorChain
body; its complete `LocalSourceForm:107–137` has no conditional form. The
cross-level typing dependency additionally identifies the intrinsic infix
formation gap. This attempt does not replace arithmetic, the conditional,
primitive meanings, or either original Call with the skeleton to declare
the exact statement proved.

Even for the carrier-shaped skeleton, the genuine native pairs name B/R,
not O/E. The source root SCC does not establish B ↔ C or R ↔ D. Source
incidence has no general implication X <: Y, so two source paths cannot
be composed as a subtyping proof of equality. Parent creation supplies only
the polarity-specific comparison and actual provenance, not a return reference.

## Actual owner/consumer seam and first missing premise

| Responsibility | Actual owner on the pinned baseline | Evidence and remaining obligation |
| --- | --- | --- |
| Resolved source coordinates and levels | `candidate_source.rs:209–216,254–307,369–411` | Parameter Names select their actual formal endpoint; module/local Names and Apply retain operands/results. No per-fragment resolved Name incidence is emitted as an SCC input. |
| Actual copy creation | `candidate_extrusion.rs:90–163,224–249` | Allocate at target level, retain parent before copied bounds, reverse Function argument polarity, preserve result polarity. No source-owned incidence/target transport is defined here. |
| Actual parent record | `candidate_intrusion.rs:171–220` | Copy/parent/kind/polarity/target retained; provenance is explicitly excluded from graph adjacency. |
| Fresh use and original boundary | `candidate_scheme.rs:567–574,1009–1016,1221–1266,1316–1334` | Old anchors shared, above-boundary local rows coherently freshened, bounds restored, live root installed. This is not resolved Name-target transport. |
| Qualifying SCC consumer | `candidate_intrusion.rs:375–486` | Scans bound sides, Function ports, Effect rows/views, then compares component IDs for actual pairs. It does not read the approved Apply/definition source-incidence relation. |
| Equality and activation | `candidate_intrusion.rs:513–605`; `candidate_extrusion.rs:763–838` | Transfer both bound sides/origins, canonicalize, minimum level and nongeneric union, then invoke opposite replay. Calling replay does not prove complete contextual discharge or original witness preservation. |
| Complete Call | `candidate_call.rs:81–130` | Explicitly pending whole registration, formal/exposure, Gen-Call, argument carrier, receiver and complete result/future suppliers. Four-port demand does not fill them. |

The **first missing premise for applying this attempt to an actual qualified
pair** is the construction/transport law at this source-to-copy seam:

> The approved resolved Name incidence of each actual Apply/definition owner
> is assigned to its actual Value row; extrusion and each coherent fresh use
> retain its original owner/binding targets with the intended image/shared
> target identities; the pre-equality SCC consumer reads precisely that
> transported relation on the actual retained parent/copy endpoints.

Its original sources know the Name, owner and resolution; its copy/use
constructors know the polarity memo, image and shared captures. Current
records do not supply their join to the SCC consumer. The approved clauses
do not establish how copied descriptions own/target those incidences. This
is missing evidence at named owners, not a hypothesis added to make the
parent theorem conditional, a proof that qualification is impossible, or a
request for another ordinary-bound graph reconstruction.

Until that seam is supplied, neither the exact source nor the bounded analogue
supplies an actual source-qualified pair. The bounded replacement derivation
therefore discharges only the finite native-store/direct-use preservation
slice above. **No original all-source preservation/principality clause is
discharged, and no source-qualified counterexample is constructed.** After
qualification is grounded, the remaining semantic question is whether every
required original joint interface at that actual pair admits preserving equality,
including all later constraints and the original quantifiers. That conclusion
is still unproved; this note does not assume it.

Complete Call must retain one correlated actual provider, whole argument,
entry, result/future interface and evidence. Row equality does not identify
provider, attachment, receipt or witness identities. Hygiene retains composed
polarity, original annotation boundary authority and independently surviving
contributions. Every separately constructed residual recipe retains its
lineage and current/future fan-out. The finite two-port proof has no premises
that would establish those richer properties.

## Economy audit and stop

Prior native-level and operation/reference approaches, followed by the forced
port derivation, left actual incidence transport/qualification untouched.
The new finite elimination argument establishes a specific native preservation
slice but does not repair that premise. Apply the existing economy audit
before any further equivalent parent proof:

- Correct source/consumer qualification and equality safety remain A; required
  ordinary recursive inference/generalization remains B. No parent gate is
  reclassified, weakened or promoted.
- Reconstructing resolved owners/targets from later bounds is D: construction
  already knows them. Retaining those original incidences and coherent
  copy/use maps can remove that recovery debt without changing ordinary typing.
- Retention alone cannot prove equal witnesses or select an unapproved
  target-transport meaning. The genuine A/B preservation question remains
  after its operational premises are grounded.

Stop at this source seam, rather than attempt another conditional graph model.
One next action: the primary assigns its source/Value transport owner the
actual incidence map for `(C,B,+,1)` and `(D,R,-,1)` through publication and
fresh use, with pre-equality SCC-consumer correspondence; resume this parent
proof on the resulting source-qualified trace. Frozen output awaits a fresh
primary-assigned compiler_referee; the producer cannot certify it.

## Checks, resources and dependency snapshot

Static commands only: `cat`, bounded `sed`/`rg`, reference locators,
`git rev-parse HEAD`, `git branch --show-current`, dependency-scoped
`git diff --name-only <baseline> -- <inputs>` and SHA-256 capture. The named
repository dependency diff was empty. Reference Typer's hash matches the
consumed native derivation. No compiler/tests/expectations/shared records were
edited. No tests, builds, probes, Oracle calls, measurements, Git mutations or
child jobs ran. Shell file inspection/hash commands are not compute experiments.
`git diff --no-index --check /dev/null <lease>` emitted no whitespace diagnostics
(exit 1 records the new-file difference); final HEAD still matched the baseline.
At most five static reads were batched; zero lightweight/heavy experiment
processes and zero samples. CPU/RSS and exact reasoning wall time were not
instrumented; this was one bounded attempt within the 45-minute packet.

Requested runtime: normal proof leaf, `gpt-6.1-sol/high`. `.codex/config.toml`
registers prover and its Sol/high defaults; `agents/prover.toml` omits model
and effort pins. Effective runtime role/model/effort metadata is unavailable
to this leaf and is reported **unknown**. No Astra, override effectiveness
or hot reload is claimed. No independent review has run on this artifact.

Direct dependency content SHA-256:

```text
fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
ea09a810be20984ca6c2711c4372e77cc7c360b2b208946465fcf6dad5bd4b33  notes/theory/2026-10-11-inference-rebuild-native-spec-proof.md
6dba2dee2ad24674e67d6cc91cb65373255da7d568ebcebc14c6eecf13dc366d  notes/theory/2026-10-12-odd-even-cross-level-typing-proof.md
9c44f9220a43631b7bb7e6723b5f777c3f467242e68ff2dcbb19df73e846cec0  notes/progress/2026-10-12-odd-even-native-extrusion-audit.md
238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830  notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference shared/src/main/scala/simplesub/Typer.scala
```

## Commit packet

Exact leased/changed path:
`notes/theory/2026-10-12-qualifying-parent-copy-preservation-proof.md`.
Baseline SHA: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`.
Changed dependency hashes: none against the named baseline at inspection;
the dependency snapshot above includes the newer approved owner clauses and
review repairs, rather than the older hashes quoted in historical artifacts.
Claim/review status: unreviewed bounded native constraint/use preservation and
precise source obstruction; original parent gate OPEN. Checks already run:
static owner/consumer reads, baseline/dependency comparison, dependency hashes
and the new-file whitespace check;
no executable semantic checks. Producer writes stop at handoff.
Proposed checkpoint message:
`research: derive native polar-copy preservation slice and isolate qualification bridge`.
Shared-record deltas left for primary/curator: link the new joint B/C and R/D
finite elimination result; preserve all-source equality/principality OPEN;
assign actual incidence copy/use transport and SCC consumption to its source
owner. No task/index/theory-status/design/question-board record was edited.
