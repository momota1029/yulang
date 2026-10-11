# Value-reference transport: native map derivation and a missing incoming path

Date: 2026-10-12
Status: unreviewed research derivation and conditional graph characterization; parent gates OPEN
Baseline: `874d43756cc44ce1787b4ca30a7595eeff1bc121`, `research/simple-sub-intrusion`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output: this file; leaf only; no further delegation

## Frozen statement and authority

The original parent obligation quantifies over every supported source program,
every lawful finite inference/use history at its original lexical, type and
event scopes, and every actual retained distinct Value extrusion pair `(c,p)`.
Before the equality being justified, qualification is

```text
Q_H(c,p) := Parent_H(c,p,polarity,target_level)
           and p ->* c and c ->* p in the actual Value-reference graph G_H.
```

The required conclusion is preservation of joint source typing, complete Call
meaning, effect hygiene, attachment/provider/witness/residual lineage, and
required principality, with actual constructor-to-consumer correspondence.
The pair's polarity and target level are retained creation provenance; they
are neither edges nor a level filter on qualification. This packet leaves
that universal obligation unchanged.

The local question is whether the approved original-owner incidences and native
Simple-sub operations determine the transport needed to establish `Q_H`.
Its conclusion must be a derivation of that law or its precise missing
premise. The three examples below are discriminators, not a restriction of the
original source domain. Distinct shadowing binders remain distinct; fresh-use
copies remain distinct from extrusion copies and original resolved binders.

Governing sections of
[`parent-copy SCC intrusion`](../design/2026-10-10-parent-copy-scc-intrusion.md):
**Selected operation and compiler responsibility** (lines 26–36),
**Value-reference SCC clarification** (38–54), **Apply-result source-fragment
ownership** (56–72), **Nested Apply membership** (74–89), and
**Definition-root Value ownership** (91–121). The last three clauses explicitly
leave copy/use transport and pair qualification unestablished.
The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and **Evaluation** require native inference and its actual proof bridge.
The accepted root edges for the user's nested odd/even example are `O→E` and
`E→O`, across inference levels. They are not the Call port pairs.

Method: direct hand derivation from reference `Typer.scala`, static inspection
of current Rust constructors/consumers, then a finite graph calculation with
each transport assumption stated. No reconstruction axiom such as `Fam_delta`
or `EmittedGenCall0`, graph checker, test, build, Oracle or execution is used.

## A compact relation that exposes the missing data

Let an incidence be `(v, sigma, beta, b)`, where `v` is its actual Value owner,
`sigma` is a resolved Name occurrence, `beta` is its original scoped binder,
and `b` is that binder's actual Value row. Keep the occurrence and binder even
when several incidences project to the same adjacency `v→b`. They provide
correlation, not new semantics. `G_H` is this adjacency projection.

For one copy/use event `kappa`, the unknown transport relation is

```text
T_kappa(v, v_new, sigma, beta, b, b_new).
```

It specifies the incidence owned by `v_new` and its target `b_new`, while
retaining which original occurrence and binder produced it. The native
event separately supplies a partial type-row map and its exact copy domain.
Freshening supplies an unsigned map `mu_kappa(b)`. Extrusion supplies a polar
map `m_kappa(b,s)`, `s∈{+,-}`, not generally an unsigned map.
An absent map entry is not permission to allocate another row.

Two candidate completions, where their target maps exist, are:

```text
Anchored: T(..., b, b).
Mapped:   T(..., b, mu_kappa(b)) if b is in this event's copy domain;
          T(..., b, b) otherwise.
```

A third proposal closes the event's copy domain over referenced targets and
then applies the mapped rule. This changes the domain rule, and can require
additional Value rows and type-bound transport. It cannot be described as
ordinary native freshening on its original domain.

These equations are proposals for copied owners, not alternative definitions
of an original Apply's resolved target. Both preserve the already approved
original incidences. Neither is adopted here. In particular, a polar `m` does
not supply the `mu` in the second equation without a further rule.

## Identity first: what native inference actually determines

For original `let id = lambda x. x in id`, `typeLetRhs` at boundary 0 enters
level 1; `Lam` creates `X` at level 1, and the body `Var(x)` returns that exact
monomorphic `X` (`Typer.scala:48–67,205–207`). The scheme is
`PolymorphicType(0,Function(X,X))`. Its later use allocates exactly one `X_u`
because `freshenAbove` has one shared variable memo (`:166–188,201–202`).
Both Function ports become `X_u`. No bound or extrusion pair is created by
this identity definition or its simple fresh use. The usual Value scheme is
`forall alpha. alpha -> alpha`; the derivation asserts no complete Yulang
Function/effect scheme from this two-port reference calculation.

For the approved Yulang definition-root incidence, let `I` be the separate
definition root and `X` its formal: `I→X` from the body Name. Do not invent a
separate body-reference row: candidate parameter Names alias their formal
endpoint (`candidate_source.rs:209–217`). Nor identify `I` with a Lambda root
merely because both concern the identity function (`:445–459,477–495`).
If an authentic candidate fresh-use map includes both root `I` and formal
`X`, anchored transport gives `I_u→X`, whereas mapped transport gives
`I_u→X_u`. These graphs differ; neither gives a nontrivial SCC or qualifies
an extrusion pair. Native freshening has a coherent unsigned type map here,
but no source-reference rule chooses which of these two edges it owns.

Polar splitting is source reachable in the original reference; it does not
require a hypothetical externally supplied bound. Infer this term at level 0:

```text
lambda f. let y = f (lambda x. x) in y
```

At the cut before generalizing `y`, the outer formal `F` has level 0. The
initializer is at level 1, so inner formal `X` and App result `Y` have level
1. Its generated comparison is

```text
F <: Function(Function(X,X),Y).
```

The right Function has too high a level for `F`. `constrain` calls negative
extrusion to 0 (`Typer.scala:121–123`). The outer argument reverses polarity,
so the inner identity Function is extruded positively; its argument reverses
again and its result does not. Starting with empty bounds, the shared polar
memo therefore allocates

```text
m(X,-)=X_minus,  m(X,+)=X_plus,  m(Y,-)=Y_minus,
all at level 0, with X_minus distinct from X_plus.
L(X)=[X_minus], U(X)=[X_plus], L(X_plus)=[X_minus], L(Y)=[Y_minus],
U(F)=[Function(Function(X_minus,X_plus),Y_minus)].
```

This follows directly from `:133–157`. Argument traversal creates X_minus
first; positive X traversal then copies the already inserted X_minus lower
to X_plus. Other fresh-copy selected bounds are empty. `X_minus <: X` and
`X <: X_plus` are type constraints, never
Value-reference edges. For example, a lattice valuation with
`X_minus=bottom`, `X=int`, `X_plus=top`, and suitable remaining ports satisfies
these one-sided relations without equating the two copies.

**Native-map impossibility lemma.** For any such event that maps one wrong-level
row `X` in both polarities to distinct rows, no function `h:Value→Value` can
simultaneously satisfy `h(X)=m(X,-)` and `h(X)=m(X,+)`. Otherwise function
single-valuedness equates the two distinct fresh allocations. This is an
elementary proof about the native maps, not a theorem that source references
must preserve type-port positions.

An anchored unsigned source incidence is coherent without `h`. A mapped
incidence needs a declared interpretation: original binder target, one selected
description, separate typed incidence positions, or another approved law.
Duplicating an edge to both polar images is also an additional graph rule;
the native algorithm does not say that one Name occurrence means two targets.
No marginal choice is made independently for each occurrence here. Requiring
one unsigned map to preserve both ports would be a new premise and is refuted
by the displayed native source prefix.

## Nested odd/even: paths and exact scope of divergence

Keep the original user's distinct `n_outer`/`n_inner` binders and conditional
source. Approved ownership proves its root SCC `O↔E`. Current ordinary HIR
admission of its exact indented/conditional/infix text is still absent; this
note does not invent a minus signature or conditional lowering.

Use the smaller Call-bearing analogue already derived in the
[odd/even note](2026-10-12-odd-even-parent-copy-scc-derivation.md):

```text
let rec odd = lambda n_outer.
  let even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

In the original reference, boundary-0 recursive row `O` and outer formal `A`
have level 1. Inner formal `B` and App result `R` have level 2. The inner Call
forces negative demand extrusion, creating level-1 polar copies
`C=m(B,+)` and `D=m(R,-)`. Their one-sided relations are `B <: C` and
`D <: R`. Local `even` generalization is at boundary 1. Its later use makes
fresh `B_u,R_u` while keeping level-1 `C,D` fixed, with
`U(B_u)=[C]` and `L(R_u)=[D]`. Those are use copies, not new extrusion
parent records. These exact native facts and opposite-bound replay were
derived at `odd-even-parent-copy-scc-derivation.md:105–157`.

For the approved source incidence projection of the analogue, the determined
edges include

```text
O→E, O→A; E→O, E→B; R→O, R→B; S→E, S→A.
```

The nested initializer belongs to `E`; its references are not reassigned to
the enclosing `O`. `S` is the final outer Apply result. Standalone Lambda,
Block and formal-row adjacency is not decided by these clauses.

For the extrusion event `B↦C,R↦D`, anchored copying of the known R incidences
gives `D→O,D→B`; event-wide mapped copying, *if separately selected*, gives
`D→O,D→C`. There is no determined outgoing reference for `B`, hence none
to copy to `C` in this projection. Neither finite graph has a path from the
original roots or original ports to `C` or `D`. Thus neither qualifies `(C,B)`
or `(D,R)` in this determined projection. This calculation is not a claim of
their nonmembership in the full unknown graph: unresolved constructor rules
and later events could supply further edges.

Actual SCC partitions distinguish target copying once a whole root SCC is
in the copy domain. For a finite event with `O,E` both in domain and distinct
images `O_u,E_u`, preserving the original graph and only adding copy-owned
edges gives:

| Completion | Added root edges | SCCs on the four roots |
| --- | --- | --- |
| Anchored | `O_u→E`, `E_u→O` | `{O,E}`, `{O_u}`, `{E_u}` |
| Mapped | `O_u→E_u`, `E_u→O_u` | `{O,E}`, `{O_u,E_u}` |

This is a literal path calculation, not merely a difference in edge spelling.
No original root can reach a new root in either completion. Even the second
completion therefore does not put an original root and its copy in one SCC.

**The copy-domain premise is essential.** It has not been derived for the
exported odd scheme in the displayed native history. Original nonrecursive
`even` has a Function scheme, not a separate mutable binder row E at all;
its generic formal/result rows are freshly instantiated before contributing
to outer bounds. Current candidate capture follows its actual type/bound
graph, not definition-root incidence. It cannot be asserted to contain the
original E merely because `O→E` is an approved source edge. If E is outside
the native copy domain, the mapped rule leaves that target anchored and the
table's second cyclic copied component does not follow. A proposal to close
the domain over references can supply this missing domain premise, but is a
new construction decision requiring its own native-typing preservation bridge.
The table is a conditional finite graph characterization, not an observed
candidate history or a source-qualified parent/copy counterexample.

## Apply `konst 1`: reference ownership is independent of provider shape

For `konst = lambda x. 0`, original inference gives `Function(X,int)` with
generic `X`; a use coherently freshens X. Applying it to literal 1 generates
`int <: X_u` and `int <: R` by Function comparison
(`Typer.scala:68–74,106–108`). Its returned provider is the literal; no X
body Name and no runtime pointer to konst is required for the approved edge
`R→K`, where K is the original resolved konst binder row. The definition
root K has no resolved Name occurrence in its literal body in this projection.

If a later native event copies R but does not copy K, anchored and mapped
laws both give `R_copy→K`. If the domain also contains K, they give
`R_copy→K` and `R_copy→K_copy`, respectively. Neither graph creates a
return path here. A proposal to recursively copy K merely because R
references it changes copy reachability even when the native result R only
has a ground int bound. Runtime provider shape and ordinary native type
reachability therefore cannot recover this source target or its domain rule.

This is the approved Apply incidence plus an original Value-only type
derivation. The `konst` name use, complete Yulang Call dispatch, latent effects
and provider/output evidence remain separate obligations. No returned-provider
tuple is substituted for the source incidence.

## A proof of why copy-only transport cannot yet qualify a pair

**Conditional incoming-path lemma.** Let `G=(V,E)` be any directed graph.
An event adds fresh vertices `N`, disjoint from V, and only edges whose
owners are in N. All old-owner edges remain unchanged, and no such edge
targets N. Then no old vertex reaches any new vertex in the resulting graph.
Proof: a path beginning in V would need a first edge from V into N. Every
edge with owner in V is an old edge with target in V, contradicting that
first crossing. Therefore no fresh copy `c∈N` qualifies with its retained
parent `p∈V`, whatever outgoing incidences c copies.

Anchored and mapped append-only cloning both satisfy this hypothesis, even
when copies form cycles among themselves or point back to parents/uncles.
Repetition preserves the same conclusion at each event's creation cut. It
does not prove permanence: a later actual reference producer or incoming-edge
redirection may supply a path into an earlier copy.

This supplies the minimized additional qualification premise:

> Which actual operation creates or redirects an incoming Value-reference path
> from the parent-side graph into this extrusion copy, and what exact scoped
> incidence licenses it? Copying outgoing incidences alone is insufficient.

Parent metadata, inequality insertion, the O/E source SCC, and a cycle between
fresh root descriptions do not supply this premise. The user's statement that
parents can reference children permits such paths; it does not specify the
source/transport operation that constructs them for the pairs in this history.
This is not a restriction on permitted family crossings.

## Original and current-source bridges

**Original reference projection fact.** None of the reference's generation,
bound insertion/replay, level comparison, polar extrusion, scheme boundary or
freshening transition reads a source-reference relation (`Typer.scala:48–188`).
Its `Variable` payload consists of level, lower bounds and upper bounds
(`:221` onward), and no intrusion/SCC operation occurs in this inference owner.
Consequently, for any fixed native history, decorating it with two reference
transport proposals leaves every native allocation, bound, propagation step
and scheme result equal up to the same fresh naming. Induction on the history
proves this because each next transition reads identical native state and
ignores the decoration.

The fact concerns the original implementation, not a proof of Yulang soundness
under arbitrary decoration. Once Yulang uses that graph to add equality, it
reads the decoration and can change bounds and principal schemes. Agreement
before that extra transition does not establish equality preservation afterward.
The original reference determines polar/unsigned type maps, but cannot determine
an additional graph law whose incidences it neither stores nor consumes.

The current Rust owning paths supply the following concrete bridge boundary:

| Owner | Established source operation | Missing graph operation |
| --- | --- | --- |
| `candidate_source.rs:209–217,394–411` | Parameter Name aliases actual formal; Apply retains callee/argument/result/effects and source coordinates | No emitted result-owned resolved-Name incidence |
| `candidate_source.rs:445–459,477–495`; `candidate_scheme.rs:1316–1335` | Separate Lambda recipe, definition body link, installed local root and boundary | No published root-owned Name incidence summary |
| `candidate_extrusion.rs:90–163,224–249` | Polarity/target-keyed allocations, parent retained before selected-bound copying, all four Function ports traversed | No incidence payload or signed target-selection law |
| `candidate_scheme.rs:36–108,1008–1020` | Captured rows/nodes/bounds/context evidence; one canonical row remap preserving anchors and non-generic metadata | No source incidence field or reference-based copy-domain rule |
| `candidate_intrusion.rs:358–488` | Actual lower/upper payload and Function/Effect-dependency scan; component comparison of retained parents | No consumer of the approved source-incidence adjacency |

These are direct inspected constructors/consumers. The earlier reviewed
[source-owner audit](../progress/2026-10-12-value-reference-source-bridge-audit.md)
provides additional HIR locators, but is not used to turn retained coordinates
into emitted edges. Stored bounds alone also do not establish replay: the
odd/even prefix's activation comes from its separately traced opposite-bound
consumer. Nothing here changes the source or scans incidental IDs to recover
unrecorded incidences.

## Claim boundary, obligation economy and next action

Results produced here: a source-derived native identity/polar prefix; a proved
native-map incompatibility with one simultaneous unsigned port map; a
conditional finite copied-SCC comparison with its domain premise exposed;
the conditional incoming-path lemma; and a static original/current source
bridge. None establishes the parent theorem or authentic qualification of
the actual odd/even ports.

Two different methods now reach the same premise: native operational derivation
determines only type maps, while direct incidence/path derivation needs a
target/domain/incoming-path transport rule. Another equivalent graph-copy
lemma would still assume that rule. Under **Natural compiler behavior and
proof-obligation economy** in `rules/compiler-engineering.md`, correct
qualification and equality preservation remain A/B. Reconstructing original
occurrence/binder/owner identities from later bounds is D: source construction
already knows them and can retain them canonically. Their retention removes
identity-recovery debt, but does not decide the semantic target or domain law.
An arbitrary copied-SCC characterization remains conditional research; no
parent gate is reclassified, retired or closed.

The exact OPEN premise is a joint transport contract specifying (1) whether a
copied incidence targets the original binder or a use/copy description,
(2) the native versus reference-closed copy domain, (3) treatment of both
polar images without independent marginal selection, and (4) the actual
incoming-reference producer or redirection needed for parent/copy qualification.
The inspected approved ownership clauses and original Simple-sub do not derive
this contract. Adopting one therefore needs primary authority adjudication;
it is not an authorized implementation detail established by this proof.

One next action: the primary adjudicates this exact contract against intended
ordinary inference and obtains the required design decision for its unresolved
parts, then assigns the source-incidence producer and its matching SCC
consumer with equality preservation kept OPEN. Do not resume another proof
of the same transport premise until it is grounded.

## Checks, resources and frozen dependency snapshot

Read-only commands: `cat`, `rg`, bounded `nl`/`sed`/`head`/`tail` windows;
`git status --short`, `git rev-parse HEAD`, `git branch --show-current`,
reference `git rev-parse HEAD`; exact-input `git diff BASE -- paths`;
`sha256sum`; two UTC clock reads. Initial truncated captures were followed by
decisive bounded rereads. Write: `apply_patch` to this lease only.
Final `python3` text-integrity checks found 414 lines at that check, no trailing
whitespace/tabs, a terminating newline and no missing relative links; they
perform no graph execution. Read-only Git diffs found no direct-input change
against either baseline. `git diff --check` also returned zero, but its
untracked-file coverage is not used as the whitespace evidence.
No Git mutation, test, build, probe, interpreter, Oracle, measurement,
delegation or shared-record edit. At most one lightweight shell/tool process
ran at a time. Allocated wall-time limit: 40 minutes. Exact CPU/RAM and total
reasoning wall time were not instrumented; no resource peak is claimed.

Normal requested policy route: `gpt-6.1-sol/high`. The configured prover role
omits model/effort pins and agent defaults request that route. Effective runtime
model/effort metadata is unavailable to this leaf, so observed settings are
unknown. No Astra, nested process, model override or hot reload is claimed.
Independent review has not occurred; the producer does not certify this note.

Direct read dependencies, unchanged from the pinned Yulang baseline:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| `notes/progress/2026-10-12-value-reference-source-bridge-audit.md` | `13faac40d4e98a689aacc9e4f548ff7aacb717890bb194c9c12113d8d9f1308b` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference `syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-12-value-reference-transport-proof.md`.
- Baseline: `874d43756cc44ce1787b4ca30a7595eeff1bc121`; reference baseline above.
- Changed dependency hashes: none; the direct snapshot is listed above.
- Claim/review: unreviewed native derivation and conditional graph characterization;
  no source-qualified pair theorem, universal preservation or implementation closure.
- Checks: exact source locators, direct-input baseline comparison, note whitespace;
  zero tests/builds/Oracle or executable graph probes.
- Proposed checkpoint: `research: derive native Value copy maps and isolate incoming-reference qualification`.
- Shared-record deltas left to primary/curator: retain the transport and original
  parent equality gate OPEN; record the polar-map incompatibility and required
  incoming-reference premise; distinguish hypothetical whole-root SCC copying
  from native type-reachable copy domains; preserve source admission, complete
  Call, effects, soundness, principality and cutover as OPEN. No shared file edited.
