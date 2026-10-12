# Shared C source bridge: representation escape audit

Date: 2026-10-13
Status: frozen unreviewed research; conditional representation obstruction and bounded constructor audit
Baseline: `c69d0b3629879294511fce4e8e20ceffc791ac53`
Exclusive lease: this file
Method: static falsification of source representation escapes; no solver experiment
Budget: at most 45 minutes, light static work; zero builds, tests or Git mutations

## 1. Objective and result

Can a legal source representation of the fixed correlated helper preserve one
active monomorphic f root, the qualified original C=B event and the actual
native freshening map, while retaining legal int/bool helper uses? Investigate
source allocation and checking constructors, rather than repeating the earlier
frame-fresh C scalar assignment or the ordinary g typing derivation.

No genuine source countermodel was constructed. A precise conditional
obstruction is available: every representation that preserves the native
endpoint map, endpoint incidence and equality interpretation has the same
unsatisfiable four-clause reduct. Adding arbitrarily many correctly scoped
description/checking/proof witnesses cannot repair that reduct. This rules out
those representation escapes under an explicit correspondence premise; it
does not establish that the currently selected source rules supply that premise.

The exact absent application is the source rule for a helper's reference to
an active root of another validating component, together with introduction and
transport of that call's actual extrusion operand C. Existing records describe
same-component Live/Internal and already installed Mono/Established captures.
Neither is the constructor output needed at this nested publication cut.
Consequently no independently legal Source Generalize allocation for this
fixed complete source/event program has been exhibited here. Missing source
construction is not source rejection or impossibility of every future lawful
definition.

## 2. Governing inputs and claim boundaries

- [Nested live-root derivation](../theory/2026-10-13-nested-live-root-generalization-derivation.md), §§3–8: fixed source and event; actual publication graph and map; conditional shared-C contradiction; F is a changed map, not a preserving algorithm.
- [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md), §§2–4, and [construction](../theory/2026-10-08-source-generalize-definition-and-proof.md), §2 L1–L5, §§3.1–3.4,4,5.1–5.3: actual constructor records, whole source clauses, original scopes, source checking and allocation before assignments.
- [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), Approved extrusion-event qualification, Definition-root origin, Qualification: this G/F occurrence qualifies its actual pairs C=B and D=R; freshening is not another extrusion event.
- [Local self-recursion](../design/2026-10-10-local-self-recursive-binding.md), Selected source behavior and Proposed source-to-solver seam: nested active f lookup uses its original monomorphic root; installation follows initializer formation.
- [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md), Decision and Scope: description copying does not copy or retarget Value-reference edges.
- [Parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md), Selected operation: equality affects solving and later use.
- [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–5: preserve ordinary native inference and required natural behavior; do not infer a restriction from a proof difficulty.

This is a complementary researcher packet. The primary's prover lane owns
the constructive parent obligation. The yulang-proofs skill was read for the
source correspondence boundary; no delegation or independent review occurred.

Claim classes: a conditional finite no-go statement and a bounded negative
constructor audit. No established source-preservation theorem, source-qualified
refutation, source acceptance result or principality result is claimed.

## 3. Exact finite statement and hypotheses

The fixed source, copied only to identify occurrences, is

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

Let H be its actual native history from the input derivation §4. For two
independent published g uses, its unchanged maps satisfy

```text
mu_i(o)=o; mu_i(C)=C; mu_i(B)=B_i; mu_i(S)=S_i.
```

Quantify over any complete source representation R with any finite allocation
schema and any number of legal logical intermediates, including endpoint
terms and per-frame ViewLogic/EventProof witnesses. Assume:

1. **Faithful endpoint incidence.** Its interpretation of H assigns one
   endpoint to each retained native coordinate. Repeated references and root
   ports use that same interpretation. The g Function input and original
   extrusion parent are both B; they are not separately reinterpreted at
   different occurrences. Interpretation commutes with the actual mu_i:
   the image of C is one shared endpoint c, the image of B_i is b_i.
2. **Faithful equality transport.** The qualified C=B clause is active before
   the relevant publication/uses, or its full translated clause is active in
   both independent frames. Its interpretation is endpoint equality, so it
   supplies c=b_0 and c=b_1. The actual G/F origin, pair identity and lineage
   are retained. This is a correspondence premise, not a rule derived here.
3. **Faithful use projection.** The actual wrapper and first succ consumer
   entail b_0 <: int through B_0 <: S_0 <: V_0 <: int. The second actual
   argument entails bool <: b_1. This is exactly the already displayed native
   source-use reduct, not an independently chosen client W or marginal view.
4. **Scalar relation laws.** Equality permits substitution, subtype is
   transitive, and bool is not a subtype of int under the retained primitive
   relation. Full source validity implies these scalar projections.

**Conditional conclusion:** R has no joint satisfying interpretation for
these two uses. Therefore no representation satisfying 1–4 can be the sought
legal countermodel. Hypotheses 1–2 contain the unestablished source bridge;
their conditional use must not be reported as establishing that bridge.

Proof: projecting any purported joint interpretation gives

```text
bool <: b_1; b_1=c; c=b_0; b_0 <: int.
```

Substitution and transitivity give bool <: int, contradicting hypothesis 4.
This argument also covers endpoint terms: evaluate the terms under the one
joint scoped strategy first, then apply the same relations. Additional source
clauses or existential proof witnesses cannot satisfy a conjunction whose
retained reduct is false. Per-frame body proofs about one event may differ;
their difference does not change the retained endpoint equalities.

This is an inclusion-minimal derived clause witness, not a minimal source
program claim. Removing respectively the four clauses permits assignments
all int; b_1=bool,c=b_0=int; b_1=c=bool,b_0=int; or all bool. These are just
minimality checks of the reduct, not source admissibility certificates.

## 4. Source representation escapes tested statically

| Proposed escape | Owning rule and result |
| --- | --- |
| Add ViewLogic or EventProof witnesses per description frame | Construction §§3.3,5.2 allow these at their own telescopes, with shared actual operands. A witness for c=b_i still requires that equality. A fresh intermediate d_i with c=d_i=b_i gives the same reduct. The rules do not replace native C by d_i. |
| Use endpoint terms rather than fresh constants | §5.2 permits terms of the right sort/telescope. With unchanged C incidence their evaluated images still share c. Making C's interpretation depend on frame i violates the commuting native map premise, even if o itself stays shared. |
| Check y at a wider argument description while returning a narrower description | §3.2 permits genuine local inclusion proofs. Native App first infers y as B and demands Function(B,R); g's actual root is Function(B,S). Replacing the event's parent by a widened checking target changes this demand/pair, or assigns two interpretations to the same B port. A check alone grants neither change. A source-to-native theorem explaining such a split would be new required evidence, not a countermodel satisfying hypothesis 1. |
| Check the helper at a weaker whole Function interface | A lawful complete Function check retains its original interface/evidence and proves the checked-domain and observation inclusions. It does not delete the intrinsic equality/use clauses or replace the source's selected final root without an actual formation boundary. A weaker client description cannot make a retained unsatisfiable conjunct true. |
| Put the equality solely in the original base event proof | This need not produce the frame equalities of hypothesis 2. Thus it is outside the conditional theorem. No selected constructor establishes that this routing implements equality affecting the actual later native uses. It is the precise transport question, not an established escape. |
| Reclassify C as a per-event coordinate | §5.2 keys EventField by actual source event, not by freshening. The fixed native C is reused in both maps, and copying descriptions creates no extrusion occurrence. A new key cannot silently replace its identity. An independently proved operational interpretation relating such fields to the shared coordinate is absent. |
| Capture f as Established or make f Internal to K_g | The former requires an installed contract, which this f lacks. The latter requires actual component registration, and whole-component new would allocate that component's description tuple. Neither existing rule supplies cross-component active capture preserving the one live tuple. |

This table audits the selected rules as constructors, not possible arbitrary
mathematical interpretations. No claim is made that the table enumerates every
future independently established constructor.

## 5. First absent source constructor

At the resolved Name f inside g's initializer, the required source output is
an authentic typed dependency on the still-open tuple rooted at o in K_f,
from g's own K_g description program. It must retain the actual call demand,
extrusion operands/pair clauses and their original scopes through publication
and both subsequent g descriptions. The adopted §3.3 record catalogue has:

- Live/Internal supplied by recursive-group registration for its own joint
  component; and
- Mono/Established supplied by an actual installed immutable contract or
  monomorphic rebind.

It supplies no application for this different-component active open root.
Additionally no inspected owning rule introduces extrusion-created C with
the source classification and telescope needed by the §5.1 walk. Numeric
level, target bound-store membership and Value SCC qualification do not
manufacture that source introduction. The next rule must establish these
outputs and their endpoint/transport meaning; inventing a Shared or EventProof
record without that owning application would assume the answer.

Current Rust scheduling supplies only a narrower operational fact:
candidate_source.rs:252–309 tracks active initializers; :382–385 emits a direct
Action::Link for this lookup; :396–411 retains Apply endpoints;
candidate_scheme.rs:1320–1334 installs the eventual root/boundary and
:1366–1381 captures/freshens a later use. These constructors do not emit the
required Source Generalize records. This confirms a concrete existing owner
for retained active-entry incidence, without establishing its missing law.

The audit therefore separates two conclusions: the current catalogue lacks
the application needed to construct an admissible representation, while any
completion that independently establishes hypotheses 1–4 cannot rescue this
joint use by extra proof allocation alone. Neither conclusion licenses F,
a changed equality meaning, or a new supported-source restriction.

## 6. Evidence, coverage and resources

Commands: bounded cat/sed/rg of the governing documents and native
Typer.scala; read-only git rev-parse, status and an explicit dependency-path
diff against the baseline; sha256sum; one apply_patch for this leased note.
Initial combined captures of task/search material were truncated; decisive
Source Generalize constructor/allocation and derivation sections were read
in narrower captures. Two first Rust reads used the input note's abbreviated
yu-solver path and failed; rg --files located the actual crates/ paths and
the relevant owners were then read. No whole-repository absence is claimed.

Oracle independence: no executable checker or differential oracle was used.
The native map was read from the actual reference constructor; source
allocation permissions were read separately from the selected source rules.
Both remain connected by explicit hypotheses 1–2. Primitive separation and
the displayed scalar use projection are shared assumptions, not independent
validation of full Call or source semantics.

Coverage: this one source, its two actual uses, the selected record/allocation
catalogue and the listed checking escapes. No seeds, numeric search ranges,
solver mutations or runtime inference were used. The four deletion
calculations characterize clause minimality only. Zero heavy processes,
builds, tests, benchmark samples, children, code edits or Git mutations.
CPU/RSS and exact reasoning wall time were not measured; work stayed within
the assigned 45-minute bound. Effective runtime model/effort metadata unknown.

Failure conditions for the conditional result: a genuine independently
established source rule can invalidate a hypothesis, for example by proving
that equality is faithfully applied only to a base environment without the
per-frame clauses while explaining all actual later-use behavior. Such a
result must explain correspondence, not merely omit hypothesis 2. A source
admission proof can also show that the assumed scalar projection is wrong.
No such derivation was found here.

Unverified: complete Yulang source admission, full Call/effects and EventField
construction, recursive introduction L4, all possible source checking
grammars, equality activation/replay timing, general soundness, required
principality, normal progress, termination, production correspondence and F5.
The exact odd/even source is not substituted for this helper; its extrusion
parent is subtraction result T, not B, and its one inner use is not this
heterogeneous two-frame discriminator.

Recommended next action: have the primary's constructive source lane supply
the missing active-root/extrusion-operand owning application and prove or
refute the commuting endpoint/equality transport premise. Apply this finite
obstruction to its result; if all hypotheses hold on an admitted source,
return that source-qualified contradiction to design authority. Another
scalar satisfiability assignment cannot resolve the missing source premise.

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-shared-c-source-bridge-falsification.md`.
- Baseline SHA: `c69d0b3629879294511fce4e8e20ceffc791ac53`.
- Dependency changes: none by this worker; explicit baseline diff was empty.
- Frozen hashes: Generalize selection `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`; construction `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; assigned nested derivation `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9`; occurrence qualification `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775`; local self-recursion `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895`; parent-copy decision `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b`; copied-row ownership `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd`; candidate_source.rs `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49`; candidate_scheme.rs `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1`; reference Typer.scala `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.
- Review status: unreviewed producer artifact, research only; no parent closure or authority promotion.
- Checks already run: static constructor/escape audit, explicit four-clause derivation and deletion calculations, baseline/dependency inspection and hashes; no code/tests/builds.
- Proposed checkpoint message: `research: audit shared-C source representation escapes`.
- Shared-record deltas left to primary/curator: record conditional impossibility under commuting endpoint/equality transport; keep that premise and the active-root/extrusion-operand construction OPEN; record that proof witnesses/endpoint terms alone cannot repair its false scalar reduct. No shared task, index, authority, theory-map or question-board file changed. Writes stop at handoff.
