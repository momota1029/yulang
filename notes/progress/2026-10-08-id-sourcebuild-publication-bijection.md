# Exact id publication: canonical owner identity audit

Date: 2026-10-08
Status: research-only conditional construction and minimized representation counterexample; compiler-referee reviewed; source-owner premises remain open
Baseline: `b84fa53e3e5a75d561a874219d25525d1e72d4a0`
Branch: `research/simple-sub-intrusion`
Exclusive lease: `notes/progress/2026-10-08-id-sourcebuild-publication-bijection.md`
Authority: no production implementation, source-rule change, theorem closure or cutover

## 1. Objective, method and authority

Audit whether the allocation identity of a proposed immutable
`Arc<IdPublicationOwnerRecord>`, joined to `DefinitionRootId`, can represent
the exact source publication `p_id` for the singleton unannotated immutable
binding `my id x=x`. Method: explicit domain definitions, conditional
constructor derivation, and a smallest witness against payload-only
canonicality. No executable semantic model or compiler experiment is used.

The selected [source Generalize definition](../design/2026-10-08-source-generalize-definition.md)
§§2–4 and [source construction/proof](../theory/2026-10-08-source-generalize-definition-and-proof.md)
§§3, 4, 5–5.2 govern. The recorded user selection in
[its review](2026-10-08-source-generalize-review.md) §1 authorizes that native
source definition; it supplies no production architecture approval.
[The id instance](../theory/2026-10-08-id-sourcebuild-instance-candidate.md)
§§1–2 supplies the exact H-source scope as a conditional research instance.
[The SourceBuild owner draft](../design/2026-10-08-id-sourcebuild-owner-design.md)
§§3.1–4.1 proposes the Arc representation and explicitly leaves its supplier
and bijection unproved. Its failure alternatives in §5 are unselected.
The draft is a hashed input, not semantic authority.

Preserve these accepted distinctions: final source root versus public/F5
root; fixed actual anchors versus inferred descriptions; publication versus
registration, execution and Rust storage transfer; H-source versus H-bridge.
No pending question-board answer is consumed. This audit adds no source
restriction or annotation requirement.

## 2. The exact proposition and its domain

Fix an authentic source-owner context `Omega`: one admitted definition
occurrence, its actual anchor formation and its publication derivation, with
the original fixed world/registration/initializer operands. `Omega` is a
mathematical context, not a proposal for a new runtime ID. A HIR artifact can
be reused in multiple construction/solve attempts; its brand alone does not
identify this context or actual initialization operands.

Let `B_Omega={b_id}` and let `h(b_id)=r` be its authentic HIR definition join.
Let `P_Omega` contain exactly the source immutable-binding publications of
this binding in this owner context. Exclude Name lookup, instantiation,
invocation, registration, RHS execution, F5 scheme installation, terminal
transfer, later alias publication and separately exported tuples. This is
the event family addressed by the draft, not all source exports sharing a
component. Let `A_Omega` contain the distinct certified publication-owner
allocations retained on successful SourceBuild freeze. Arc handle copies of
one allocation are one element of `A_Omega`.

`Pub_Omega(p,b,C,R,alpha)` means the authentic source publication rule emits
event p for b, selects validating component C and final root R, and retains
the actual anchor-owner link alpha and complete dependent operands.
`Rep_Omega(a,p)` means the certified constructor assigned allocation a to
that very rule output. Neither predicate is defined by equal IDs, equal
payloads or successful solving.

The draft's exact singleton assertion needs both of these propositions:

```text
Semantic uniqueness:
  exists exactly one p in P_Omega such that
    Pub_Omega(p,b_id,C_id,R_id,alpha_id).
  Every p in P_Omega is that output, with those exact incidences.

Canonical representation (on successful certified freeze):
  for every p in P_Omega, exists exactly one a in A_Omega: Rep_Omega(a,p);
  for every a in A_Omega, exists exactly one p in P_Omega: Rep_Omega(a,p).
  Rep_Omega(a,p) preserves root(a)=h(b_id), C_id, R_id and alpha_id,
    including every actual dependent anchor operand.
```

The first assertion is about source events. The second is about objects:
it gives an encoding `enc:P_Omega -> A_Omega`, injectivity
`enc(p)=enc(p') => p=p'`, and surjectivity onto **certified retained**
allocations. It also gives the inverse decoder. The root join commutes with
the source binding join. Handle equality for the event encoding must use
allocation identity, e.g. `Arc::ptr_eq`, rather than payload `PartialEq`.
The pair `(r,a)` supplies the HIR join and event representation; a fresh
numeric event ID is not logically necessary under these hypotheses.

Semantic uniqueness is stronger than the bijection alone: two authentic
publications could have two correct distinct owner records. Thus the Arc
pair can distinguish events even where root-only uniqueness is false, but
that does not establish the draft's one-publication-per-binding assertion.
Across different `Omega` contexts, event identity must remain separated even
if the HIR root is reused. The theorem never identifies all publications of
one root across time, compilation attempts or source-owner contexts.

Under an optional complete-or-absent policy, F5 success with no sidecar has
`A_Omega=empty`; it is outside the successful-certified-freeze proposition.
There is no surjectivity assertion from all semantic events to all F5 results.
Whether missing metadata should prevent compilation is the primary's
unresolved failure-policy decision, not a consequence of this encoding.

## 3. What the selected source rules establish

Source construction §3 starts with an actual initialization event, or an
actual inert source closure/delay and fixed captures. §3.3 produces typed
owning-rule records and distinguishes actual Executed/OneShot operands from
Internal descriptions. §5 identifies a publication as the actual source
event prescribed by the source. FinalRoot selects the final annotation
target, an actual selected common formation, or otherwise the complete
synthesis root. For the exact id instance with no annotation or actual common
formation, that last case gives R_id, conditional on authentic formation.
§5.1 deliberately distinguishes member and joint-tuple publications that
can use the same component; §5.2 retains p in ScopedClosure.

These rules establish the required event/root/anchor meaning **given the
authentic source event and local-law suppliers**. They do not provide a
source-to-HIR lifecycle lemma counting exactly one relevant publication per
DefinitionRootId, and they do not govern Arc allocation canonicality.
Fixing one actual p in the source judgment does not prove there can be no
second publication in an unspecified owner context. Conversely, one compiler
allocation does not prove that its payload denotes any authentic p.
SRC/SRC-J/GS/GC operate over the supplied source records and genuine L1–L5;
they do not discharge this absent production-owner correspondence.

The claim that the restricted event family is a singleton is therefore a
**candidate source-owner premise**, not an established theorem of this
compiler. It may be proved by the actual one-binding publication constructor
and its source derivation; it must not be installed as a new language meaning
merely because one record is convenient.

## 4. Conditional construction and proof

The following is a construction sufficient for the representation theorem.
It is a proposed engineering invariant, not an implementation authorization.

**H-pub.** The authentic owning source derivation for this admitted input
contains exactly one relevant publication introduction and supplies its
actual p, source binding/HIR incidence, C_id, selected R_id and complete
anchor-owner output. All selected applicable L1–L5 premises are genuine.
The no-other-publication statement is proved from that owner's rule/derivation
inventory, not from an Arc count.

**H-linear.** Staging receives that owner output through one private single-use
construction route. Its publication-record transition is `Ready -> Frozen`:
it creates one fresh immutable record for the supplied authentic output and
retains the resulting strong Arc. There is no second `Ready` token/producer
for that same output in this context; subsequent views, session transfers
and result transfers copy/move only this Arc. The constructor cannot be
replayed, structurally deep-copied into a new certified allocation, or invoked
independently by two staging paths for the same source event. These are
control-flow/ownership obligations to prove, not a Boolean `valid` field.

**H-fields.** This transition stores the exact source binding root, C_id, R_id
and anchor link; joins validate the actual HIR and source-component owners.
The anchor owner supplies complete original operands for the actual permitted
formation. Inert registration is an authentic closure/registration owner;
ReturnedInstallation requires its actual Executed/OneShot and same-world
tuple. Tags or schema variables do not supply missing actual operands.

**H-retain.** After freeze, the record and transitive dependencies remain
immutable and alive through their final use. Identity comparisons keep strong
handles alive; no raw address is used as a historical event key after its
allocation is freed. Any borrowed closure view remains bounded by its owner.
Fallible staging produces the whole package or no certified allocation.

**Conditional theorem.** H-pub, H-linear, H-fields and H-retain imply the
singleton semantic and representational propositions in §2 on successful
freeze.

Proof: H-pub gives `P_Omega={p_id}` and its unique correct incidence tuple.
On the sole Ready-to-Frozen transition, H-linear creates allocation a_id;
fresh allocation identity separates it from other simultaneously live owner
records. No later permitted transition creates another certified allocation:
Arc cloning preserves the allocation and moves preserve its ownership.
Induction on those later storage/view transitions yields
`A_Omega={a_id}`. Define enc(p_id)=a_id and dec(a_id)=p_id. Each composite
is identity on its singleton domain, giving injectivity, surjectivity and
unique decoding. H-fields proves the commuting HIR join and exact selected
component/root/anchor preservation. H-retain preserves these incidences and
the comparison domain until use completes. Staging failure proves no theorem
about a frozen package because none exists. QED, conditional on those premises.

Only the canonical-object part follows from the proposed linear route.
H-pub remains the precise absent source-owner premise. An implementation or
checker of the Ready/Frozen model could demonstrate agreement with H-linear;
it would not prove H-pub or that the selected source rules have an authentic
production supplier. No such checker was run here.

## 5. Smallest failure witnesses

**Duplicate-allocation witness.** Take one authentic event p_id with one
binding, one HIR root and one correct incidence/anchor tuple. Allocate two
immutable records a0 and a1 with identical fields using two fresh Arc
allocations. Let `Rep(a0,p_id)` and `Rep(a1,p_id)` both claim authenticity.
All payload/root/component/root-selection checks succeed, but
`a0 != a1` by allocation identity. A decoder from allocations to p exists
and is total, yet it is not injective and no inverse encoder can cover both
allocations. There is no bijection. This witness is minimal among nonempty
singleton-event witnesses: one allocation cannot violate the exactly-one
allocation property; two suffice. It is a representation counterexample,
not a Yulang program refuting source Generalize.

**Missing-record witness.** Keep the same one event, but retain no certified
record. The empty allocation family cannot be the surjective image of the
nonempty event family. This is minimal. It discriminates a claim about all
F5 successes from the narrower successful-freeze claim; an explicitly
optional no-sidecar outcome is not automatically a policy defect.

**Root-only cross-context witness.** Reuse the same HIR artifact/root in two
owner contexts with distinct authentic source events p0 and p1, e.g. distinct
actual initialization/registration operands. The root projection maps both
to r, so root-only decoding is not injective. Two contexts/two events are
minimal for this collision. This is an underdetermination witness against
discarding Omega and owner evidence, not a claim of two publications in the
one fixed exact-id owner context. Equal displayed types, code and HIR joins
do not determine actual world/event operands.

Named mutations for a future discriminating lifecycle audit are: replay the
publication constructor; deep-copy a certified record; omit terminal strong
retention; replace anchor operands with matching tags; coalesce records by
root across source-owner contexts. The first two attack H-linear, the third
H-retain, the fourth H-fields/H-pub, and the fifth the event domain. They
were reasoned about here and were not executed.

## 6. Bounded compiler correspondence

| Inspected fact | What it establishes | Missing event obligation |
| --- | --- | --- |
| `yu-hir/src/module.rs:185` DefinitionRootId; equality at `:207` | Exact artifact pointer brand plus DefId payload equality; root copies share that HIR identity. | No publication rule, source-owner context, selected semantic root or anchor tuple. Root identity is not DefId pointer identity. |
| Root creation at `:928`, lower_plan at `:1288`–`:1358` | One branded root and one constructed HirBinding for this admitted plan; parameter q belongs to it, and Lambda/body Name joins are retained. | Source binding-to-HIR incidence needs H-identity; one HIR item does not count source publication events. |
| `lower_leaf` at `:1997`, plain header at `:2025` | Body resolves to the same parameter; plain header accepts the required identifier/one-parameter structure. | No immutable-world/registration/publication local law is emitted by these shape checks. |
| `yu-solver/src/lib.rs:510` CollectedDefinition; `scc.rs:689` component query | Collection/component joins exist for the structural singleton plan. | Authentic source C_id and complete relation need their source constructor; a plan ID does not select semantic R_id. |
| Scheme replacement at `yu-solver/src/lib.rs:14166` | F5 scheme installed once in its dense position. | No source publication event, independent selected source root or anchor payload is supplied. Exactly-once installation counts a different event. |
| `finish` at `:15740`; SolvedModule construction at `:15970` | HIR, schemes and solver result fields transfer to a frozen Rust result. | No proposed publication/anchor owner is present in the inspected fields. A move preserves an existing identity; it cannot establish source authenticity or create a missing supplier. |

This is a bounded inspection of the ordinary HIR binding/Name path,
collection/SCC joins, scheme installation and result transfer. It is not a
whole-repository proof that no owner exists anywhere. No source text was
parsed, no compiler source was edited, and no test, build or benchmark ran.

## 7. Oracle independence, residuals and next evidence

There is no executable oracle, random seed, search range or exhaustive
enumeration. The source specification supplies independent semantic meaning;
the draft supplies the candidate storage shape; production source inspection
supplies structural facts only. They share the selected H-source assumptions.
The source specification is independent of F5 success, but its genuine local
laws are explicit dependencies, not a newly checked oracle. The conditional
proof does not validate those laws or H-pub. The finite witnesses test logical
implications about encoding cardinality and domains, not source soundness.

Omitted cases: annotations, common formations, imports/captures, State,
recursion, multi-definition and tuple exports, alias re-publication,
all-language acceptance/principality, public projection, alternate pointer
serialization, resource/failure-policy selection and concrete anchor-owner
payload cost. No failure policy is promoted from the draft.

The exact blocker is the absence in this inspected construction path of an
authentic publication-owner rule output and its one-per-context event
derivation, followed by a proved canonical record-retention route. Additional
root-equality or Ready/Frozen toy checks would leave that premise untouched.
This is construction/retention evidence to obtain at the owner; it is not an
all-view characterization that Arc identity can prove later.

Recommended next action: identify the permitted exact-id anchor/publication
owner and return its actual local-rule output contract and source derivation,
including event count and FinalRoot incidence, for independent review. Then
audit the one private staging/retention path against H-linear/H-fields/
H-retain. Keep production authorization and failure-policy selection separate.

## 8. Dependency snapshot, checks and commit packet

All tracked dependencies below matched baseline bytes at initial inspection;
the draft was already untracked. SHA-256 values:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-08-id-sourcebuild-instance-candidate.md` | `5b7d468bbe32fdded65b3c6e90f00a231ac7b9fca05cfd1ca9924f3468f890b9` |
| `notes/progress/2026-10-08-source-generalize-review.md` | `dcb73203e4b5b845e401f8705fbd1fc513b3791595120fa2db5fac94b7df6b5b` |
| `notes/design/2026-10-08-id-sourcebuild-owner-design.md` | `7dfc6e6a00d749089d15d24372e3258c511b5014364d834d666a1eec95b9e39d` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |
| `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |

Verification command: one read-only Python note check validates local Markdown
link targets, final newline, absence of trailing whitespace, the eight hashes
above and equality of tracked dependencies to the pinned baseline; read-only
Git checks inspect HEAD, branch and the exact leased-path diff. Results are
reported in the producer handoff. These checks validate the artifact snapshot,
not the mathematical proof. No independent review was performed by this
producer. The artifact is frozen at handoff; no further writes occur while
it is submitted for review.

Resource envelope: one note; bounded reads and one lightweight check process;
zero Cargo/test/build/benchmark processes and zero semantic probes. No supplied
numeric CPU/RAM/wall-time budget accompanied the packet. No expansion was
taken; actual peak RSS, CPU time and elapsed wall time are unknown. No search
was interrupted or incompletely enumerated because none was launched.

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-08-id-sourcebuild-publication-bijection.md`.
- Baseline SHA: `b84fa53e3e5a75d561a874219d25525d1e72d4a0`.
- Dependency changes: none observed on tracked inputs; the hashed untracked
  draft is a non-authoritative read dependency, not part of this lease.
- Claim/review status: conditional construction and minimized representation
  witnesses; compiler-referee passed the conditional claim at frozen SHA-256
  `b5cf16b216cd0e9105fa73d34c63968e0ebc635aaddec86768e93566c0fefa35`; no
  production correspondence certification or gate closure.
- Checks: narrow note/link/whitespace/hash/baseline check and read-only Git
  branch/HEAD/path-scope checks; no compiler checks.
- Proposed commit message: `research: audit exact id publication owner bijection`.
- Shared-record deltas left to primary/curator: record the separate H-pub and
  canonical-allocation obligations in the owner draft/active gate; preserve
  the successful-freeze domain and source-owner-context scope. No task,
  theory-status, index, authority or question-board file was changed.
