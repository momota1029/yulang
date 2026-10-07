# Ordinary result checking to the actual Function export

Date: 2026-10-07
Baseline: `8f40797c72c1fe0ca1af14694b1a135fde777c54`
Status: compiler-referee reviewed bounded source/implementation correspondence; research only
Exclusive lease: this note only
Semantic/implementation authority: none

## Objective and result

Trace one nonidentity `Value(A) <= Value(B)` result check through the owning
ordinary Function comparison and final export. The distinct method here is
inspection of the actual result-child construction and its output product,
not a further inventory of the proposed source-contracts §5.3 calculus.

The actual F5 resolver has a result-covariance case. Its result child is an
endpoint pair, and its retained completion is an optional **incompatibility**
witness. Source Lambda construction feeds the body value directly into the
Function result; it does not introduce a checked-result certificate. Final
export reads the definition's bound row and builds a closed type predicate.
These inspected products do not construct the decorated checking evidence
required at the actual successor `B_common` root. This localizes a concrete
construction seam before attempting parent evidence reconstruction.

No independently established current decorated nonidentity inclusion was
obtained. The original Integer/Top semantic cut therefore remains. The
conditional result lifting below separates that cut from the later query
and export cuts. No admitted-source counterexample, accepted successor
`Direct`, gate closure or production defect is claimed. `ALL_VIEW` remains
open; `PRINCIPAL` retains its existing conditional status and open premises.

## Independent review

A compiler-referee reviewed the frozen content at SHA-256
`8e4a535a64dc62ed2a6e5eb2d4f2b74c61e81955048efc7868a1f0c0241eb54f` and
returned PASS with no findings. The review covered the cited F5 result-child
and memo products, the F5/successor boundary, the paired Option 2 conditional
lift, and whether the result-certificate seam sharpens rather than replaces
the existing ALL_VIEW obligation. It did not inspect every resolver route,
execute a probe, or establish successor source semantics. The integration
metadata added after that frozen review leaves the reviewed research claims
unchanged.

## Baseline and governing dependencies

The primary selected the baseline and language meaning. Exact governing
locators, with line numbers at that baseline:

- Typed core `notes/design/2026-10-02-typed-computation-core-elaboration.md`
  §7, L537–560: same decorated values, retained evidence and checking
  constraints; L615–627: actual receiver admission and complete invocation;
  §9, L1083–1122: joint domain/observation containment, not an effective
  subtype algorithm. This construction is Draft, not independently adopted
  concrete inclusion rules.
- Source contracts `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §2.2, L107–142: active independent `DescMem` and admission; §3.7,
  L287–397: paired Option 2 extras; §5.1, L500–527: actual common formation
  and retained value comparisons; §5.3, L658–689: actual-root introduction
  and conditional resolution conformance. Concrete clauses remain Draft.
- Concrete compatibility `notes/design/2026-10-03-concrete-compatibility-boundary.md`
  §1 and §2, L708–720: direct concrete resolution cannot compose successes;
  §4, L763–769 identifies the actual `constrain_live` comparison surface.
- F5 `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
  §§21–22, L525–592: supported body feeds Function result; four structural
  subpairs and Top success. Its retained narrow algebra is evidence about
  that implementation. Charter `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`
  §§1–3 retires F5 Function generalization as the successor target; old
  kernel acceptance is not current complete descriptor authority.
- Certified uses `notes/design/2026-10-04-certified-callback-and-constrained-use.md`
  §6, L527–561: the replacement-root obligation is
  `Direct(B_common(s,a),R_V(v))`, with the same original source witness.
- The predecessor actual-export and Integer/Top notes dated 2026-10-08
  supply the already recorded cuts; their conclusions are not reopened.

The pinned committed answers for production denotation (Option A), bound
membership (Option 2), inlet-context domain and Function call-view formation
were read and compared with baseline bytes. Membership remains independent
of query success; admission includes all independently typed compatible
punctured contexts at original `xi=(nu,K,D)`. Unanchored licensed extras are
permitted. No new role, entry, profile, source restriction or selected
primitive interpretation is inferred from those decisions.

## Exact implementation trace

Use `my f x = 1` only as the existing ordinary source producer. It is not a
source witness for a result annotation or `VIncl(Int,Top)`.

| Construction point | Exact input/output and implication |
| --- | --- |
| `crates/yu-hir/src/module.rs:442`–483 | Complete `ResolvedExpr` inventory includes Lambda/Integer/Name and opt-in shadow structure, with no result-check variant or checked target value endpoint. This is a bounded statement about this enum. |
| `crates/yu-solver/src/lib.rs:1667`–1727 | `emit_lambda` collects the Integer body with `emit_integer(...,None)` and retains its value/effect component positions in `LambdaRecipe`. No independent `B` or value-inclusion evidence enters this recipe. |
| `crates/yu-solver/src/lib.rs:10705`–10745 | `admit_lambda_fact` uses the body's positive live value as the Function result, the original parameter as argument, and the body effect as result effect. The Lambda-owned slot-2 occurrence/provenance records `Function(...) <: definition.root`, then calls `constrain_live_value`. This is source synthesis into the root, not result checking against a target `B`. |
| `crates/yu-solver/src/lib.rs:11292`–11379 | A concrete Function pair enqueues argument, argument-effect, result-effect and result subpairs. L11352–11357 creates exactly the result endpoint pair `lower.3 <: upper.3`. L11368–11371 records value-child diagnostic edges, not complete descriptor clauses. |
| `crates/yu-solver/src/lib.rs:11279`–11290 | A Top upper endpoint completes the local work item without bounds mutation or a positive decorated inclusion certificate. |
| `crates/yu-solver/src/lib.rs:723`–726; L3837–3854; L3972–3990 | The pair key has only lower/upper endpoints; work items have only the task. `TypedPairMemo::Value` holds diagnostic children, direct incompatibility and `Pending/Complete(Option<DiagnosticWitness>)`. Its diagnostic witness has terminal pair, error kind, distance and first field. Original occurrence/cause passed to `constrain_live` remain relevant to provenance/diagnostics; they do not themselves establish membership. |
| `crates/yu-solver/src/lib.rs:15371`–15394 | `component_generalization_draft` selects the actual definition-root row and invokes the F5 generalizer. This call does not consume a result-check proof product. |
| `crates/yu-solver/src/lib.rs:15465`–15473; L15516–15524; L15551–15557 | Finalization recursively rebuilds Function argument/result and fixed pure effect children, then calls `set_scheme` with quantifiers, recursive bounds and predicate. These inspected finalizer cases do not emit complete successor membership/admission or `Direct` evidence. They must not be substituted for the designated `B_common` export. |

The smallest **kernel** result-only comparison with concrete children is

```text
Fun+(Int-, Empty-, Bottom+, Int+)
    <: Fun-(Int+, Bottom+, Empty-, Top-).

children in declared order:
    Int+ <: Int-
    Bottom+_effect <: Empty-_effect
    Bottom+_effect <: Empty-_effect
    Int+ <: Top-.
```

Each child has the F5 trivial action. Symbolic execution of the displayed
branches therefore finds no incompatibility and no bound transition, subject
to ordinary availability admission succeeding. This was derived from code,
not executed. It is kernel behavior, not an independent semantic oracle or a
concrete successor view: no complete decorated literal introduction, strict
Int/Top interpretation, common allowance, admission or Option 2 grammar is
established by that comparison.

## Conditional same-witness semantic bridge

Fix the original source scope tree `T`, witness `w`, `xi=(nu,K,D)`, complete
consumer/provider correspondence, actual role/entry and common allowance `W`.
Let `A != B` without a retained equality identifying them. Assume:

1. An independently typed original result value and an independently established
   same-decoration `VIncl(A,B)` under those exact original scopes and operands.
2. Complete independently interpreted invocation and admission presentations
   for the actual roots; the same admission clauses and receiver/carrier
   contract on both sides. All entry, receipt, consumer, pending suffix,
   request/response, future-provider and non-result predicates match.
3. The only changed hard-envelope predicate is a positive result occurrence
   `MemValue(A,z;w,xi,T)` replaced by `MemValue(B,z;w,xi,T)`. The inclusion
   applies to every occurrence of this predicate, including latent future
   observations, rather than only the one literal return.
4. Production membership has the complete paired §3.7 grammar on both sides,
   with identical `W_abs,Z`, invariant parameters and original witnesses;
   the admission certificate also covers abstract providers. Every actual
   alternative is inventoried. Both source bases satisfy their hard guards.

The checking rule retains the decorated result. For each original admitted
challenge and whole observation tuple, apply hypothesis 1 only at the changed
result predicate; every other conjunct uses its unchanged witness. Thus the
old hard envelope implies the checked envelope without selecting a new
`w`, provider, `xi` or allowance. Executable Return/Call/Bind code and consumers
remain the same, so their source-base relation is unchanged. Requests and
nonreturning prefixes are retained; they are not discarded because this is a
result check.

Induct on the paired finite abstraction derivation: a source leaf retains the
same tuple; an unanchored `Z` leaf retains its original licensed tuple; a
`W_abs` step retains its predecessor and whole rewrite witness; the final
guard uses the proved envelope implication. Hence complete membership is
included at every admitted challenge. Identical admission gives the domain
premise. Typed-core §9's joint law yields semantic Function containment using
the same final projection. This is a **conditional theorem**, with hypotheses
1–4 explicitly supplied; it constructs no finite accepted query evidence.

## First construction seam and failed shortcuts

For an actual result-checking derivation supplied independently, the first
unconstructed source-to-query premise is:

```text
original result check with complete decorated VIncl(A,B)
  -> a finite local inclusion proof at that result occurrence,
     preserving its complete operands and original binder/witness incidence,
     usable by the ordinary whole-Function resolver at B_common(s,W).
```

The inspected F5 result-child rule accepts endpoint tasks, not that proof
product, and retains incompatibility data rather than a successful decorated
certificate. The ordinary source Lambda recipe also supplies no checked target
or such product. Thus success of that child cannot reconstruct the displayed
premise. This is narrower and earlier than asserting an unexplained parent
`Direct` oracle; it names the owning result-check output that must be derived
or identified. The existing primitive interpretation cut still precedes it
when the proposed concrete pair is Int/Top.

Even if that local proof is supplied, the parent must prove the complete
invocation/admission correspondence and all production alternatives at the
**actual** export. The restricted candidate §5.3 Function case requires matched
non-coverage interfaces and does not automatically admit the changed result
interface. Its explicitly conditional adoption/conformance also remains.
No claim is made that the whole repository has no other applicable resolver.

Concrete-success transitivity is falsified by the selected optional-Record
witness `{foo?: string} <: {}` and `{} <: {foo?: int}` succeeding while
`{foo?: string} <: {foo?: int}` fails (compatibility L714–718). It forbids
composing an intermediate export query to discharge this designated root.

The `VIncl`-only shortcut fails as a certificate construction in the inspected
route: it gives neither independently complete admission nor proof clauses
for entry, consumers, ordinary `DescMem`, residuals and paired extras. The
conditional lemma deliberately lists each omitted premise. Removing one
leaves its proof step unjustified. This is proof-premise falsification, not
a Yulang counterexample: no freely chosen alternative semantics, independent
model rows or assumed transition checker are used to claim a source failure.

## Checks, limitations and resources

Checks: bounded `cat`, `rg`, `sed`/`nl` reads; read-only HEAD; one sequential
Python process comparing each direct dependency's live bytes with
`git show 8f40797c...:path` and computing SHA-256. All matched. Navigation
captures that truncated were not used as complete searches; decisive sections
and owning implementation cases were reread in bounded ranges.

No executable probe, mutation run, random seed/range, Cargo build/test,
formatter, compiler edit, child agent or Git mutation occurred. The method
is manual derivation and bounded product inspection. No independent oracle
for decorated inclusion exists in this experiment; the conditional proof
shares its explicitly supplied interpretations and grammar with the source
packages. It cannot validate those source rules by simulating assumed rules.

Resource budget: lightweight read processes and one dependency comparison;
zero heavyweight processes. No numeric CPU, RAM or wall-time limit was
assigned; peak RSS, CPU and total reasoning wall time were not measured.
Output is this unique note only. Source-wide result checking, registered casts,
recursive inclusion, actual complete descriptor/admission production, arbitrary
view validity and production query/export conformance remain unverified.

Recommended next action: derive or identify one original-scoped result-check
certificate from an independently interpreted nonidentity value inclusion,
then specify its consumption by an applicable whole-Function resolver case
at `B_common`; use this construction seam rather than another F5 Top probe.

## Dependency pins and freeze

All direct inputs matched pinned baseline bytes. Principal implementation pins:

```text
1513dc92db0e29fd8258fc5521637d91a603dd72a3e8af1fb1d11fef8121dcd7 crates/yu-solver/src/lib.rs
50d0f1040a29f66c7b2640f2e4ce7fe9ed4def58daaf41e6cc3c3b5e8fab8e4a crates/yu-hir/src/module.rs
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16 notes/design/2026-10-03-concrete-compatibility-boundary.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83 notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80 notes/design/2026-10-04-certified-callback-and-constrained-use.md
```

The four governing rule files, four approved-answer files and two predecessor
notes also matched the baseline. Task/index files were navigation only.
Writes stop at submission. Review is pending; the producer's inspection is
not independent review.

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-all-view-result-checking-bridge.md`.
- Baseline SHA: `8f40797c72c1fe0ca1af14694b1a135fde777c54`.
- Changed dependency hashes: none at comparison; recheck if dependencies move.
- Review status: compiler-referee PASS with no findings on the frozen research
  claims; no theorem/gate status promotion.
- Checks already run: exact section/code reads; baseline/live byte and SHA-256
  comparison; note scope/whitespace inspection. Zero builds/tests/probes.
- Proposed commit message: `research: trace result checking through Function resolution and export`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  the precise result-check proof-product seam under the existing ALL_VIEW cut;
  retain primitive decorated inclusion, whole admission/membership, actual
  export resolution and existing PRINCIPAL prerequisites. No shared record,
  authority, question-board bundle, manifest, lockfile or compiler path changed.
