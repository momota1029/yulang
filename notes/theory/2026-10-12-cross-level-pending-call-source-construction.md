# Fixed nested-recursive core: HIR construction and candidate admission stop

Date: 2026-10-12
Status: frozen unreviewed research; conditional static HIR construction and
entrypoint characterization; candidate state and intrusive preservation OPEN
Assigned baseline: `39c06498c801e9affa2fc664019ac0bde0cb7bc5`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen objective, statement and exclusions

Fix the original term, including both recursive bindings and distinct formals:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

The imported stock theorem concerns exactly this term: its native simplified
interface is `Theta = Top -> Bot`, and every finite derivation in the paper's
specified system at type tau satisfies `Theta <= tau`. During initialization,
odd is monomorphic; even has an allocated recursive root despite its unused
self binder. Inner and outer publication boundaries are respectively 1 and 0
in that reference derivation. This pass changes none of those quantifiers.

The assigned existential bridge asks for an actual syntax-directed candidate
construction of this closed term reaching the authentic inner call-demand
extrusion, with occurrence identity, origin E / receiver O, joint polar pairs
`(C,B,+,1)` and `(D,R,-,1)`, pending original demand k, transformed child Qc,
admitted processing relation and bound evidence, followed by publication and
use. A scalar projection or arbitrary Scala-state translation is insufficient.

For locating that construction, use the closest module spelling, with explicit
braces so no indentation-body choice is introduced:

```yulang
my odd n_outer = { my even n_inner = odd n_inner; even n_outer }; odd
```

This spelling preserves the two named function binders, the two formal Names,
both Apps, the inner sequential publication and the final odd Name. Its outer
binding is a module definition. Equivalence of that module publication with
the reference recursive Let is an additional operational bridge, not assumed
by this note. No second definition, wrapper-local binding, annotation, primitive
or literal is substituted for the final Name.

**Claim class:** conditional static construction plus bounded entrypoint
characterization. For every recovery-free CST of the displayed spelling with
the direct-root binding/expression and brace/ML shapes described below, a
successful `lower_module_with_local_source` constructs the stated carrier and
final resolved Name. On that HIR, `CandidateInference::solve` returns
`CandidateError::Unsupported` before collection. This last consequence follows
from its item match, without assumptions about solver transitions. Resource
availability is required for successful HIR allocation. Parsing this exact
byte string was not executed; recovery-free CST formation remains unverified.

Exclusions: no admission theorem for the language or other compiler routes;
no candidate session is supplied; no k/Qc relation, bound fiber or occurrence
activation is assumed; no intrusion execution, equality-preservation theorem,
complete Call/effect adequacy, principality extension, failure recovery,
termination or production cutover. The original universal parent remains OPEN.
The stop condition is the first unsupported admission/constructor relation.

## 2. Governing sources and actual constructors

Authority is top-level inference principles §§1–5; parent-copy SCC design
**Selected operation and compiler responsibility**, **Apply-result
source-fragment ownership**, **Nested Apply membership**, **Definition-root
Value ownership**, **Retained boundary**; value/type association **Approved
extrusion-event qualification** and **Definition-root origin for nested
call-demand extrusion**; copied-row ownership **Decision**. Local self-recursion
**Selected source behavior** and **Proposed source-to-solver seam** specify the
temporary monomorphic local binder and publication ordering. These decisions
do not assert that the present candidate API admits the displayed module.

The imported dependencies are the reviewed stock core result, the extracted
candidate consumer law, and the reviewed conditional continuation boundary,
all with their original limited scopes. Their headers retain historical
unreviewed labels; reviewed status here is the primary's assignment evidence,
not this producer's certification.

| Responsibility | Exact source owner |
| --- | --- |
| Root semicolon progression | `yu-syntax/src/root_statement.rs:153–158` |
| Same-line ML argument node | `yu-syntax/src/expression/operator_chain.rs:758–805` |
| Opt-in carrier API and nonshipping boundary | `yu-hir/src/shadow.rs:36–43` |
| Complete module namespace / root plans | `yu-hir/src/module.rs:939–945,1286–1335` |
| Carrier creation before ordinary placeholder body | `yu-hir/src/module.rs:1388–1427` |
| Outer parameter Lambda formation | `yu-hir/src/module/local_source.rs:286–321` |
| Local self identity, parameter shadowing, restore/publication | `yu-hir/src/module/local_source.rs:329–372` |
| Distinct artifact-branded expression occurrences | `yu-hir/src/module/local_source.rs:438–475` |
| ML Apply callee/argument formation | `yu-hir/src/module/local_source.rs:488–579` |
| Lexical Name resolution, then module fallback | `yu-hir/src/module/local_source.rs:636–657` |
| Brace local binder and sequential work formation | `yu-hir/src/module/local_source.rs:698–828` |
| Direct-root final Name lowering | `yu-hir/src/module.rs:1493–1547,2086–2165` |
| Carrier preflight and final item rejection | `yu-solver/src/shadow_apply.rs:79–110` |

All paths in the table are under `crates/`. Existing
`yu-hir/src/tests/local_self_recursive_binding.rs` supplies inspection-only
fixtures of the same binder and nested-helper shapes; no test was run, and a
fixture is not exact-program execution evidence.

## 3. Conditional syntax-directed HIR construction

The direct-root plans contain one binding odd and one expression odd. The
namespace includes exactly that DefId, so outer recursive odd Names resolve
to it. The carrier's first slot is the outer Lambda; its formal n_outer is
installed before the body. The body is the brace Block. Its only local binding
even receives a HirLocalId, distinct from the module odd root and both parameter
IDs. Its parameterized initializer installs even's temporary self identity,
then n_inner, and forms the inner Lambda and App. Neither inner Name refers to
even. Publication restores that initializer's lexical additions and installs
even for the final Block App; n_outer remains visible.

Up to names for artifact identities, the carrier graph is:

```text
Lambda(n_outer,
  Block(bindings=[even],
    initializer(even)=Lambda(n_inner,
      Apply(Name(odd: ModuleDef O), Name(n_inner: Parameter P_inner))),
    final=Apply(Name(even: Local L_even), Name(n_outer: Parameter P_outer))))
```

This accounts for nine LocalSource expression slots: two Lambdas, one Block,
two Apps and four Names. The separate direct-root final expression is
`ResolvedExpr::Name(NameResolution::Resolved(odd DefId))`. Each carrier
expression has its own HirOccurrenceId and SourceNodeKey. LocalSourceIndex
ownership remains the outer DefinitionRootId; LocalSourceBinding's HirLocalId
identifies even without creating another module DefinitionRootId.

This HIR identity is evidence of source occurrence retention only. The approved
origin E is the semantic root of even's definition, and the receiver O is the
resolved odd definition. Carrier arena ownership by O must not be mistaken for
the approved call origin. No extrusion event or Value-reference incidence is
produced merely by the above identity formation.

No unresolved or ambiguous Name, annotation or Operation appears in this
carrier. Consequently `candidate_source.rs::preflight`, lines 82–112, returns
Ok for it. The ordinary ResolvedExpr body of odd is a Lambda around an
UnsupportedExpression placeholder for the brace body: `direct_atom`,
`yu-hir/src/lib.rs:184–193`, accepts only integer/identifier atoms; the ordinary
`lower_simple_chain`/`lower_body` emits the placeholder at
`module.rs:2103–2107,1682–1695`. The opt-in carrier is formed separately;
`retain_placeholder_errors`, `candidate_source.rs:143–158`, explicitly permits
this initializer placeholder for the private candidate path.

These facts characterize the source carrier rather than ordinary semantic
admission. The public `lower_module` uses default counters at
`module.rs:876–882` and does not form that carrier. Its brace-body placeholder
is an earlier ordinary-HIR boundary, not a parser rejection. No other backend,
legacy compiler or whole-language acceptance claim follows.

## 4. First candidate admission obstruction

For odd's binding item, `CandidateInference::solve` obtains the carrier,
preflights it, retains the permitted placeholder and continues at
`shadow_apply.rs:89–94`. For the separate final odd expression, the next match
is exactly:

```rust
HirItem::Binding(binding) => binding.value(),
HirItem::Expression(expr) if matches!(expr, ResolvedExpr::Integer { .. }) => expr,
_ => return Err(CandidateError::Unsupported),
```

The final Name matches the last branch (`shadow_apply.rs:97–100`). Therefore
execution does not reach `ConstraintBatch::collect_candidate_mode` at line 110,
`InferenceSession::try_new_candidate` at line 111, or `run_candidate` at line
113. The whole-module preflight rejects before any source action is executed.
This is the decisive localized obstruction at this API, not evidence that
the selected equality produces an incorrect type or that Yulang should reject
the source. Removing the final Name would remove the original required
conclusion; it is not a completion of this packet.

The directly neighboring `CandidateValueObservation::solve` has the same
standalone-integer restriction (`shadow_apply.rs:532–535`) and does not provide
a bypass. No dispatcher outside yu-solver/yu-hir was found in the bounded
`crates/` call-site search for CandidateInference/local-source APIs. That search
does not certify the absence of other compiler entrypoints or establish their
acceptance. Public ordinary HIR and these two private candidate APIs are the
only admission paths characterized here; broader paths remain unverified.

| Required outcome | Evidence at this stop |
| --- | --- |
| Source syntax / HIR | Conditional carrier construction and exact binder/Name map; no exact parser execution or language acceptance theorem |
| Source-to-candidate cut | Unconstructed: the supported complete-result entrypoint rejects final Name before collection |
| Occurrence identity/origin/receiver and joint pairs | Approved mathematical event imported; no candidate extrusion event emitted in this API history |
| Pending k/root, transformed Qc child, admitted relation and bound evidence | Not emitted or consumed on this rejected entrypoint; candidate owners' existence cannot instantiate them |
| Publication/continuation and intrusive preservation | Unconstructed / OPEN; stock theorem and conditional scalar law retain their own scopes |

The static planner inspected during location work does retain an Apply input
(`candidate_source.rs:394–411`, `candidate_call.rs:30–47`) and a source action
continuation (`candidate_source.rs:31–47,611–658`). Those are downstream of the
unreached collection call. They are not a paused candidate session for this
source and do not establish k/Qc, replay or publication.

Wrapping the closed term in `my result = { my odd ...; odd }` would make the
final Name a local body instead of a standalone root expression. It introduces
an additional definition and Block, however. The planner starts a root at
level 1 and adds one for each local initializer
(`candidate_source.rs:254,288–305`): outer odd would then be at 2 and inner
even at 3. No derivation of that different operational history is substituted
for the fixed level-1/2 reference cut.

## 5. Obligation economy and next owner

Earlier scalar/quotient and native-continuation attempts left the same session
construction premise unproved. This pass changes method to actual source/HIR
construction and reaches an earlier entrypoint boundary. It does not add a
reconstruction relation, recalculate solver-row SCCs as Value SCCs, or declare
the parent proved/refuted by an admission limitation.

Faithful original-source admission, continuation and preservation remain A/B.
Occurrence/child/bound certificates already known by their actual constructors
are D when discarded, but classifying them does not prove their existence.
Here no generation owner runs at all through the inspected complete-result
entrypoint. Another scalar proof cannot affect that premise.

One next action: primary adjudication with the source-admission/API owner of
`CandidateInference::solve` to identify or authorize the smallest faithful
entrypoint for the complete displayed module, preserving its final Name and
publication scope. Only after that constructor is grounded should the owning
App-demand/extrusion lane supply k/Qc and actual processing/bound certificates.
This note authorizes no compiler edit, API change or additional source restriction.

## 6. Checks, resources and dependency snapshot

One bounded static pass, within the assigned 30-minute ceiling. Read-only
`rg`, `nl`/`sed`, rule/skill/authority reads, SHA-256 and Git object byte
comparisons; one leased Markdown write. Nineteen direct repository dependencies
byte-match the assigned baseline. No dependency was changed. Some combined
reads truncated; decisive owner windows were reread narrowly. Two malformed
sed locator commands and nonexistent speculative `spec/`/file locators supplied
no evidence and were discarded.

No builds, tests, parser execution, Scala execution, probes, benchmarks,
measurement samples, compiler/expectation edits, Git mutations, questions,
external contact or delegation. At most four lightweight read commands were
submitted concurrently; no heavyweight process. Exact CPU/RAM and reasoning
elapsed time were not measured. Primary retains verification/integration.
Requested settings: normal Sol/high (`gpt-6.1-sol` / high); observed runtime
model/effort: unknown. Prover model/effort pins are absent, configured defaults
are Sol/high, and no override, hot reload or Astra execution is claimed.

| Direct dependency | SHA-256 |
| --- | --- |
| stock core note | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| consumer owner audit | `f4b5dfebe1eff301f248279e4d52a4234e17a6f7d1fb0b904f44b7055dc646cb` |
| conditional continuation note | `f48640f9d393293c2187b9da62b15eb45c9acb94ff382f4d5e092ebebb9d0b0b` |
| parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type occurrence authority | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| local self-recursion authority | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| HIR `module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| HIR `module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| HIR `shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| HIR `lib.rs` | `51e5fa543cd65ced879a7561e0d602e686a072378cde5ec16a20b4afb875fc0a` |
| local-self-recursion fixtures, read only | `4e2b9bc5210358059533cbe3b7fc2202daf64123b77e7333f198eb707eb7b59c` |
| solver `shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| solver `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| solver `candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| solver `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| syntax `root_statement.rs` | `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626` |
| syntax `expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` |

Unverified: exact parse, semantic admission or observational equivalence to
the reference term; other entrypoints/backends; candidate session construction,
approved Value graph/event activation, k/Qc relation, bound evidence, replay,
complete Call/effects, generalization, final output, soundness/principality,
termination, failures and production/cutover. Independent review is pending.

## Commit packet

- Exact changed lease: `notes/theory/2026-10-12-cross-level-pending-call-source-construction.md`.
- Baseline: `39c06498c801e9affa2fc664019ac0bde0cb7bc5`.
- Changed dependency hashes: none; direct snapshot above.
- Claim/review: unreviewed conditional HIR construction and candidate entrypoint
  obstruction; no session, intrusive run or parent theorem closure.
- Checks already run: static source/rule inspection, SHA-256, 19 baseline byte
  comparisons, leased-file whitespace and dependency recheck; zero tests/builds.
- Proposed checkpoint: `research: locate fixed recursive core candidate admission boundary`.
- Shared deltas left for primary/curator: record final standalone Name rejection
  before candidate collection, distinguish conditional cold carrier from ordinary
  HIR/semantic admission, and route the first missing entrypoint to its owner;
  retain k/Qc, occurrence activation, intrusive preservation and parent gates OPEN.
