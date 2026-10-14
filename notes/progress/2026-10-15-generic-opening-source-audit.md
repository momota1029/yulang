# Generic operation-arm opening: pinned source audit

Date: 2026-10-15
Status: frozen, unreviewed research checkpoint; bounded static source characterization
Role/method: researcher; declaration/HIR/native-constructor coverage and falsifier audit
Baseline: `research/simple-sub-intrusion`, `871d2ecb559f064dc034501b8bfe8c9bd6659876`
Exclusive lease: this file only
Authority: redesign charter §§19–20; operation-instance binding package §§2–4,7–9;
top-level inference principles. The package is Draft and grants no implementation
authority; the charter's selected user decisions govern their stated scope.

## Result and exact premise

The committed native candidate has a generic **operation-use** constructor, but
its admitted operation-arm domain is monomorphic. The actual `echo` arm fixture
is stopped before constraint collection by `monomorphic_signature`. Consequently
this audit finds neither an admitted generic arm judgment using caller-private
`s=Int` nor an admitted generic arm judgment preserving a rigid opening. The
precise missing source/native constructor is the operation-arm opening that
checks one body/consumer template under the declared local binder while
retaining its correspondence to the request witness. This is a coverage gap,
not a contradiction to the selected source meaning.

Hypotheses of that bounded statement: entry is the committed
`CandidateInference::solve`; a successfully formed LocalSource has a resolved
operation declaration whose signature contains `SourceAnnotationValue::Variable`;
the inspected preflight is used without bypass. Under those hypotheses,
`shadow_apply.rs:191–228` preflights source before `collect_candidate_mode` and
session creation, and `candidate_source.rs:119–130,178–184` returns Unsupported.
No claim is made about direct internal invocation of private constructors,
legacy inference, future implementations, or overall source rejection.

## Minimized actual positive discriminator: echo

The smallest existing committed arm fixture relevant here is
`crates/yu-solver/tests/candidate_operation_catch.rs:74–85`:

```yulang
act echo:
    our send: 'a -> 'a

my result = catch echo::send 1 { echo::send(x), k -> k x, v -> v }
```

This file contains a real parse/lower/solve test contract, including healthy
parse and successful HIR lowering assertions, followed by the expectation
`Err(CandidateError::Unsupported)`. The test was **read, not run** in this audit.
It is stronger source evidence than an invented transition model, but its
written assertions are not a new observed execution result.

The minimized constructor trace at the frozen source owners is:

1. `module/source_annotation.rs:215–304` builds a declaration Arc with actual
   family/declaration SourceNodeKeys, visibility, signature position and the
   complete parsed signature. `parse_type:401–432` retains each `'a` occurrence
   as `Variable("'a")`. The family header is nullary: its SourceEffectId has no
   family type tuple. Thus this example's `'a` belongs to the operation-local
   declaration signature, independently of which concrete call is observed.
   No explicit binder-ownership/quantifier record is carried by this HIR struct.
2. `module/local_source.rs:677–708,798–810` resolves the call's `echo::send`
   to that declaration; the call is `Apply(Operation, Integer(1))`.
   `catch:827–895` independently resolves the arm's operation to the declaration
   and forms an Operation pattern with payload binder ordinal 0 and continuation
   binder ordinal 1. Their identities include the definition owner and arm
   SourceNodeKey. `Work::CatchArm:426–431` installs lexical resolutions for
   `x,k`; the body `k x` is an ordinary Apply of those CatchBinder names.
   These are value binders, not a retained existential type opening.
3. `CandidateInference::solve` calls source preflight for every binding before
   collection. The occurrence of `Variable` in the argument/result makes
   `monomorphic_signature` false. No CatchOperation action or native arm-body
   constraints are admitted on this entry path for this fixture.

Operation-instance §9 makes `k x` the uniform payload/response correspondence
discriminator, with one rigid checking name in both places. It does not claim
complete handler acceptance or an executed Oracle fixture. The committed test
therefore identifies a concrete positive construction seam still unavailable;
it cannot establish completeness or an authority violation by itself.

## Caller-specialization falsifier: sink

Charter §19 explicitly rejects the complete `sink::put : 'a -> ()` handler
containing `my checked: int = x`, even with only Int callers. That source text
is a user-selected semantic discriminator. It is **not** an observed compiler
failure or success. No corresponding fixture was found in the bounded searches
of `crates`, `lib`, and `spec`; this is not an exhaustive repository search.
In particular, this audit did not parse its bare payload-pattern spelling or
produce its HIR, and does not assert that the exact charter text reaches native
preflight. If it reaches LocalSource with the stated resolved generic signature,
the same preflight argument excludes it before native arm checking.

The minimal falsifying judgment would have all of the following evidence:

- an authentic, admitted handler arm for unconstrained operation-local `'a`;
- a real payload consumer generated by `checked:int=x`;
- a private operation-use witness `s` constrained by the caller to Int;
- successful justification of that consumer using the private constraint as
  an arm assumption about the fresh rigid opening `kappa`.

That would violate §§19–20. Merely seeing Int at the request, satisfying
ReachSel => OpCompat for Int callers, or seeing an ordinary flexible variable
unify with Int does not demonstrate a generic arm derivation. The ordinary
consumer demand need not be encoded as literal equality `kappa=Int`.
Unsupported is also not evidence of proper uniform rejection.

## Actual native constructors and the same-witness limit

| Owner | Retained or constructed at this baseline | Exact limit |
|---|---|---|
| `candidate_effect.rs:785–805`, `candidate_operation` | One shared value/effect/view map for a resolved signature use; signature construction at `level+1` links the result to the operation value endpoint | Operation use is admitted independently of arm availability; no generic arm proof follows |
| `candidate_effect.rs:1422–1513`, signature value | Operation-local spelling lookup creates one fresh value row and reuses it for all occurrences, including A and B; Function ports are constructed jointly | Fresh row allocation is flexible inference construction, not the selected rigid existential elimination |
| `candidate_effect.rs:1517–1605`, signature effect | Outer operation family is injected only at the outer signature result interface; named effect variables reuse their map | Operation origin retains declaration/occurrence; this is not proof of a complete request witness package or joint K,D disposition |
| `candidate_source.rs:324–329,399–445` | A representative endpoint for each used lexical CatchBinder; CatchOperation action retains declaration, owner, occurrence, payload/continuation positions, original scrutinee endpoint and effect | Generic signatures are excluded before this action is used by solve; arm fields do not name an actual request's local substitution |
| `candidate_effect.rs:806–866`, catch operation | One shared environment constructs paired A ports and paired B response ports. Raw k accepts B, returns the original scrutinee V; fresh E/R obey E<=R and S<=R | It is a provisional monomorphic constructor using conservative full-S; it is not a request-linked generic opening, exact J, full Call, or K,D bridge |
| `candidate_source.rs:340–350,564–580` | CatchBinder names reuse their representative; local aliases take the ordinary local-use route | These lexical identities alone do not prove binder retention through generic alias generalization or resumption |

`candidate_operation_source.rs:59–76` contains a separate actual source fixture
with a generalized operation alias used at Unit and Int, expecting independent
value instances. That is about separately typed uses of a generalized value;
it does not license two witnesses for aliases of one monomorphic request.
`candidate_operation_catch.rs:89–125` contains direct/aliased/repeated raw
resumption and payload-alias contracts for monomorphic declarations. Those
contracts were read without execution. They exercise concrete interfaces and
response-entry effects, not operation-local existential identity.

The maps are dropped after type graph construction. This observation alone
does not prove that type-variable sharing was erased: allocated row identities
can retain sharing in the graph. Conversely, shared signature maps, declaration
Arcs, identical family IDs and repeated value-binder IDs do not prove that
payload Atheta, response Btheta, dependent J, profiles and K,D all belong to one
original request witness after alias/raw-resumption transport. No such generic
request/arm consumer is reached by the inspected entry route. No whole-native
graph search or lifecycle theorem was attempted.

The joint-correspondence falsifier would be an actual admitted request whose
dependent payload, response, J, profile or K,D fields are rebound to different
local substitutions through an alias or resumption. Its necessary evidence
includes the original use witness, each dependent incidence and the actual
consumer/transport route; independent per-field compatible assignments do not
meet that criterion. No such witness was observed here.

## Evidence, independence, exclusions and resources

This is a bounded static characterization grounded in committed source and
existing committed fixture text. The source authority and compiler code are
distinct inputs; no synthetic checker or assumed transition system supplies
an oracle. It shares the selected charter/package assumptions with the
constructive lane and does not independently certify that lane's derivation.
No executable oracle, random seeds/ranges, mutation, probe, build, test,
benchmark or measurement was used. No substitutions of a new rule or proposed
production implementation were made.

Commands: read-only `git show <baseline>:<path>` with narrow `sed`/`rg` locators;
`git grep` bounded to named owning trees; `git rev-parse`, `git branch`,
`git status`; Python SHA-256 of committed dependency bytes and byte equality
comparison with working files. The output lease did not exist before writing.
All compiler interpretation used committed bytes. Working candidate_source.rs
and candidate_effect.rs differed and were deliberately not interpreted; other
listed direct dependency working files matched. HEAD was the assigned SHA at
the initial and final checks. Static note integrity checked balanced code
fences, absence of trailing whitespace and a final newline. No Git mutation
occurred.

Inspected compiler intervals are listed above; fixture files were read in full.
Inspected policy: AGENTS, design authority, research lab, Git concurrency,
compiler engineering, orchestration and researcher/prover contracts; skill:
yulang-proofs. Design INDEX used as locator; no index summary promoted to a rule.
The task records were inspected at the relevant operation-Catch/handoff sections.
Omitted: legacy inference implementation, parser execution, whole HIR/native
source coverage, source declarations with family parameters, generic callbacks
and local effect binders beyond the signature map, replay/intrusion/extrusion,
generalization/lifecycle, diagnostics and production routes. No conclusion
about those paths follows. Full checking completeness, lifecycle, principality,
soundness, full Call and implementation remain OPEN.

Budget: one static leaf within its 15-minute allocation; zero build/test/probe
processes, zero measurement samples. Read/hash shell processes
ran sequentially within each source read; peak CPU/RAM were not measured.
This note is frozen before submission and makes no independent-review claim.

Recommended next action: give the constructive lane the authentic
`echo` HIR arm/call seam and the absent generic arm-opening owner, so its proof
can identify exactly how the independently declared checking template connects
to the original request substitution and all dependent consumers. Keep the
generic implementation and parent proof gates OPEN pending that bridge.

## Frozen direct dependency hashes (SHA-256)

```text
461780f1574b83aacf86921997927e01794169b848835636cf9a2c8f3e9019c1 notes/design/INDEX.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9 notes/design/2026-10-02-operation-instance-binding-package.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38 crates/yu-hir/src/module/source_annotation.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
a5fe26b4c5423468826842a618c8647af1d94a9ef135d18607999262977ead1a crates/yu-solver/src/candidate_source.rs
f4a8cb624204ae8afd4f2ab599048e71efc5022724130161d390058a09997d9d crates/yu-solver/src/candidate_effect.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831 crates/yu-solver/src/shadow_apply.rs
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484 crates/yu-solver/tests/candidate_operation_catch.rs
7e438b91ed03dbb52b644f78bc082232efd5164fd8d095d10373d826d2d7d0cb crates/yu-solver/tests/candidate_operation_source.rs
```

## Commit packet

- Exact path: `notes/progress/2026-10-15-generic-opening-source-audit.md`.
- Baseline: `871d2ecb559f064dc034501b8bfe8c9bd6659876`.
- Dependency hash changes by this leaf: none. Concurrent working edits to two
  native dependencies are outside the audited frozen baseline; primary must
  revalidate any later applicability.
- Claim/review: bounded static source characterization; frozen; unreviewed;
  no theorem closure or implementation authority.
- Checks already run: committed-source locator inspection, bounded fixture
  search, eleven SHA-256 dependency hashes and baseline/working comparison,
  note fence/whitespace/final-newline integrity;
  no builds/tests/probes/measurements.
- Proposed commit: `research: audit generic operation-arm opening source seam`.
- Shared deltas left to primary/curator: record native generic-arm construction
  as unavailable at this baseline, link the authentic echo source seam and
  unexecuted sink discriminator, and retain all original parent gates OPEN in
  tasks/current.md, tasks/research-lab.md and any governing theory map. No shared
  record, authority, question-board bundle or compiler file was changed here.
