# Frozen Oracle: one application separates source, expected owner and endpoint

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed research-only characterization; one minor export qualification repaired
Claim class: conditional internal representation witness; no language counterexample
Current baseline: `601c80804e02924d90ac502e794b8b94d66223f1`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Semantic/implementation authority: none
Review: compiler_referee PASS on content SHA-256 `8cee055e195a77114e7536fb191ff53274649574ffc6afa9cae84b679069c136`; one minor empty-export qualification repaired by primary; scope covers the constructor witness, owner/port distinctions, ordering, and current-authority boundary

## Objective, governing premise and result

Test the candidate shortcut that an application `ExprId` and its old typed
endpoints directly supply the current original slot/contribution association.
One ordinary application already separates three coordinates: its source-owned
App identity, its argument's expected-type owner, and a callee Function-demand
constraint. Their identity is false in the inspected constructor. Whether a
later explicitly justified join relates them is a separate question left open.

The current obligation is
`OriginalAssocType_X(beta,p0,j_call;s0,c0)` in
[Attach-law construction](2026-10-06-attach-law-construction-attempt.md) §§3–5.
That judgment must provide original contribution typing and slot association
on the same whole row X. The separate original-footprint clause in
[main source-generation](2026-10-06-main-source-generation-minimal-clause.md)
§6 requires original typed positions/contributions, static owners/receipts and
complete profile inventory. These research notes locate an open premise; they
do not create semantic authority. The underlying
[call-view authority](../design/2026-10-05-inferred-function-call-views.md)
§§2–5 requires one shared source relation, stable original identities and
comparison-independent formation. The primary's accepted same-row and
non-Oracle-authority decisions are retained. This note selects no new meaning
for the unannotated formal or the nested block.

The falsified candidate is **direct key/coordinate identity**, not every
possible historical-to-current correspondence. A useful candidate bridge may
instead retain the App, argument, boundary origin, constraint root and a
justified typed projection together. The historical constructor alone does
not discharge the current original `(s0,c0)` premise.

## Smallest conditional witness

All historical paths below are relative to the pinned Oracle checkout.
Use one ordinary source call `f x`, with two already lowered ordinary name
expressions. This is a source-constructor witness, not an executed source
acceptance or inferred-type observation.

Hypotheses:

1. Callee and argument lowering have returned valid `Computation` values
   `F=(e_f,v_f,epsilon_f,...)` and `A=(e_x,v_x,epsilon_x,...)`, with distinct
   existing expression IDs `e_f` and `e_x` in one well-formed arena.
2. `apply_arguments` reaches the ordinary nonempty-argument branch and
   invokes `make_source_app(F,A,...)`; construction returns normally.
3. The arena has representable IDs, so append allocation does not wrap its
   `u32` index. Available module/source ranges allow the source App provenance
   insertion. No solved type, accepted provider, profile or whole row is assumed.
4. For a nonempty root witness, the post-submission
   `constraint_record_id(callee_lower,empty,callee_upper)` lookup returns `r`.
   This hypothesis is unnecessary for the expression-owner distinction;
   without it the same expected key is registered with no roots and marked
   incomplete.

The constructor trace is:

| Coordinate | Exact construction | What it identifies |
| --- | --- | --- |
| Boundary/origin | `make_source_app` allocates an ApplicationArgument boundary `b`, passes its origin to `make_app_with_origin` (`tail.rs:630–642`) | Source boundary for the callee-demand constraint; not an App or typed slot ID |
| Demand endpoints | `make_app_with_origins` allocates result value/effect and call effect; builds `callee_lower=Pos::Var(v_f)` and `callee_upper=Neg::Fun { arg: Pos::Var(v_x), arg_eff: Pos::Var(epsilon_x), ret_eff: return_effect.upper, ret: Neg::Var(result_value) }` (`tail.rs:543–563`) | A whole four-port demand on the callee, not the argument's value endpoint alone |
| Expected-owner key | After subtype submission, register `(Expression(e_x),ExpressionExpected,[])` with `[Constraint(r)]` when r exists (`tail.rs:564–587`) | **Argument** expression as expected-type owner; neither callee nor application as owner |
| App/result | Later append `e_app = App(e_f,e_x)` and return `Computation(e_app,result_value,result_effect,Computation)` (`tail.rs:615–627`) | The application's computed output endpoints |
| Source App key | Insert ApplicationProvenance at `e_app` with module, application span and callee span (`tail.rs:643–669`) | Source application identity and location, not a typed profile |
| Boundary span record | With an argument range, separately insert application/callee/argument spans at `b` (`tail.rs:671–689`) | A potential source join channel, not an original typed contribution |

`poly::Arena::add_expr` appends at the current vector length
(`crates/poly/src/expr.rs:239–242`). Under hypotheses 1–3, both operands
already exist when App is appended, hence

```text
e_app != e_x
e_app != e_f

ApplicationProvenanceTable key = e_app
expected occurrence key = (Expression(e_x), ExpressionExpected, [])
expected root = Constraint(r), with r addressing v_f <: Fun(v_x,...,result_value)
returned output interface = (result_value,result_effect)
```

The expected occurrence's empty path is the default vector path
(`crates/poly/src/provenance.rs:24–25`), not a statement that the constraint's
Function argument child is the current original effect-observation slot.
`TypeOccurrenceKey` explicitly separates owner, role and path
(`provenance.rs:69–92`). Erasing the role/path or replacing the owner with
`e_app` therefore changes the registered coordinate even for this one call.
The root is the submitted **callee** comparison; its registered owner is
the **argument**; the source provenance key is the **application**. All three
are present in one lowering invocation, so this witness requires no mixing of
different executions or independent endpoint choices.

Removing the application removes this expected-owner registration and source
App allocation. No second call, annotation, recursive definition, generated
wrapper, Function child-derivation label or receiver-signature elaboration is
needed. Minimality is one-call local constructor minimality; no exhaustive
minimum over all syntax or compiler paths is claimed.

## Ordering, retention and failure conditions

The boundary/origin is allocated before subtype submission. The expected-owner
record is registered **after** `infer.subtype` returns, before App allocation;
App source spans are registered after `make_app_with_origin` returns.
`constraints/machine/entry.rs:493–499` shows that `subtype` enqueues the root
and calls `drain()` when it admitted work or the queue is nonempty. Thus the
expected-owner record is lowering-time post-submission evidence and may follow
local propagation. It is not an untouched pre-solve atomic declaration, a
post-global-solve typed contract, or evidence of independent whole-row admission.
The root lookup itself is an optional lookup in canonical constraint storage
(`entry.rs:1718–1725`); no runtime observation of its success was made.

`register_type_occurrence_roots` stores pending roots, deduplicates them and
marks empty roots incomplete (`analysis/session/occurrence_provenance.rs:38–69`).
The later sidecar builder merges pending entries and exports root anchors while
preserving the owner/role/path key with a calculated completeness status only
when the aggregate root list is nonempty (`occurrence_provenance.rs:71–122,
156–193`). An empty aggregate returns `SubtypeProvenanceSidecar::empty()`
(`:116–118`), so an incomplete pending entry with no roots need not appear in
the exported sidecar. This is a retained provenance channel under that
nonempty-root condition. This bounded trace does not prove absence of a later
projection, source join, alias recovery or semantic reconstruction elsewhere.

The App enum retains just its two expression children, while the lowering
`Computation` carries transient value/effect endpoints. The inspected
`Typing` table is DefId-keyed (`crates/infer/src/typing.rs:1–5,14–24,106–129`);
the App definition stores no endpoints (`crates/poly/src/expr.rs:472–482`).
These schemas confirm why source identity, temporary interface and provenance
coordinates must be distinguished. They do not establish that all old typing
information is unrecoverable from constraints, RefIds, schemes or other tables.

Discriminating logical mutations, not executed tests:

- Replace `Expression(e_x)` with `Expression(e_app)`: changes expected-owner
  identity. This is not the historical record established by the constructor.
- Replace the constraint root with the argument's `v_x`: loses the distinct
  whole callee-demand root and its return/effect ports.
- Identify the returned `(result_value,result_effect)` with an original
  signature slot/contribution: assumes an additional interpretation and typing
  law that this constructor does not state.
- Treat registration as strictly prior to solving: contradicted by synchronous
  subtype drain before the root lookup.
- Infer that the distinct keys forbid any later join: exceeds this witness.

The nonempty root part fails if lookup returns None. Normal source App insertion
fails if the required application/callee span conversion returns None.
Exceptional lowering, unsupported arena overflow, generated internal calls,
empty argument syntax and extra annotation/projection steps are outside this
witness. Distinct IDs may later have equal semantic endpoint solutions; no
endpoint inequality or source rejection follows from distinct identity sorts.

## Current implication, independence and omitted scope

Direct substitution of old App/result coordinates for current
`(beta,s0,p0,c0)` is unsupported. A bridge based on these historical coordinates needs a source-derived
join and a contribution-typing interpretation that distinguish the argument
expected owner, callee four-port demand and application output, on the same
original X with its source scope and profile. The presence of one historical
constraint record gives neither a completed original profile nor both
`Attach_C`/`Lic_C` directions. Same-invocation evidence in this witness is
weaker than an admitted current whole row with correlated `nu,K,D`.

The method is independent source reading of the frozen implementation, rather
than a checker implementing supplied transition assumptions. It independently
checks the narrow historical constructor claim; it cannot validate current
source rules because Oracle semantics and acceptance are non-authoritative.
Shared assumptions are the pinned bytes, normal routine completion and valid
arena/source inputs. No oracle execution, independent mathematical review or
current source-adequacy theorem is claimed.

Seeds, ranges, executable mutation counts and performance samples are
inapplicable. Search was restricted to the seven historical files below and
the named current governing inputs; several locator searches also examined
four neighboring expression-lowering files and `compiled_typed.rs`. Initial
aggregate task/index/file-list output truncated; decisive constructor, subtype,
key and registration windows were reread in bounded captures. No broad absence
or complete-call inventory claim rests on those searches. The sole incorrect
guessed main-source note pathname was resolved through `rg --files` before use.

## Dependency snapshot and checks

At initial evidence verification, both HEADs matched their assigned pins and
all thirteen direct dependency files equaled `git show <pin>:<path>` bytes.
The table records Git blob IDs, which are sufficient to reconstruct that
snapshot. SHA-256 was additionally calculated in the read-only Python check.

| Repository | Direct dependency | Pinned blob |
| --- | --- | --- |
| Current | `rules/research-lab.md` | `69860b70bc96a5a60bab3bf9ec667ea25bc6578c` |
| Current | `rules/design-authority.md` | `466da7e03855d3f5dd7f2b5dc438cccc9b1c76d8` |
| Current | `rules/git-concurrency.md` | `a55f967648dc057e111d56b2e6556d05c1edcfe3` |
| Current | Attach-law note linked above | `415e92ddc37d4e6cec6f3813516770f4cba309e2` |
| Current | Main-source-generation note linked above | `457c924b807540685b24b656425c99e9dbe4fdee` |
| Current | Call-view authority linked above | `9493abd55e61dbc59de31f319c2ff9670204069a` |
| Oracle | `crates/infer/src/typing.rs` | `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` |
| Oracle | `crates/infer/src/lowering/application_provenance.rs` | `a6c5f255ceed263e6266d2eaf1d3b04e4b984474` |
| Oracle | `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| Oracle | `crates/infer/src/constraints/machine/entry.rs` | `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b` |
| Oracle | `crates/infer/src/analysis/session/occurrence_provenance.rs` | `6a3e4da511d8c2f6f512f2c22b6112ecda6076c8` |
| Oracle | `crates/poly/src/expr.rs` | `4cd13e8b9d71b63f768d4a5739a264b5a3b76c1e` |
| Oracle | `crates/poly/src/provenance.rs` | `0980898542588402426b80cca421a5299fd75867` |

Commands used: read-only `git rev-parse HEAD`, `git status --short`,
`git show <pin>:<path>`, `git rev-parse <pin>:<path>`, `git ls-tree`, bounded
`rg -n`, `rg --files`, `sed -n`, `cat`, and an in-memory `python3 -` byte/hash
comparison. Final checks repeat the thirteen-file pin/byte comparison and
run `git diff --no-index --check /dev/null <leased-note>` plus local relative
link checks. No build, tests, Oracle execution, compiler/manifest edits, Git
mutation, child delegation, broad formatting or scratch output was performed.

Assigned resource envelope: one light process, 15-minute wall cap and one
leased output. A deviation occurred: independent bounded read-only tool calls
were batched up to five concurrently; observed command durations were below
one second. No build, executable probe or heavyweight process ran. Final checks
are serial. Peak RSS and total CPU were not instrumented; no numeric RAM/CPU
limit was supplied. Work stops after this
single discriminator. Unverified scope includes downstream joins, complete
source semantics, original slot/contribution typing, profiles, independent
admission, licensing, principality and production conformance.

Recommended next action: audit a proposed historical bridge against this
App/argument/demand-root distinction and require an independent original
association interpretation before using it to discharge `(s0,c0)` typing.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-frozen-oracle-application-endpoint-falsification.md`.
- Baseline SHA: `601c80804e02924d90ac502e794b8b94d66223f1`.
- Oracle dependency SHA: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none at initial and final thirteen-file checks.
- Review status: compiler-referee reviewed; the empty-sidecar qualification
  was repaired. No current theorem closure or authority is claimed.
- Checks already run: both HEAD pins; thirteen dependency byte/blob/SHA-256
  checks; exact constructor/key/subtype/registration source reads; leased-path
  absence before creation; note whitespace and relative-link checks.
- Proposed research-checkpoint commit message:
  `research: separate Oracle application and expected-owner coordinates`.
- Shared-record deltas intentionally left for primary/curator: optionally
  register this narrow key-sort witness beside the open original association
  clause; retain downstream-join, profile/admission and licensing gates. No
  task/index/authority/question change or theorem-status promotion proposed.

Research writing stops before submission for independent frozen review.
