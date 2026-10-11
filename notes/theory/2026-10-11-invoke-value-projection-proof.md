# `invoke`: current source constructors and the ordinary value projection

Date: 2026-10-11
Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research construction; exact generation identity refuted;
bounded scalar correspondence and mathematical value interpretation derived
Production/API adoption: none

## 1. Frozen objective, scope and claim classes

The assigned claim is that erasing **only effect lanes** from the actual
four-port constraints generated for `my invoke f = f 1` gives exactly the
ordinary reference generation for `λf. f 1`, including its returned value
root and every relevant value-bound/replay case. The reference direction is
`α <: Int → β`, not `Int <: α → β`.

Fix this single, unannotated definition with empty imports, no other source
items, its original definition owner and lexical binder `f`. For every
successful construction of this source at the pinned baseline, names below
denote the owning rows, independent of their numerical ordinals or spelling.
Availability failures produce no successful result. The two actual lowering
entrypoints are distinguished below; neither a hand-built HIR nor a supplied
solver graph is the source premise.

The required exact generation identity is false. Both source routes allocate
a literal value row with two directed bounds and a definition result row.
The newer LocalSource route also allocates a separate Lambda occurrence row.
Deleting effect lanes retains these value rows and their constraints.
This is a representation mismatch, not a counterexample to sound inference
or ordinary source acceptance.

Three narrower claims are derived here: the exact current source seed;
its initial scalar value replay, before any additional source/use/provider;
and a mathematical reduction/coalescing of that value presentation to the
ordinary reference result. The last is an interpretation using the imported
ordinary calculus, not an implemented Yulang coalescer or public scheme.
No complete Call, effects hygiene, Yulang principality, generalization,
later-provider completeness, publication, or production acceptance is claimed.
No `Fam_delta`, `EmittedGenCall0`, ParameterOrigin/receipt/Force/rebind
certificate, selected provider or missing effect assumption is used.

Governing authority is the top-level inference principles §§1–5. The ordinary
base is the independently reviewed [Parreaux import](2026-10-11-parreaux-simple-sub-proof-import.md)
§§2–5, reference commit `9bae772624c23b52a93c1b226157e16898b4d9db`.
The [candidate constructor proof](2026-10-10-candidate-graph-call-correspondence.md)
§§2.2–5 is historical construction evidence; its old effect ports and abbreviated
literal seed are not substituted for the current source reads.

## 2. Actual source map and owning constructors

The opt-in `yu_hir::shadow::lower_module_with_local_source` delegates to
`module.rs:911–921`. Parameter construction at `module.rs:1398–1428` passes
the actual owner-qualified `HirParameterId` to `local_source::form`.
`module/local_source.rs:289–319` introduces that parameter into lexical
lookup before constructing the Lambda body in its parameter scope.
The Apply constructor at `:553–574` retains distinct callee and argument
source indices. This preserves the binder and source incidence; it does not
assign types or certify source Call meaning.

`CandidateInference::solve` (`shadow_apply.rs:74–114`) obtains the actual
carrier and calls `collect_candidate_mode(hir,true,true)`. The branch at
`lib.rs:1126–1141` selects `emit_candidate_source` when LocalSource exists.
At `candidate_source.rs:187–216` every expression obtains value/effect
components, while a formal Name's **used value endpoint** is the original
parameter endpoint. Its separately allocated occurrence value component
has no emitted value relation in this example (`:239–247,368–381`).

Use these names for distinct source-owned value rows:

| Name | Owner |
|---|---|
| `α` | lexical Lambda parameter `f` |
| `s` | integer literal occurrence |
| `β` | Apply result occurrence |
| `L` | outer Lambda value occurrence, on LocalSource route |
| `r` | definition value root |

Effect rows are literal evaluation `ae`, Name evaluation `ce`, Apply
evaluation `re`, Lambda evaluation `le`, fresh invocation `e`, and fresh
Lambda entry/return `p,q`. The latter three are actual allocations, not
certificate objects. The unannotated source creates no annotated formal
domain, so Lambda's value argument is the actual `α-` (`lib.rs:11242–11248`).

The emitted/admitted LocalSource seed is:

```text
Int+ <= s-; s+ <= Int-                       literal slots 0,1
BottomEffect+ <= ae-; ae+ <= EmptyEffect-     literal slots 2,3
BottomEffect+ <= ce-; ce+ <= EmptyEffect-     formal Name slots 1,2
α+ <= Function4-(s+, ae+, e-, β-)            Apply slot 0
ce+ <= re-; e+ <= re-                       Apply slots 1,2
BottomEffect+ <= le-; le+ <= EmptyEffect-     Lambda evaluation
p+ <= q-; re+ <= q-                        Lambda slots 3,4
Function4+(α-, p-, q+, β+) <= L-             Lambda slot 2
L+ <= r-                                  root Link slot 30
```

Literal construction is `candidate_source.rs:336–350`; formal Name lookup
and pure evaluation are `:213–216,368–381`; Apply recipes are `:394–413`.
Actual Apply admission is `shadow_apply.rs:1334–1401,1408–1468`: it constructs
the negative Function, records provenance and actively calls
`constrain_live_value`; separate admissions actively call
`constrain_live_effect`. Lambda collection is `candidate_source.rs:445–459`;
actual Lambda admission at `lib.rs:11267–11362` allocates `p,q`, admits the
two effect relations and positive Function. The definition Link is retained
at `candidate_source.rs:493` and executed at `:665–668` through
`candidate_scheme.rs:1337–1344`. Actions are consumed by the actual source
schedule (`candidate_source.rs:632–675`), not merely stored as recipes.

The older `lower_module_with_shadow_applications` route (`module.rs:898–908`)
has no LocalSource. It follows `emit_candidate_value` and
`emit_candidate_lambda` (`shadow_apply.rs:1086–1178`), constructing the
Lambda directly into `r` instead of `L`. Its literal still emits **both**
value bounds (`lib.rs:1699–1734`). Current shared Lambda admission still
allocates `p,q`. Thus either actual entrypoint falsifies exact effect-only
generation identity; the extra `L` concerns only the LocalSource route.

## 3. Natural erasure and exact mismatch

Define the syntactic value map on actual endpoint shapes, without unfolding
mutable row bounds:

```text
π(ValueRow(v), polarity) = v
π(IntPositive) = π(IntNegative) = Int
π(Function4±(a, ae, re, b)) = π(a) → π(b)
π(value constraint A+ <= B-) = π(A) <= π(B)
effect constraints have no image
```

The polarized endpoint is used in its valid constructor position; this map
does not identify two value rows. It is independent of nominal Term handles
and numerical row ordinals. The two omitted children have effect kind;
Function value children have value kind in both polarities. Current Function
decomposition (`lib.rs:12493–12541`) produces the argument pair reversed
and result pair preserved, exactly ordinary arrow variance after erasure.
This derives the map from constructors, not a new Function denotation.

The LocalSource image is exactly the seed

```text
V = { Int <= s, s <= Int, α <= s → β, α → β <= L, L <= r }
returned/root endpoint: r
```

The reference (`Typer.scala:59–74`) instead returns literal `Int` itself,
binds `f` to fresh `α`, submits `α <= Int → β`, returns Apply variable `β`,
and returns Lambda term `α → β`. Renaming cannot remove `s,L,r`, turn row
`s` into the `Int` constructor, or replace root row `r` by an arrow.
Already the surviving literal pair refutes exact identity. Dropping it or
replacing `s` from its bounds is value elimination in addition to effect
erasure. This refutation does not depend on subsequent solver success.

## 4. Initial scalar replay: actual admission, not a stored-bound assumption

For this single definition all traversed source levels are one
(`candidate_source.rs:253–287`; startup `lib.rs:10045–10104`). All fresh
invocation and Lambda effect rows inherit one. There are no annotations,
operations, local/module uses or recursive definitions in the frozen source.
Consequently there is no annotation view/Allowance, contribution or fresh-use
copy constructor in this source schedule. Extrusion visits rows at or below
the target and retains them (`candidate_extrusion.rs:82–94`); it creates no
younger-row parent. Intrusion has no parents and returns immediately
(`candidate_intrusion.rs:358–374`). This is derived for this source, not a
restriction on ordinary programs or arbitrary continuations.

Scalar admissions pass through the current typed drain, including Transport,
Context and Dispatch (`lib.rs:12154–12173,12197–12311`). Here source contexts
are identity: `candidate_context_source` creates a prefix only for a closed
Allowance (`candidate_context.rs:2488–2494`), absent from this schedule.
Identity replay contexts remain identity (`:2956–2965`) and
`candidate_context_execute_relation` returns without consuming the task
(`:2744–2755`). The Lambda inferred-entry handle is retained provenance;
`candidate_context_seed` records it without changing this identity context
(`:2496–2536`). No typed certificate meaning is inferred from that handle.

Value Dispatch delegates to the actual candidate bound owner
(`lib.rs:13748–13751`; `candidate_extrusion.rs:807–840`). It inserts before
replaying opposite bounds. Replay at `candidate_extrusion.rs:763–803`
constructs a same-kind child task; `candidate_context_begin_replay` enumerates
the retained lower/upper provenance fibers (`candidate_context.rs:2911–2999`),
and `candidate_context_step_replay_child` starts the actual typed drain for
that child (`:3022–3035`). A table of installed bounds alone would omit this
activation bridge.

Up to repeated memoized tasks and reconstructed equal Function shapes, all
initial **value** tasks and resulting bounds are:

| Admission | Installation and complete opposite-bound replay |
|---|---|
| `Int <= s` | insert exact lower `Int` on `s`; no upper yet |
| `s <= Int` | insert exact upper `Int` on `s`; replay `Int <= Int`, terminal |
| `α <= Function4-(s,ae,e,β)` | exact upper on `α`; no lower/provider |
| `Function4+(α,p,q,β) <= L` | exact lower on `L`; no upper yet |
| `L <= r` | equal-level left-row branch inserts upper `r` on `L`; replay that same Function lower against `r`, installing it on `r` |

There is no bound on `β`, no positive Function lower on `α`, and no upper
on `r`. The legacy route skips `L`: the Lambda Function is installed on
`r` directly. A distinct unused formal-Name occurrence value row remains
empty and cannot generate a value task. The constant/constant task has no
row insertion (`candidate_extrusion.rs:819–820`) and compatible `Int`
shapes yield no diagnostic conflict in Dispatch.

This exhausts the initial scalar cases: no value Function/Function pair
occurs, so four-port decomposition cannot introduce further tasks here.
Effect row/row and row/leaf replay stays effect-kind
(`candidate_extrusion.rs:844–876`); the only terminal effect comparison
reachable from these seeds is Bottom against Empty, which succeeds
(`candidate_effect.rs:888–895`). It creates no view or value demand.
Effect conflict replay returns on the empty conflict map (`:659–670`).
Thus deleting effects is safe for this **initial value-task characterization**.
It is not an effect-erasure theorem for other sources or future providers.
Physical pair counts, cause/fiber identities and replay receipts are not
identified with the reference cache.

## 5. Ordinary value reduction and coalescing

Here is a direct mathematical elimination theorem about `V`, not a new solver
or a unification rule. For every assignment of the original `α,β,r` in a
reflexive/transitive subtype preorder with ordinary arrow variance:

```text
(∃s,L. Int <= s ∧ s <= Int ∧ α <= s→β ∧ α→β <= L ∧ L <= r)
  iff
(α <= Int→β ∧ α→β <= r).
```

Forward: `Int <= s` gives `s→β <= Int→β`, hence the required demand;
transitivity through `L` gives the root constraint. Reverse: use the **same**
assignment with `s := Int` and `L := α→β`; all five constraints follow.
Both emitted literal bounds are retained; no equation solver or syntactic
row identification is assumed. Mutual subtyping gives `s ≈ Int` in the
preorder quotient. The existential witnesses here eliminate internal value
wrappers; they are not independent Call/provider witnesses.

The remaining `α→β <= r` is precisely an upper observation of the
reference's returned term. The returned Yulang row itself is still `r`;
the theorem does not assert runtime replacement of it by that term.

Alternatively apply the **ordinary** Fig.11/reference coalescing definition
to the complete initial projected bound table in §4. Its positive root is

```text
C_raw = r ∨ ((α ∩ ((s ∨ Int) → β)) → β).
```

Positive `r` reads its installed Function lower; negative `α` reads its
negative Function upper; that arrow's argument reads `s` positively and its
result reads `β` negatively. The outer result reads the **same** `β`
positively. The intermediate `L` is not a lower on `r`: its actual replay
installed the Function itself. The literal's `s <= Int` upper remains in
the store, although ordinary positive coalescing reads its lower list.
No recursive binder is introduced in this acyclic value dependency trace.

Let `D=(Int→β)→β`. In the paper's scheme order `P <=∀ Q` iff some free-type
substitution makes `P <= Q`, the ordinary closure of `C_raw` is equivalent
to that of `D`:

1. `C_raw <=∀ D`: substitute the coalesced free variables
   `r:=⊥, α:=⊤, s:=⊥`, keeping `β` unchanged.
2. `D <=∀ C_raw`: since `Int <= s∨Int`, arrow contravariance gives
   `(s∨Int)→β <= Int→β`; therefore
   `α∩((s∨Int)→β) <= Int→β`. Contravariance of the outer arrow gives
   `D <= (α∩((s∨Int)→β))→β <= C_raw`.

These substitutions concern the free variables **after ordinary coalescing**;
they are not assignments to mutable source rows that must satisfy `V`.
The reference's `C_ref=(α∩(Int→β))→β` is similarly equivalent to `D`, as
established in the imported base. Thus the ordinary coalesced mathematical
result follows for this initial value projection. There is no implemented
public Yulang scheme here and no application of Parreaux's universal
principality theorem to the four-port compiler.

## 6. Economy audit, limits and cost

Exact physical generation equality is a C characterization; failure of it
is not an A/B inference defect. Treating administrative value rows as unknown
source syntax and reconstructing them later would create D debt: their
owners already know the literal, binder, body and definition link. The
construction above needs only native bounds and actual scalar replay.
No retained source certificate, extra semantic relation, source restriction
or production redesign is proposed. Two approaches were used: direct
constructor/replay case analysis and mathematical elimination/coalescing.
Neither is presented as closure of the original parent theorem.

For this fixed source, erasure/elimination is a constant-size mathematical
calculation, with no compiler traversal or allocation introduced. General
shape erasure would cost the visited value DAG size with sharing retained;
this note proposes no runtime implementation and proves no general solver
complexity bound.

Unverified scope includes other source programs, later providers/callers,
cross-level extrusion, qualifying parent/copy intrusion, annotations,
nonidentity contexts, resumed/failing routes, graph capture/freshening,
full Call, effects hygiene, SCC generalization, production output and full
soundness/principality. Actual broader consumers can mix effect and value
work; the initial trace's lack of such work cannot be generalized.
Independent review is pending; the producer does not certify these claims.

Next action: independently review this frozen source/initial-replay bridge
and its mathematical interpretation, then apply only its scoped result to
the primary's complete-Call/extended-constrain parent obligations.

## 7. Checks, dependency snapshot and commit packet

Checks: read-only `rg`/`sed` source inspection, current and reference
`git rev-parse`, pinned `git show` versus working-byte comparisons and
SHA256 hashes. All direct dependencies matched the pinned Yulang baseline;
reference HEAD matched its assigned commit. A final artifact check passed
trailing-whitespace and fence-balance checks. Its first HEAD-equality assertion
failed because primary-owned HEAD advanced to
`1a3330cec82f51c4c588e4204264bd83a85947b4`; revalidation found every direct
dependency unchanged in both HEAD and the working tree against the assigned
baseline. Lease-scoped `git diff --check` returned zero but did not inspect
this untracked file; the direct artifact check supplied that coverage.
No Cargo, Scala, tests, probes,
performance measurements or Git mutations ran. One leaf, no descendants,
lightweight commands, within the 30-minute wall envelope. Requested runtime:
`gpt-6.1-sol/high`; observed model/effort metadata unavailable, **unknown**.
No Astra request. The only changed path is the exact leased note.

Frozen SHA256 dependencies:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  top-level principles
cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113  Parreaux import
56cc8d4d2d0260ffa01a3198a051a6da384f84ceaad209d8886d8c6504497018  candidate graph correspondence
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  candidate_source.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  yu-solver/src/lib.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  candidate_extrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  candidate_context.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  candidate_effect.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  candidate_scheme.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference Typer.scala
```

Commit packet:

- Exact lease: `notes/theory/2026-10-11-invoke-value-projection-proof.md`.
- Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`; changed dependency
  hashes: none at the snapshot check.
- Review: pending fresh independent review; research-only; no parent closure.
- Checks already run: static owner/consumer reads, pinned-byte/hash checks,
  HEAD dependency revalidation, direct whitespace/fence checks;
  no executable compiler verification.
- Proposed checkpoint message: `research: derive invoke ordinary value projection from current constructors`.
- Shared-record deltas for primary/curator: record exact erasure identity as
  refuted, preserve the source-derived value quotient/initial-replay result,
  and retain complete Call, effects, source-Generalize and inference gates
  OPEN. Correct historical literal/effect summaries when consumed; no shared
  record was edited by this leaf.
