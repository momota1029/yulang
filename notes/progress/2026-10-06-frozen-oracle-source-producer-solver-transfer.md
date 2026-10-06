# Frozen Oracle: positive return push and matching frame-pop replay

Date: 2026-10-06
Status: frozen research-only bounded characterization and conditional local derivation; independent review pending
Yulang3 baseline: `c647dc0062c09cc094020757dc0b3afed58b025e`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Historical checkout: `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, dependencies, and result

Trace a remaining solver seam after the already characterized ordinary-name
effect prefix and negative Function demand. The prior
[solver-mechanism note](2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md)
already identifies the literal `Neg::Bot` argument-effect branch and negative
`Empty`-push erasure. Repeating those rules would not resolve its open premise.
This continuation instead follows the **positive** return push into bounds and
the frame's matching output pop into replay composition.

Current governing sections remain
[inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, particularly §3, and the
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. The selected internal protected seed and ordinary-value refinement on
one shared inferred relation, distinct actual provider roles/entries, and exact
returned captured-step interpretation are retained. Historical fields and
constraint weights supply no new current meaning.

**Result:** the eligible unannotated call produces a left weight with one
`Empty` push on its call-effect-to-result-effect edge. The selected Defined
frame records a pop with the same subtraction ID; its lambda wrapper puts
that pop on both positive output ports. If the wrapped effect port is compared
to a sink and the relevant bound pair is replayed, composition cancels the
matching push followed by pop. An unmatched pop or reversed order produces
different weight fields. This cancellation does not inspect the ordinary
argument's empty-row upper or evaluation tag. Its additional premise is
consumption of the particular wrapped output and successful replay; it is not
an unconditional transformation triggered by ordinary-value evidence alone.

Read dependencies are the prior producer continuation, solver-mechanism note,
multi-use continuation, main Oracle crosswalk, minimal-clause §5, and the two
governing designs. Ten historical files and these seven current dependencies
matched their pinned blobs byte-for-byte; hashes are below.

## Hypotheses and claim class

H1: inspected bytes equal the exact historical/current blobs. Verified.

H2: the already described ordinary name/application route reaches an eligible
unannotated direct formal call and selects a Defined frame. Write `epsilon`
for the supplied argument effect, `rho` for the fresh call effect, `b` for the
application result effect, and `s` for that frame/formal's subtraction ID.
For the isolated ordinary-effect prefix, `epsilon` starts fresh without other
bounds or aliases. This is a conditional lowerer-state premise, not proof of
surface acceptance.

H3: the chosen Defined frame is wrapped successfully, its collected predicate
contains the single relevant `pop(s)`, and the body effect under consideration
is `b`. A comparison later consumes that wrapper's positive return-effect port
against `Neg::Var(eta)`, with empty incoming weights. `rho`, `b`, and `eta`
are distinct, at compatible levels, with no competing aliases, registered
filters, or extra weights on this isolated path. This explicitly supplied
comparison is not synthesized by the ordinary-name prefix itself. In the exact
nested source, the frame selector can place `s` on an outer frame; H3 does not
claim that the inner application effect directly occupies that outer output.

H4: projected lower/upper bounds for the stated path are admitted and their
proof pair is replayed. Drain completes without terminal proof/resource
failure. No subsumption, duplicate/evidence-only routing, or unrelated queued
work prevents the stated path from being materialized. Computing a replay key
requires less than this hypothesis; asserting a new stored edge requires it.

Established facts: H1 and the cited field operations/branch predicates.
Bounded characterization: this producer-to-consumer path. Conditional local
derivation: matching-ID cancellation under H2–H4. H2–H4 are candidate state
premises, not established accepted-program coverage. No semantic theorem,
global absence result, current source-rule closure, or production conformance
is claimed. The producer does not independently review this artifact.

## Source producer and consumers

All following paths are relative to the historical checkout.

1. `crates/infer/src/lowering/expr/constraints.rs:7–28` emits
   `Bot <: epsilon <: Row([],Top)` with the appropriate positive/negative
   polarity. Canonicalization drops the literal bottom root
   (`constraints/machine/entry.rs:1092–1117`); empty-row upper insertion uses
   `row_effect.rs:88–117,236–244`. Under the isolated fresh-state premise,
   `epsilon` has that upper and no explicit bottom lower. This retained prefix
   is not a literal replacement of `epsilon` by `Bot`.
2. `lowering/expr/tail.rs:543–563` inserts the demand
   `Neg::Fun(arg=Pos::Var(A_x),arg_eff=Pos::Var(epsilon),ret_eff=R,ret=Neg::Var(V))`
   above the shared `Pos::Var(A_f)`. The argument effect is a demand port.
   That routine passes only the callee and `rho` to the return-view helper;
   no argument evaluation tag is passed (`:552,740–744`).
3. The eligible helper allocates/reuses `s`, declares `(rho,s,Empty)` on first
   creation, records `pop(s)` in the selected frame, and constructs both
   `R=Neg::Stack(Neg::Var(rho),push(s,Empty))` and
   `L=Pos::Stack(Pos::Var(rho),push(s,Empty))` (`tail.rs:769–798`). The frame
   selection/guard mechanism is an existing dependency, not re-derived here.
4. `tail.rs:615–623` separately submits `callee.effect <: b` and `L <: b`.
   The positive stack is consumed by
   `constraints/machine/propagate.rs:11–24`: its inner endpoint remains
   `Pos::Var(rho)`, while the push becomes a left weight. The optional
   pre-pop-family recorder visits this `Empty` item, which yields no families
   (`machine/entry.rs:1864–1890`, `constraints/mod.rs:4780–4782`). This does
   not erase the push entry: directed conversion creates
   `(id=s,leading_pops=0,family=Some(Empty),pushes=1)`
   (`directed_weight.rs:81–100`).
5. Variable-to-variable transfer stores lower/upper bounds
   (`machine/propagate.rs:104–129`). Lower bound storage retains these weight
   counts when the left filter is `All`
   (`machine/bounds.rs:630–646,674–676,3174–3190`). The push's family and the
   separate left filter are distinct fields; `Empty` in the former does not
   by itself trigger the latter's filter test.
6. Defined parameter frames are popped and passed into their wrappers
   (`lowering/expr/lambda.rs:852–863`). The Defined predicate collector appends
   `frame.subtracts` (`tail.rs:1058–1072`). Output construction wraps both
   `Pos::Var(body.effect)` and `Pos::Var(body.value)` with those weights
   (`:1092–1109`). The wrapper constructor uses `Pos::NonSubtract`, not
   `Pos::Stack` (`lowering/expr/constraints.rs:137–145`), and the resulting
   ports occur in a positive Function (`lambda.rs:958–969`).
7. When H3's Function comparison reaches the return-effect port, ordinary
   Function transfer preserves incoming weights on that covariant child
   (`machine/propagate.rs:257–263`). Positive `NonSubtract` normalization
   prepends its pop to the left weight (`:26–36`). Consequently the second
   local path edge is `Pos::Var(b) <: Neg::Var(eta)` with left `pop(s)`.
8. Replay at `b` composes the lower path then the upper path on the left;
   both bound-insertion orders use that same order
   (`machine/bounds.rs:3452–3464,3622–3634`,
   `constraints/mod.rs:3598–3606`). Replay admission is a real premise:
   pair preparation may omit a pair, and canonicalization, duplicate,
   evidence-only, or resource handling may prevent a newly stored constraint
   (`machine/bounds.rs:3422–3454,3648–3709`).

## Conditional transfer and smallest discriminator

Write an edge as `u --(left,right)--> v`. Set
`T_s=push(s,Empty)`, `P_s=pop(s)` in directed left form. The two local edges are

```text
rho --(T_s,empty)--> b
b   --(P_s,empty)--> eta.
```

Directed left composition uses the integer rule

```text
(m,n) compose (p,q) = (m,n-p+q)       if p <= n
                     (m+(p-n),q)     otherwise,
```

with saturating addition in the second case
(`constraints/directed_weight.rs:137–169,399–404`). Here `m,p` count leading
pops, and `n,q` count pushes for the same ID. Thus
`(0,1) compose (1,0) = (0,0)`, and `push_entry` removes the zero-count entry.
Both right weights are empty, so directed mix leaves the result unchanged
(`constraints/mod.rs:3624–3637`). Under H4, the replay key/edge is

```text
rho --(empty,empty)--> eta.
```

This is a source-grounded calculation of weight fields, not a checker that
postulates transition rules. The ordinary empty-row upper is not read by the
composition functions. Changing it while holding these endpoints, admitted
path, weights, and replay premises fixed does not change this calculation.

**One-field discriminator:** keep the two path endpoints and push fixed;
replace only the wrapper pop's subtraction ID by `t != s`. Composition now
retains two entries: `(s,0,Some(Empty),1)` and `(t,1,None,0)`. They cannot cancel
because `push_entry` matches IDs before composing counts. This is one push,
one pop, one pivot, and one changed field; no claim of language-level
cardinal minimality or accepted source realizability is made. It is an
analytical mutation, not an executed compiler experiment.

An ordering mutation gives another precise failure condition:
`P_s compose T_s` yields `(s,1,Some(Empty),1)`, so the same ID alone does not
justify cancellation. The path must contain the push before its matching pop.
Neither mutation selects a current semantic rule.

If an unweighted concrete positive Function lower with literal
`arg_eff=Neg::Bot` reaches the original demand, the prior characterized branch
adds `epsilon --> rho`. Conditional replay can then carry that argument
effect along the above path to `eta`. The special branch is selected by that
callee port, not by `epsilon`'s upper; no such concrete Function lower is
provided by the isolated formal-to-demand prefix. The separate
`callee.effect --> b` contribution instead acquires `P_s` on replay and has
no matching push on this two-edge path. Cancellation therefore does not
erase the frame pop from every contribution or the stored declaration fact.

## Independence, omissions, and stopping boundary

The frozen source grounds the historical transition and is independent of
current stipulated toy checkers. Its lowerer and solver share one historical
implementation's assumptions. Blob equality establishes provenance, not an
independent semantic oracle. No Oracle acceptance, printed scheme, compiler
execution, or self-review is used.

The precise remaining premise is **which complete source comparison and
typed occurrence path supplies H3**, particularly when the exact nested
candidate places the subtraction on an outer captured-formal frame. This
note derives the local cancellation if that path exists; it does not prove
that path for the nested component. It also does not construct current
Handler/NonHandlerFormal evidence, `Delta_formal`, joint `(nu,K,D)`, original
profile/receipt, exhaustive admission, soundness, or principality. A larger
toy enumeration of the same count rule would leave those premises untouched.

Unverified cases: nested outer-output/function-port composition, aliases,
recursion, multiple frame predicates, nonempty filters/families, nonempty
incoming right weights, generalized/exported schemes, actual source
acceptance, proof-pair coverage, terminal failures, and complete saturation.
Changed blobs, missing/mismatched frame pop, different wrapper/body endpoint,
reversed order, additional weights, filtering, or H4 failures invalidate the
corresponding stored-edge derivation. No global absence claim is made.

Recommended next action: inspect the exact nested outer-output comparison
path only if a further historical correspondence obligation is needed; keep
the current source-owned refinement predicate as a separate open gate.

## Checks, resource use, and provenance

Commands used: read-only revision/status reads; bounded `rg -n`, `nl -ba`,
`sed -n` windows; Python `subprocess` byte comparisons with
`git show SHA:path`, plus SHA-256. Seven sequential frozen-source captures
were used, including the final provenance capture, below the twenty-capture
cap. Early combined current-context captures were truncated; decisive
historical windows and governing sections were recovered narrowly. No omitted
search output is treated as absence evidence.

One lightweight process at a time; no build, test, Oracle run, formatting,
parallel computation, Git mutation, seeds/ranges, executed mutation, or
performance sample. CPU, peak RSS, and exact total wall duration were not
instrumented. Command captures completed in roughly 0.1–0.2 seconds each;
the approximately fifteen-minute wall budget was the scheduling limit, but
exact consumption is unknown. Unrelated staged/unstaged shared-record work
was preserved.

Verified historical SHA-256:

| Path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Verified current SHA-256:

| Dependency | SHA-256 |
| --- | --- |
| Inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Nested-block addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| Main minimal clause | `495aceda697cef317f27be0375423246d9b2c7a341ea81a2bbf8df6e28910b4e` |
| Prior producer continuation | `7b31b95460725948b32f41a3f792c6efc125ade48d83389122f5f3145d36d552` |
| Prior solver mechanism | `68249800e84b767860b76a88086bbe9321c060304065f408fea4afc2f32cd3f9` |
| Multi-use continuation | `ba24a24339402daf9b24d089935754401c0af87786cca6b82dce74bcb9432b67` |
| Main Oracle crosswalk | `d192164e3b07328620fd58c75f4f359b277333885747c815d073520b9bb67784` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-source-producer-solver-transfer.md`.
- Baseline SHA: Yulang3 `c647dc0062c09cc094020757dc0b3afed58b025e`;
  Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; ten historical/seven current blobs matched.
- Review status: frozen, unreviewed research-only bounded characterization and
  conditional local derivation. No self-review or semantic/implementation
  authority. Writes stop before submission.
- Checks already run: revisions/status, seven bounded historical captures,
  exact blob equality/SHA-256, narrow output-scope inspection. No tests,
  builds, Oracle execution, formatting, or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: characterize Oracle return push and matching frame-pop replay`.
- Shared-record deltas intentionally left for primary/curator: record the
  conditional matching-ID cancellation and its output-consumption/replay
  premises; retain the exact nested path and current source refinement,
  original profile/admission, and all proof/production gates as unresolved.
  No shared record was edited.
