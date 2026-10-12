# Oracle choice: independent cut contribution at the actual output POP

Date: 2026-10-12
Status: frozen bounded derivation; independent compiler_referee review clean;
original H and returned-scheme preservation OPEN
Claim class: bounded native source/projection and local collection derivation; exact remaining operational premise
Y3 baseline: `c5c8a6f29`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read location: `/home/momota1029/rust/yulang2-oracle-capture`, using only pinned `git show` bytes
Exclusive lease: this file; constructive leaf, no delegation

## 1. Frozen objective and original scope

The original universal H is unchanged from
[global hygiene proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:
for every successfully lowered Oracle source, every composed-negative concrete
annotation occurrence, its original lexical scope and binders, every actual
copy/use, and every actual function call/output route, authorized subtraction
removes only that instance's attached contribution. Independent contributions
at the same resolved family survive; symbolic tails stay connected; every
current/future concrete lower encounters its retained check. Occurrence,
attachment, scope, actual provider/call binder and correlated residual lineage
survive copying/generalization up to the actual consistent fresh-use renaming.
Successful lowering does not imply successful inference/publication. Incorrect
lowers require actual checking/error and safe nonpublication. Complete Call,
soundness and required principality remain separate required conclusions.

The assigned discriminator is the **entire** source string in Oracle
`crates/infer/src/lowering/tests/case_05.rs:203–226`:

```yulang
act parse 'item 'err 'pos 'snap:
  pub fail: 'err -> never
  pub cut: () -> ()
  pub snapshot: () -> 'snap
  pub restore: 'snap -> ()
role ParseError 'err:
  pub e.merge: 'err -> 'err
pub choice(p: () -> [parse 'item 'err 'pos 'snap] 'a, q: () -> [parse 'item 'err 'pos 'snap] 'a, ()): [parse 'item 'err 'pos 'snap] 'a =
  my snap = parse::snapshot()
  catch p():
    parse::cut(), k ->
      parse::cut()
      catch k(): parse::fail e, _ -> parse::fail e
    parse::fail e1, _ ->
      parse::restore snap
      catch q(): parse::fail e2, _ -> parse::fail: e1.merge e2
```

Keep the declaration binders `'item,'err,'pos,'snap`, choice's annotation
binders and `'a`, parameters p/q/unit, local snap, k, e/e1/e2 and each wildcard
in their original scopes. B is the separate `parse::cut()` application in
the cut arm. It is not the arm pattern, the outer `p()` call, or `k()`.
E means this declaration's resolved parse family **with four actual invariant
arguments**. Distinct operation references initially allocate their own
signature variables; equal family paths do not identify their arguments.
The fixture has no final invocation of choice. A subsequent use is quantified
only when the real compiler actually constructs it; none is invented here.

Required target: follow B through the concrete output POP, returned scheme,
and any actual use/output, retaining the four jointly scoped arguments, both
callback annotation IDs, result ID, and actual current/future checks. Neither
a same-family head nor a successfully stored constraint alone is that target.

Shared hypotheses: immutable source bytes, valid fresh allocation, and normally
completed owning constructor/admission/queue/scoped-query calls before a
terminal failure. These hypotheses do not supply bound inclusion, successful
role resolution, the exported scheme, acceptance, attachment adequacy,
complete replay, or the desired survivor conclusion. The nonterminal prefix
claim below is conditional on normal completion, not an executed assertion
that the fixture reaches this prefix. Resource/error paths are not proved.

Authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6; [residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md);
[complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§§2–5. The retracted callback expected result is excluded. No semantic choice,
source restriction, successor representation or production authority is added.

## 2. Actual POPs, including q and the result annotation

Oracle locators below are relative to `crates/infer/src/`, except `poly/...`
which has prefix `crates/`. Let tau be the ordered four annotation argument
handles. Callback annotations p and q share their named Value-variable map;
their closed Effect coordinate may be shared. Their IDs are separately fresh:

```text
alpha_p != alpha_q != rho
P_p = POP(alpha_p) with filter Set(E,tau)
P_q = POP(alpha_q) with filter Set(E,tau)
P_r = POP(rho)     with filter Set(E,tau).
```

`annotation/constraints.rs:424–470,657–690,921–925` constructs the callback
PUSH/filter/POP pair and returns the actual predicate. The paired Function
retains all four ports (`363–389`). `lambda.rs:1278–1283,1581–1591` retains
the callback call predicate; `919–934` stores it on its own local binding.
**`lambda.rs:1571–1578` makes each Function parameter's immediate output
predicate empty.** This prevents a second p/q parameter-output POP from being
invented around the outer curried wrappers.

The p/q/unit frames are pushed in source order (`lambda.rs:664–742`). Both
ordinary callback calls occur while unit is the last frame; ordinary Catch
does not push a Function frame. `tail.rs:549–552,690–704,719–725` appends the
actual local callback predicates to that frame. Continuation k is Annotated
and returns the actual outer scrutinee Effect (`control.rs:1562–1629`);
`tail.rs:740–758` supplies no unannotated-call PUSH/POP for k. Its binding
has no callback annotation predicate to append.

The result `[parse ...] 'a` uses a fresh inner coordinate and a fresh rho,
not the callback closed-row coordinate (`annotation/constraints.rs:501–542`).
It constructs `Push_rho(U_r) <: R`, returns P_r at `223–240`, registers the
result filter on R, and appends P_r to unit's frame
(`expr/method_body.rs:1715–1752,1876–1888`; `tail.rs:1075–1081`). The plain
result Value `'a` supplies no additional predicate (`constraints.rs:316–322`).

Reverse wrapping at `lambda.rs:852–863,946–968` therefore constructs the
actual unit Function with:

```text
ret_eff = fold NonSubtract(Var(R), dedupe([P_r,P_p,P_q]))
ret     = fold NonSubtract(Var(body_value), the same actual predicate list).
```

Here list order follows annotation/frame accumulation; weights are combined
by the real constructors, not reordered by family. `tail.rs:1058–1072,
1084–1108` and `expr/constraints.rs:137–143` are the consumers. The outer
q and p Functions have empty output predicates for these Function parameters;
their returned Values lead to this same allocated unit Function. Their
evaluation Effects are the actual pure wrapper Effects. No bare R return from
the earlier nullary fixture is substituted.

## 3. Native B seed and inclusion at the body coordinate

This section derives a bounded normal-prefix inclusion; it does not assume
an included B lower. Name the actual allocations Z_B (operation-reference
Value), K_B (call Effect), C_B (complete application Effect), A_B (cut-arm
block Effect), T (outer Catch Effect), D (snapshot/outer-body block Effect),
and R (skeleton body Effect when a named skeleton exists; otherwise D).

The resolved B reference directly calls `constrain_act_operation_ref`
(`expr/block_local.rs:990–1048`). This is an ordinary defined function, with
no sub-return target suppressing the owner. Its stored `cut: () -> ()`
signature and declaration's four parameter names are used together at
`1066–1091`. Positive signature lowering (`lowering/mod.rs:599–615`,
`signature_effect.rs:19–26,78–106`) creates:

```text
F_B = Fun(actual unit argument, Row([],Top),
          Row([Con(E, beta_B[0..4])]), actual unit result)
F_B <: Z_B.
```

Each beta_B entry is the actual invariant neutral argument made by this
signature lowerer. There is no alpha_p/alpha_q/rho PUSH on this row. Failure
branches returning without F_B are excluded by normal owner completion; the
fixture's assertion is not used to bypass those branches.

Z_B is first exposed as this fresh receiver, so its Function lower is
unclaimed/projectable. The complete B demand at `tail.rs:535–563` is
`Var(Z_B) <: Fun(unit_value,unit_effect,Var(K_B),result_value)`; the resolved
global-operation branch uses the bare K_B return (`740–754`). Native Function
comparison at `machine/propagate.rs:212–269` emits the **same F_B's** return
row to K_B. It retains the Function comparison's actual structural parent,
whose replay uses F_B and this very demand. No separately selected provider
or output is introduced.

The source then emits the following empty-context forwarding roots:

```text
K_B -> C_B -> A_B -> T -> D -> R.
```

Owners: `tail.rs:615–624`; `expr/block_local.rs:130–140,1284–1306`;
`control.rs:1164–1168`; the outer prepend of local snap; and
`lambda.rs:788–808`. C_B/A_B/D are freshly allocated block/application
receivers. T is allocated before its first cut arm and is not supplied to
the continuation constructor; k uses the outer scrutinee Effect instead.
The rest of the arm cannot consume B as its scrutinee: `catch k()` has a
different actual computation. The outer Catch's handled-row producer takes
p's scrutinee, not C_B or A_B (`control.rs:922–974,995–1021`). Incomplete
handling of parse's other operations adds routes; it does not subtract B's
arm Effect from T.

For this candidate, R's first incoming exposure is D-to-R. The skeleton
allocates R before body lowering (`lambda.rs:1127–1143`), but the unit
parameter is Unannotated and has an empty predicate. KnownBeforeBody does
not connect its empty predicate (`lowering/local.rs:137–143`); after this
iteration the current Effect is the unit layer's pure function Effect, not
R (`lambda.rs:1186–1240`). The p/q immediate predicates are also empty, as
§2 established. There is no recursive choice call in the fixture. Thus the
pre-body skeleton has no R-to-output Effect connection that can be confused
with D-to-R. Active skeleton records retain params, not R. The result
annotation is installed **after** D-to-R.
The ordinary binding entry supplies no `param_uppers` that could silently mark
unit Annotated: `expr/method_body.rs:55–84` calls `lower_lambda_params`, and
`lambda.rs:244–268` passes `&[]` and no implementation requirement.

For each forwarding root, the fresh incoming key has no qualified replay
parents at initial root admission (`machine/entry.rs:1357–1424`). Var-to-Var
stepping installs the alias lower before its upper (`propagate.rs:104–129`),
then `bounds.rs:962–1029` registers an original Direct claim and the associated
Standalone clause. The Direct coverage root cannot be activated by the
scrutinee's Var-to-Row producer: production activation is keyed by that
actual producer at `row_effect.rs:490–540`, not by equal family or shared
payload arguments. The operation demand is a Function producer, likewise
distinct from a Var-to-Row reduction producer. Unclaimed F_B plus the uncovered
Direct demand includes its Function comparison and derived K_B row. Evaluation
uses `proof/mod.rs:11735–11763,11812–11915`; extra excluded clauses do not
erase an included clause.

This applies the reviewed Direct/structural/replay argument in
[handler proof](2026-10-12-same-family-handler-output-proof.md) §§4–6 to the
new actual keys above. Its old **nullary extrusion** conclusion is not used:
`bounds.rs:4523–4532,4547–4593,4654–4727` traverses all four beta_B neutral
arguments and lowers reachable levels in place, returning the same positive
row ID. It neither erases the argument list nor creates an extrusion copy
or a qualifying parent/copy pair.

Replay activation is explicit. An uncovered forwarding claim makes the real
planner retain a generic pair (`proof/mod.rs:9448–9520`); lower and upper
arrival paths emit that row-to-next-Var task (`bounds.rs:3450–3473,
3582–3645`). `subtype` actually drains (`entry.rs:493–499`). A concrete Row
is not equal-Var self, lower alias-count subsumption, or evidence-only Var
replay (`entry.rs:1092–1118`; `bounds.rs:4274–4294,3814–3829`). Duplicate
canonical tasks retain their actual binary derivation/claim-parent effects
(`entry.rs:1165–1259`; `bounds.rs:3832–3848`). The row-to-Var branch installs
the concrete bound (`propagate.rs:150–160`). Each actual ReplayConjunction
has the included preceding row and uncovered forwarding upper as its two
premises. Induct over this finite route.

Conclusion of this prefix derivation: B supplies a projectable concrete row
bound b_R at the actual R, with its ordered four beta_B handles and a B-derived
included parent clause. It is independent of the callback/scrutinee contribution
by its actual constructor and parent route. This independence is not the
projection enum `Independent`, nor a global attachment theorem.

## 4. What the concrete output POP actually does to B

The final unit Function is installed at a fresh wrapper Value; each outer
wrapper returns that actual inner Value. The successful named-body connection
to the public choice Value is `expr/mod.rs:335–338`. There is no source use of
public choice in this fixture before that connection. Their ordinary Function
lowers and Var-to-Var forwarding have the same unclaimed/Direct/replay
argument as §3. Thus a normally completed scoped query follows the actual
final Function chain, including the unit return port containing all three
POPs. It does not choose an unrelated marginal return.

`structural_kernel/access.rs:862–895` includes b_R through its actual clause.
`compact/collect/mod.rs:848–918` clones the selected bound and passes its left
weight combined with the incoming output weight to its actual positive
endpoint. `Pos::NonSubtract` is consumed at `collect/type_nodes.rs:83–85`;
it combines weights and recursively collects the inner. It does not delete
all Con(E,...) nodes. Native use comparison has the analogous explicit
normalization at `machine/propagate.rs:26–35`. E is an effect family and has
four args, so terminal-constructor weight erasure does not apply
(`machine/entry.rs:1783–1818`).

Let W be the weight actually accumulated along this final return path,
including P_p/P_q/P_r in their actual construction order. The **local
collector result** for B's endpoint is exactly:

```text
Con(E,beta_B)  ->  (E, [N(beta_B[0],W), ..., N(beta_B[3],W)])
N(Bounds(l_i,u_i),W)
              = Interval(collect_pos(l_i,W), collect_neg(u_i,empty)).
```

Owners: `collect/type_nodes.rs:261–288,318–344,404–445`. The emitted row
has E as its concrete key whenever this recursive collection completes;
POPs do not supply a branch that deletes that key. This conclusion keeps
**all four arguments**: it is not the old empty-vector proof. The four
lower/upper pairs are transformed by one collector state and one actual W;
there are no independently chosen argument witnesses. Positive row merging
keeps the E key (`compact/merge/entries.rs:148–180,409–432`) while recording
argument merge constraints and combining their intervals. Therefore the
local positive image of b_R survives the actual output POP as a parameterized
row image. This is a head-and-construction result, not equality of its
invariant argument meaning with the source family or a returned-scheme theorem.

The collector can place a full variable side into recursive bounds rather
than inline (`collect/mod.rs:746–789`). Positive bound aliases become secondary
occurrences (`1099–1128`). No assertion that all source cycles are harmless,
or that the final output is an inline closed row, is needed for the local
formula above. This packet does not prove global root/recursive-bound
reachability after cleanup. In particular, a completed local collection
cannot be substituted for the whole returned CompactRoot's coupled image.

Current/future checks at the live R owner are genuine: the result annotation
registers Set(E,tau), and `bounds.rs:3213–3255` checks existing lowers;
new admitted lowers pass through `630–755,3285–3360`. For b_R, matching E
enqueues the **actual four invariant argument comparisons** with the filter
arguments (`row_effect.rs:903–938`). A true family-path match returns true
after enqueueing those comparisons; it does not prove that they succeed.
It records error on a forbidden family. This is live check invocation, not
a proof that generalization exports all its future consequences.

## 5. Exact first remaining premise and attempted routes

The full assigned target is **not established or refuted**. The first unproved
operation after the source-derived b_R/local POP map is the construction of
its **joint parameterized returned CompactRoot image**, starting with
`collect/type_nodes.rs:318–327::compact_neu_id` and its recursive variable-side
calls. It applies W only to each invariant argument's positive side. The
required missing fact is:

> On this exact choice source, the actual scoped collection of b_R under the
> unit output's W, including any recursive-side placement, retains one jointly
> scoped four-argument image compatible with the actual callback/result family
> arguments and all checks, and the later argument comparisons and recollection
> preserve that same B image through the real return port.

This is not the hypothesis “B is included after compaction,” nor a new proof
relation adopted as compiler semantics. §3 establishes native inclusion; §4
establishes the real local transform. The remaining fact concerns that
transform's argument meaning, shared maps, and returned-root placement.

The first new operational consumer of the potentially different argument
images is concrete: pre-POP/coexisting families and positive rows record
paired constraints (`collect/mod.rs:898–935,384–420`;
`merge/entries.rs:44–83,165–180`). Their four vectors are not empty in this
fixture. `compact/surface.rs:339–372` finalizes the actual paired CompactBounds
and calls native `constrain_invariant_neu`; the var-only fast branch is
another actual consumer, not a proof of the general branch. The module
generalizer applies these constraints, routes their events, and recollects
when its actual restart guard succeeds
(`analysis/session/generalize.rs:49–125,580–602`). The source
also contains the actual `e1.merge e2` role demand. The prior nullary proof's
“empty neutral vector, no role demand, no merge restart” argument is therefore
inapplicable. No assertion of acceptance or harmlessness of these generated
comparisons has been inserted to repair it.

The independent primary-assigned source-owner audit localized a second part
of this same premise; its precise owners were reread at the pin here. For
each finalized invariant pair `(L_i,U_i)` and `(L'_i,U'_i)`,
`machine/entry.rs:1027–1037` emits **both** `L_i <: U'_i` and
`L'_i <: U_i` with swapped directed weights as constructed there. This does
not independently choose witnesses for the four coordinates. The completed
call drains its queue, but `constrain_invariant_neus` returns `changed` by
comparing canonical **constraint count** (`651–673`). The merge driver uses
that Boolean (`compact/surface.rs:339–375`), and the shown generalizer restarts
on it (`analysis/session/generalize.rs:104–125`). A change in projection
inclusion can instead bump ConstraintEpoch and owner epochs through
`constraints/mod.rs:2356–2375`. The cache checks epochs **when called again**
(`analysis/session/generalize.rs:580–603`); an epoch increment alone does not
prove that this loop calls the collector again before using its existing
`next_compact`. Other role/dominance passes can restart, but their existence
does not establish that every relevant change is covered. No actual mismatch
on the choice fixture was demonstrated by either static lane.

The next constructive subclaim can now be frozen exactly. For **each actual
merge batch** generated while collecting this unchanged choice root, retain
its pre-state, finalized W, ordered four-coordinate maps, actual b_R support
DAG, replay parents and coverage roots. Prove that (i) its two-direction native
argument constraints preserve an included B-origin path to this same unit
return, with jointly compatible argument/check meaning, and (ii) every change
to a projection decision or bound/owner epoch in that path or those coordinates
either causes an actual recollection before this compact image is consumed,
or leaves that previously collected coupled image valid. The actual
`changed=false`/projection-epoch-changing branch is included. A source witness
where neither alternative holds refutes this subclaim; arbitrary machine
states or a count-only checker do not supply that witness. This is a concrete
operational premise to prove, not an assumed invariant or a new closure class.

Two distinct attempted routes were inspected:

1. Native bound/projection induction succeeds through b_R and exposes the
   actual output POP. It does not imply that weighted neutral argument
   collection preserves the original coupled family meaning.
2. Direct structural collection/pruning follows the same B endpoint. It
   preserves E locally, but leaves the weighted argument/recollection premise
   untouched. Counts or family equality do not prove it.

Before another equivalent attempt, the economy audit applies. Independent
same-family survival, joint argument/check preservation and ordinary annotated
callback inference are A/B. Reconstructing B's parents from a bare E key is D;
native source and replay owners already know those parents, and this note uses
them directly. The weighted invariant-argument/recollection seam is a genuine
semantic A/B bridge, not eliminated by adding a guessed certificate or calling
it C. It remains OPEN. No canonical lineage/attachment policy changes.

Downstream owners were traced to distinguish the omission from “everything
about generalization.” Dead-ID pruning traverses all four Function ports and
row argument bounds and does not remove a row key locally
(`generalize/core/prune.rs:504–557`). Cleanup selects live covariant IDs;
unquantified IDs are subsequently stripped (`605–620`;
`generalize/mod.rs:176–238,805–828`). Their observation equivalence and recursive
reachability are not supplied by preserving E. The actual module final cleanup
and post-alias/post-cleanup interval passes occur at
`analysis/session/generalize.rs:420–450,492–549`. Positive row finalization
recreates concrete heads and their actual args (`compact/finalize.rs:627–690`),
while principal variable weights erase filters (`586–603,837–839`). Actual
instantiation clones all four neutral arguments through one map and adds
quantified-root POPs with `u32::MAX` (`instantiate.rs:732–787,788–823,
906–981`). These are real downstream operations. Their full checks,
attachment/residual meaning, complete Call activation, and future-use
preservation have not been proved for this source by this packet.

One next decisive packet: prove or source-refute the exact weighted four-argument
collection/merge/recollection subclaim above on this unchanged choice fixture,
using the native b_R/POP construction as input. Freeze the actual scoped
collector root/recursive sides, argument merge constraints, and epoch changes;
attack joint argument meaning and check discharge rather than bare E membership.
The primary owns any instrumentation authorization and independent review.

## 6. Checks, resources and runtime

Read-only commands: pinned `git show` with bounded numbered ranges, `git grep`
at the same Oracle revision, `git ls-tree` for owner locators, and SHA-256 of
those pinned bytes. The original global note and governing designs were read
at c5c8a6f29. Live policy/skill/role configuration was inspected, without writes.
Initial broad captures were truncated; decisive sections were reread narrowly.
No working-tree Oracle source byte was used as immutable evidence. Its dirty
checkout was preserved. No compiler/test/build/Oracle execution, probe,
instrumentation, network request, Git mutation or other lease write occurred.

At most two lightweight shell reads were requested concurrently. Each was
bounded; no heavy process or measurement sample ran. CPU/RAM totals were not
instrumented. Work was bounded by the assigned 35-minute Sol/high packet and
stopped at the concrete operational premise above. No jobs were launched.
Requested runtime: `gpt-6.1-sol`/high. Project config registers unpinned prover
with Sol/high defaults. Observed effective model/effort: unknown; no runtime
metadata was provided. No Astra or reload claim.

Independent `compiler_referee` review found no blocking, major or minor issue
in §§2–5 at frozen SHA-256
`3301a0ac6baccbe9d81ab1b45889a11aaa62dc4c2535680371eef11c375636d2`.
It checked the actual three-POP construction, bounded native B-to-R inclusion,
local weighted four-argument collector map and stated remaining seam against
the pinned source. It did not certify acceptance, returned-scheme equivalence,
cleanup/instantiation, later uses, resource paths or the separate recollection
result. This review closes only the bounded artifact review. H, returned-scheme preservation,
complete Call, soundness, required principality and production/cutover remain
OPEN. The fixture's test assertion was read, not run.

## 7. Pinned dependency hashes and commit packet

SHA-256 of exact pinned bytes (not live-worktree claims):

| Y3 dependency at c5c8a6f29 | SHA-256 |
| --- | --- |
| Original global H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Handler output proof | `d4d77622765d986cb46cbbe0b79fdfa6b18d9099ec53129c877b4cfc0e6f367f` |
| Handler recursive-return proof | `7502f699b0269fb785c90b8e13ad7a74fbae912f1de0816999c6bb232765ee2b` |
| Handler image-preservation proof | `643a2906090eef4ce783cf2f1d2217cccdb997a6942ab7ecad47a27884b39abe` |
| Handler independent-image proof | `99c0a9417ffbdd59ba3716dc4fd6a586f60391bd0c1da48a17b9b7f0acb91c87` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Annotation hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Contextual attachment/admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| Complete Call definition | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |

| Oracle dependency at a58eefc31e22141574b6f20c6a5748151c6d79f1 | SHA-256 |
| --- | --- |
| `lowering/tests/case_05.rs` | `34b06c5590aa64f5bb7de518188c022ba4189e46c90e0526a6d5ae0a34568caa` |
| `annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| `lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| `lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
| `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `compact/merge/entries.rs` | `d848f4034fa57cb7581e58116aba5e825b3f78c79d48bbd08800352dcfc3b10f` |
| `compact/surface.rs` | `1516be08117a372269909fcb7f64780cee4389a52a4f86ef63dd6eaa752b0d89` |
| `compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| `instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `poly/src/types.rs` (under `crates/`) | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Commit packet:

- Exact changed/leased path: `notes/theory/2026-10-12-oracle-choice-output-pop-proof.md`; writing stops at handoff.
- Baseline: Y3 `c5c8a6f29`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; every semantic/source dependency above was read from the pinned object, and none was edited. Live policy/config dependency changes require primary revalidation.
- Initial checkpoint: unreviewed producer derivation. Subsequent independent
  review is recorded in §6; original parent gates remain OPEN.
- Checks already run: pinned source-owner reads/searches and hash capture; no execution/build/test/probe/measurement.
- Proposed checkpoint message: `research: trace choice cut through native output POP and argument-image seam`.
- Shared-record delta for primary/curator: link this bounded native b_R/actual POP derivation and the precise weighted four-argument collection/merge/recollection premise. Preserve original H and returned-scheme/complete-Call/soundness/principality/production gates OPEN. No shared task/index/theory-status files edited.

## 8. Passive constructor evidence prototype

The research-only [trace patch](../../tools/research_choice_recollection_trace.patch)
applies to pinned Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Its first reviewed revision at `60a2003a2` has SHA-256
`42fb29a070d09048a87a9de511a7d519978c77341d40fb1b0c184ef26b37294d`.
It is applied only in the isolated detached worktree
`/home/momota1029/rust/yulang2-choice-recollection-trace`; the dirty original
Oracle checkout and Y3 candidate remain unchanged.

One independent `compiler_referee` reviewed the prototype and its four-file
repair. Static delta review closed the missing native-row-to-weighted-compact
correspondence observations and the direct invariant-merge observation gap,
with no remaining findings. The observations reuse immutable type shapes and
already computed decisions; they introduce no solver/projection queries,
constraints, origins, epoch mutations, caches or admission reordering.
Test-only snapshotting, formatting and I/O add work and perturb timing.

Enable `YULANG_RESEARCH_CHOICE_TRACE` only for the exact existing test
`lowering::tests::case_05::parser_choice_callback_annotation_terminates`.
The original source, test name and assertions are preserved. Events record
source signature/native row IDs and all four neutral coordinates, their
actual weights and completed compact images, finalized invariant operands,
producer/lower-record/claim decisions and collection/publication epochs.
The logger caps output at 12,000 events and 8,192 bytes per event, marking
either truncation explicitly. Missing or truncated observations cannot
establish absence of an inference operation.

Runtime sufficiency is a separate gate. The execution below establishes
compilation and exact fixture completion; untruncated tuple coverage and the
resulting proof remain OPEN. This prototype does not close the returned-image
premise or H.

### First bounded execution

Primary executed the reviewed patch on Rust/Cargo 1.95.0. The initial compile
failed with signal 25 under a 128 MiB file-size limit: that limit also applied
to compiler artifacts. The unchanged sources compiled successfully after
raising that per-file limit to 2 GiB. Both compile invocations used one Cargo
job, a 12 GiB address-space limit, 300-second wall/CPU bounds, locked offline
dependencies and debug information disabled. The successful compile took
42.47 seconds; this is one observed build, not a performance measurement.

Reproduction, from the isolated worktree:

```sh
prlimit --as=12884901888 --cpu=300 --fsize=2147483648 -- \
  timeout --signal=TERM --kill-after=5s 300s \
  env CARGO_BUILD_JOBS=1 CARGO_PROFILE_TEST_DEBUG=0 CARGO_PROFILE_DEV_DEBUG=0 \
  CARGO_TARGET_DIR="$PWD/target-choice-trace" \
  cargo test --locked --offline -p infer --lib \
  lowering::tests::case_05::parser_choice_callback_annotation_terminates --no-run
prlimit --as=12884901888 --cpu=60 --fsize=134217728 -- \
  timeout --signal=TERM --kill-after=5s 60s \
  env YULANG_RESEARCH_CHOICE_TRACE=1 \
  target-choice-trace/debug/deps/infer-b635c7ec75460551 \
  lowering::tests::case_05::parser_choice_callback_annotation_terminates \
  --exact --nocapture --test-threads=1
```

The exact fixture passed: one passed, zero failed, 1,392 filtered out,
15.87 seconds. Nine warnings concern pinned Oracle unused imports/dead code;
their declarations were not introduced by the patch. Removing them would
change the historical comparison source and is outside this evidence lease.
No broad suite or Y3 production test ran.

The runtime log is retained at
`/home/momota1029/rust/yulang2-choice-recollection-trace/research-logs/choice-runtime.log`,
SHA-256 `d561bb77fc5f50aba8c736896e6e659ae7b665d120c6771e12a3790d05c934dc`.
It explicitly reaches the 12,000-event cap: tuple/publication coverage is
incomplete despite fixture success. The prefix contains 5,844 inclusion,
4,098 carrier-delta and 1,149 lower-support-delta observations. The absence
of later collector/publication events establishes nothing about those owners.

The actual independent arm reference is recorded at source range `393..403`:
`RefId(2)`, value `TypeVar(79)`, operation `cut`/`DefId(2)`, signature
`PosId(109)`, return row `PosId(108)` and row item `PosId(107)`. Its ordered
neutral arguments are `NeuId(28..31)`, with native bounds
`(PosId(103),NegId(90))`, `(PosId(104),NegId(91))`,
`(PosId(105),NegId(92))`, `(PosId(106),NegId(93))`.
These are captured identities, not a proof of their final compatibility or
preservation. Independent prefix/source audit verified that this is the arm
body's cut, distinct from the pattern reference at `368..378`. Signature
admission is `ConstraintRecordId(79)`, empty weights, epoch 86; the subsequent
return-Effect structural comparison is `ConstraintRecordId(85)` with parent
claim `UpperReplayClaimId(40)`. This is not the complete B-to-body support
crosswalk. The next
capture must reach the actual weighted collection and publication owners;
another count-only lemma cannot substitute for that missing correspondence.

### Inclusion observation filter

The inclusion-filter checkpoint `e3cde6d5e` has patch SHA-256
`808ebcab1d5115dc47640354e58791c8e5800fb8dc732aa6d153e9ad6640fb12`.
A second narrow independent delta review found no issues. The only additional
source change suppresses the inclusion logger when its already computed
before/after Boolean is equal. All 5,844 inclusion events in the first prefix
were `true -> true`. Pinned `constraints/mod.rs:2125` classifies equality as
`MetadataOnly` or `None`, never `OwnersChanged`; actual projection work and
the existing semantic transition recorder remain unchanged. Nonidentity
inclusion transitions still log, and both original caps remain fixed.

Carrier/support observations cannot be filtered by the same criterion.
All 4,098 retained carriers are distinct. Even when ledger preparation returns
no metadata mutation (`proof/mod.rs:5781`), the owning admission independently
registers claim-parent clause links (`machine/bounds.rs:2373`). An unchanged
inclusion Boolean or empty independent-support vector therefore does not
establish a whole-operation support no-op. Every carrier, producer, support,
claim and projection-owner observation is retained. The next bounded capture
tests coverage; this source audit proves no returned-image theorem.

The filtered revision compiled in 8.54 seconds and its exact fixture passed
in 17.06 seconds, using the same commands and bounds as above. The second
capture remains truncated at 12,000 events: 9,147 carrier, 1,611 lower-support
and 1,022 producer observations consume almost all retained events. It has no
retained root/neutral/merge observations. Its 53,249,776-byte runtime log is
`research-logs/choice-runtime-filtered.log` in the isolated worktree, SHA-256
`21e9452021a481c59d6315c0e7bc371620c5ea9dd231a33e9498999e338a70d8`.
Suppressing equal-inclusion logs therefore does not solve the capture gap.
Do not repeat this unchanged capture or claim absent propagation.

The next observation method must reserve a separate bounded budget for the
source/collector/merge/root frontier, so support-volume truncation cannot
silence those owners. Any omitted support observations remain explicitly
incomplete. Once actual final operands are known, the owning proof can target
their real support cone; frontier capture alone cannot establish it.

## 9. Actual weighted-direct consumer and the unresolved joint judgment

Status: frozen **independently reviewed source bridge and minimized obstruction**; no new
fixture theorem or counterexample. This section uses primary baseline
`e3cde6d5e` on `research/simple-sub-intrusion`, immutable Oracle
`a58eefc31e22141574b6f20c6a5748151c6d79f1`, and the independently reviewed
passive patch at primary checkpoint `e162e549a`, SHA-256
`b2f6de7e1dd550596d6b6c44ce64fa3f26568fdfe3742641e087258892ffe66f`.
Earlier sections and their review scope are preserved. The retained stream log is
`/home/momota1029/rust/yulang2-choice-recollection-trace/research-logs/choice-runtime-streams.log`,
SHA-256 `47d14c23e9d994998a702c39ade7ad33058f30f49a04349a2f4bed30b28e5ed9`.
Its passing test is primary evidence; this leaf ran no inference.

### Frozen statement and evidence boundary

For **every actual normal successful final collection/publication of the
unchanged §1 fixture at the Oracle pin**, B's independent parse contribution
must survive the actual `alpha_p`, `alpha_q`, `rho` subtraction with one jointly
scoped ordered four-argument/check image, through generated invariant
comparisons, projection changes/recollection and the final selected output,
including the actual `e1.merge e2` demand. All original declaration, annotation,
parameter, continuation and error binders in §1 remain fixed. There is no
invented subsequent choice invocation. Shared premises remain immutable source,
fresh arena allocation and normally completed owning calls; successful
publication in the quantifier does not supply the survivor judgment. The
reviewed §§2–4 derivations are inputs, not reproved here. Universal H, later
cleanup/fresh-use preservation, soundness, principality and complete Call remain
parent obligations. No arbitrary preservation of pre-intrusion fibers is added.

IDs below identify this single run/arena only. `(stream,event)` identifies an
observation, not a causal edge. Support ends at 12,000 events and frontier at
2,000; individual operand lines also truncate. Neither missing post-state
fields nor missing late operations can be inferred from these caps.

### Independently grounded source/consumer bridge

The B allocation in §8 still has source range `393..403`, Ref2/TV79,
signature Pos109, return row Pos108/item Pos107 and ordered Neu28–31 with
bounds `(103,90),(104,91),(105,92),(106,93)`. Frontier471 actually reaches
`compact_neu_id(Neu28,W)` with native bounds `(103,90)`, filter
`Set(parse,[Neu16,Neu17,Neu18,Neu19])` and one POP each for SubtractId0/3/6;
its active sides include TV22. Frontier498 and560 contain complete returned
intervals for Neu28 and30. Neu29/31 and the enclosing row-item output truncate;
these observations do not supply the entire jointly scoped tuple.

A new decisive **owning consumer** is source-established, rather than inferred
from a canonical count. Oracle `compact/surface.rs:398–438` accepts an interval
when its four CompactTypes contain only variables and no other shape. It does
**not** inspect their weights or occurrence origins. It extracts just `var.var`,
and `419–422,441–448` forms the distinct nonself Cartesian pairs

```text
vars(lhs.lower) × vars(rhs.upper)
  union vars(rhs.lower) × vars(lhs.upper).
```

Above 32 such pairs (`surface.rs:6,351–359`), it bypasses CompactFinalizer.
`constraints/machine/entry.rs:676–699` allocates bare positive/negative Var
nodes, enqueues each pair with **empty ConstraintWeights**, and drains the
queue. The ordinary branch instead finalizes each actual operand
(`surface.rs:361–372`); `finalize.rs:586–601,837–839` preserves POP entries
in Stack nodes, while clearing the filter. Thus the two constructors are
syntactically different for weighted variable operands. This establishes
neither semantic inequivalence nor a wrong fixture output.

Frontier1835/1836 actually surrounds that direct call. Its complete lhs is an
unweighted interval; the retained beginning of rhs.lower includes primary
TV54 and secondary TV28 under the same nonempty Set/three-POP weight above.
The control location establishes that this actual call passed the var-only
criterion and the greater-than-32 threshold. Both lines truncate before the
pair list and after-state result/epoch; neither exact pairs nor `changed`
are recoverable. The unweighted lhs and weighted rhs must not be exchanged
or completed by guessed aliases.

The batch occurs before `generalize_root_with_prepasses`' first recorded choice
iteration (frontier1992, Def7/TV22, epoch3352). The primary's independent mapper
located the caller at `analysis/session/selection.rs:255–294`; this source was
reread at the pin. That owner collects a root, applies its merges at270, then
collects method-tainted roles and applies their merges at286. Its restart guards
are the actual apply results. This prepass is distinct from the final scheme
collector, and its TV22 reachability does not make its operands the final
selected root image.

The first final-root scoped query is present: frontier1993 includes TV22
Bound2157/Pos233, producer1811, an Original Standalone arm with uncovered
claim12902. Frontier1994 includes Bound2159/Pos232, a ReplayConjunction at
TV183 with lower2156/upper2158 and result producer1812, under the same claim.
These are real included root bounds; their observations do not trace their
nested unit return to B or establish all deeper support/check incidences.
The source consumer `structural_kernel/access.rs:862–895` selects precisely
such scoped decisions; `collect/mod.rs:833–875` distinguishes scheme projection
from raw-bound collection.

### Derivation attempts and exact obstruction

The native support induction uses actual clauses, not source-family equality:
`proof/mod.rs:11735–11763` evaluates Standalone support, a DerivedUnary's
premise and **both** ReplayConjunction premises. Its support/coverage selection
at `10059–10083,11650–11665` reads live coverage. Adding bounds or clauses alone
therefore does not prove that an existing B clause remains decisive after the
prepass. The two recorded final-root arms ground the root step, but not the
B-to-unit-return chain, the four argument sides or their changing coverage.
An unexamined clause is not an independently retained B witness.

The second method compares the actual weighted and direct constructors. The
real retained filters can supply stronger native facts: `row_effect.rs:925–934`
emits invariant comparisons of the **actual** family arguments and filter
arguments with empty weights; `bounds.rs:3243–3253,3285–3315` invokes these
checks on existing/future lowers. These are possible source justifications for
bare equality of particular argument variables. They do not establish that
**every extracted pair** in this truncated direct operand is already justified
by those same four scoped coordinates. A Value coordinate can contain a
Function with effect ports; the var-only test supplies no restriction making
its weight irrelevant. No generic weight-erasure law follows from that test.
Conversely, existing genuine coordinate equalities could make a particular
bare pair redundant, so the observed weighted direct call is not itself a
counterexample.

The unresolved actual judgment is therefore: **for the prepass's generated
weighted operands and actual direct pair set, do the admitted empty-weight
relations retain the same jointly compatible B/family/check observation at
the final unit return, and do all relevant projection changes receive an
actual recollection or an independently valid surviving collected image?**
Its first omitted source owner is the weighted-variable extraction and direct
admission above, together with the existing native comparison derivations
that could justify its particular pairs. The final selection consumer is
`analysis/session/generalize.rs:67–125,327–351`; it does not supply a general
weight-equivalence premise. This judgment is not replaced by a numerical
restart lemma. No complete Call/role solution or final tuple is asserted.

These two methods leave this judgment unresolved; no third equivalent proof
attempt was made. Economy audit: preserving the independent contribution,
joint check meaning and ordinary polymorphic inference is A/B. Recovering
operand provenance from bare IDs after extraction would be D: the collector
and merge constructor already know the weighted operands and their source
sides. A bounded observation of those existing facts can discriminate the
actual semantic question; inventing a reconstruction layer, requiring empty
weights, restricting source arguments or choosing four marginal witnesses
cannot discharge it. The semantic observation law itself remains A/B and is
not reclassified away.

One next action: primary obtain complete bounded per-coordinate operands,
the actual extracted pairs and their pre-admission native comparison/support
cone from these owners, then prove their effect on the original B/check image
or exhibit the first failing source-qualified pair. This is evidence for the
existing theorem, not a proposed compiler invariant or semantic change.

### Freeze and commit packet

Only §9 of this leased note was appended. Pinned `git show`/owner searches,
bounded static log inspection and SHA-256 checks ran; no build, test, probe,
measurement, network call, Git mutation, delegation or other write ran. A failed
read of nonexistent `analysis/session/role_solve/selection.rs` was corrected to
`analysis/session/selection.rs`. At most two light read processes ran together;
CPU/RSS were not instrumented. The assigned limit is20 minutes, no heavy jobs.
Requested runtime is Sol/high; observed effective model/effort is unknown.
Fresh independent `compiler_referee` review of §9 against frozen note SHA-256
`b224f1b214234e94935ee80ee6a17cd8bde99f0a29a05595e1808f776ae3602a`
found no issues in its bounded source/obstruction claims. It establishes no
fixture theorem, semantic inequivalence, counterexample or universal H.

- Exact lease: `notes/theory/2026-10-12-oracle-choice-output-pop-proof.md`;
  writes stop at handoff. Its pre-append bytes equal the e3cde6d5e note,
  SHA-256 `5e9b1c6202e4e4af10d3f4f609b563c7b1513c82b63efc02be5f88c6bd46ec51`.
- Baseline: `e3cde6d5e`; Oracle pin above. Primary checkpoint e162e549a
  supplies the reviewed b2f6 trace dependency; the older §8 revisions remain
  historical. The trace patch subsequently changed in the live tree to
  `790cd6e2124c50e0dfdfe11286e65c71fd2515ef35d20f20e090779c269e3970`;
  that new patch/capture is excluded here. The immutable old log hash rechecks.
- Newly inspected pinned dependency: `analysis/session/selection.rs`,
  SHA-256 `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33`.
  Existing Oracle source dependencies retain the §7 pin; no dependency edited.
- Claim/review: source-qualified weighted-direct activation and exact unresolved
  observation judgment, independently reviewed; no theorem/refutation or
  parent-gate status promotion.
- Proposed checkpoint: `research: isolate actual weighted-direct choice image obligation`.
- Shared-record delta left for primary/curator: link this actual direct-consumer
  seam and final-root query evidence; preserve original H, fixture joint image,
  complete Call, soundness/principality and production gates OPEN. No shared
  record was edited.

## 10. Complete scoped input and generalized-image evidence

The current passive patch SHA-256 is
`2f5aebb481a000085f2d5683b1ca4447e181db2307602dfc7d44c75ca7352ae1`.
Its observation changes passed independent delta review. Root images and
merge inputs have separate 2 MiB payload budgets, retaining the same total
4 MiB reservation, fixed UTF-8 chunks and explicit partial markers. Complete
objects require matching `(stream,object)`, contiguous parts and the declared
byte total. No solver operation or query is added.

Primary's resource-capped compile passed in 12.65 seconds; the same exact
fixture passed in 15.80 seconds (one passed, 1,392 filtered out). Commands and
12 GiB/300-second compile, 12 GiB/60-second runtime bounds are as in §8.
No broad suite or performance sample ran. The nine pinned warnings persist.

The final log `research-logs/choice-runtime-partitioned.log` in the isolated
worktree has SHA-256
`f5bea54332825041117e2f957255b4409fc589d057a78987712746385b4f186f`.
Primary reconstructed 25 complete objects, checked each part index, byte total
and UTF-8 decoding, and saved them under `research-logs/partitioned-objects/`.
The choice objects are:

| Object | Complete bytes | SHA-256 |
| --- | ---: | --- |
| `root-image-15.txt`, collected iteration 1 | 84,111 | `a3b19eeeff836779ec237b9e0152bd6b12866f89e119a44289e5ce7e20dce075` |
| `merge-input-5.txt`, iteration 1 | 1,952,606 | `274161d2677d8822066f2b7975d659b16e72a63ce345781cceec995eee3165fb` |
| `root-image-16.txt`, collected iteration 2 | 84,111 | `04dc44b84d74ffd5fa0eaa36278a318cde8c23944d25d040785902ff486a65e7` |
| `root-image-17.txt`, selected iteration 2 | 84,110 | `8cd393e6d2420f57b2aa5a79a068eb34b2732e82a16c6a558a3b8100ca45acbf` |
| `root-image-18.txt`, generalized | 19,692 | `ee1ca6e3c5a7a26f240002b6f39befbddde3ee3c9af2ecf0a3dff1a81de73986` |

All choice objects identify `DefId(7)`/`TypeVar(22)` and epoch 3352. Support
and frontier logs still truncate; `merge-input` iteration 2 is partial. The
preceding reviewed shared-publication capture retains complete iteration 1/2
constraint vectors, but this run's partial vector must not be treated as
complete merely because the earlier run had matching bytes.

Moving scalar fields ahead of large direct-merge operands also retained its
actual pre/post epoch 3178 and `changed=false`. Count stability alone does not
prove source justification, projection stability or future hygiene. Complete
compact/generalized bytes establish the missing result observation, not
semantic compatibility or preservation. They now permit the original proof
owner to derive the actual tuple/substitution/support correspondence. Actual
definition publication/fresh use and the original universal H remain OPEN.

## 11. Complete joint image, actual merge omission, and native remainder

Status: **independently reviewed bounded source/consumer bridge**, not the original fixture
theorem or its refutation. Baseline `67830dce1`; Oracle pin unchanged. The
statement, original scopes/binders, hypotheses, required four-coordinate/check
conclusion and exclusions are exactly §9's frozen statement. Universal H,
complete Call, soundness, required principality and future-use obligations
remain unchanged. §§1–10 are preserved.

This pass uses only the partitioned log and complete objects in §10, under the
reviewed `2f5aebb…` passive patch. The five object lengths/hashes were rechecked;
the partial iteration-2 merge input and truncated support/frontier tails remain
excluded. A bounded structural decoder consumed each complete object's entire
Debug value. Its key-collision result was separately checked against all 156
literal key strings. This is static artifact inspection, not a solver probe or
proof of the decoder's source assumptions.

### One actual four-coordinate image and shared substitution

The complete iteration-1, iteration-2 and selected-root CompactRoot **values
are structurally identical**; their event headers differ. Each has precisely
one concrete parse row in p's callback return, q's callback return and the
unit return. The unit is reached through the actual p Function's return,
then q Function's return, then unit Function's `ret_eff`; no unrelated return
is selected. Native B's four Value coordinates TV81–84 occur in order in this
unit row's four intervals. The lower sides carry Set(parse,Neu16–19) and
POPs0/3/6; upper sides are unweighted. These are simultaneous occurrences in
one whole root, not independently selected witnesses.

The complete generalized object records **one shared substitution**:

```text
TV81 -> TV28; TV82 -> TV29; TV83 -> TV30; TV84 -> TV31.
```

Its p/q callback parse rows contain the ordered intervals
`[TV28,TV29,TV30,TV31]`, with unweighted lower/upper occurrences. Its same
unit-return parse row has those same four ordered lower variables under
Set(parse,Neu16–19), no stack entries, and unweighted upper variables. The
retained ParseError role has one invariant TV29 input; quantifiers are
TV26/28/29/30/31, and stack quantifiers are empty. Thus the actual exported
*structural* coordinates and role coordinate are now known jointly.

These observations have real consumers. `generalize/simplification.rs:100–151,
164–187` rewrites constructor arguments and all Function ports through the
same substitution map; `155–161` combines weights only after variable targets
coincide. `generalize/mod.rs:176–241` chooses actual quantifiers and removes
unquantified stack IDs; `core/prune.rs:504–555` preserves the row key while
traversing its four interval arguments. This explains the recorded structural
transformation. It does not prove that the chosen variable identifications,
removed stack entries or retained filter handle have the required original
check/future-use meaning. A map recorded *after* simplification cannot justify
the earlier comparisons that simplification assumes.

### Exact source-derived pair set and memo effect

The complete iteration-1 input contains 156 ordered constraints. Every operand
is a variable-only Interval accepted by `surface.rs:398–438`. Applying the
actual helper's two Cartesian products, distinct-pair deduplication and self
exclusion gives four disjoint native sets:

| Coordinate | Native variables appearing in its operands | Distinct helper pairs |
| --- | --- | ---: |
| item / TV28 | 28,54,74,81,101,108,129,148,155,185,189,194,198,202 | 182 |
| err / TV29 | 29,55,75,82,98,102,107,119,123,130,145,149,154,164,186,190,193,199,201,205 | 342 |
| pos / TV30 | 30,56,76,83,103,109,131,150,156,187,191,195,200,203 | 182 |
| snap / TV31 | 31,57,60,77,84,104,110,128,133,151,157,188,192,196,197,204 | 240 |

There are 39 constraints per coordinate. In every constraint, lower/upper
variable **sets** match those of its coordinate's first constraint, although
weights and occurrence order vary. For err, 119 and123 occur only on the lower
sides; the upper sides contain the other18 variables. Its 342 pairs are the
20-by-18 product minus18 self pairs. The other three coordinates give the
full distinct-pair products of sets of14/14/16 variables. Total:946 distinct
bare pairs. This enumeration is an exact finite characterization of the actual
complete operands; it does not assume their compatibility.

The decisive previously unseen consumer is the merge **memo key**. All156
constraints have exactly the same key:

```text
CompactMergeConstraintKey {
    lhs: Interval { center: None }, rhs: Interval { center: None }
}
```

This follows directly from `compact/merge/mod.rs:27–43,89–113`: a multi-variable
interval has no single center, so its key retains neither variable IDs nor
weights. The actual item/err/pos/snap source coordinates therefore collide.
`surface.rs:347` inserts this key into the shared applied set before invoking
the direct/ordinary branch. `analysis/session/generalize.rs:49` starts that
set empty for this invocation. Consequently the first156 root constraints
process **only index0 (item,182 pairs)**; indices1–155 are skipped by key reuse.
Role collection may append later tasks to this same set; it cannot retrospectively
make this earlier skip an err/pos/snap comparison. These claims are derived
from complete ordered inputs and the real control flow, not from absence of
trace events. Nothing is inferred about the partial iteration-2 vector.

This is not a fixture counterexample. The skipped consequences might already
follow from the native filter/call constraints, or be authentically represented
by the returned contract. What is refuted is the proposed *justification*
that collecting all four vectors, recording156 constraints or draining one
processed coordinate proves that all four generated tasks were activated.
The original theorem did not assume that shortcut.

### Actual native proof attempt and exact remaining judgment

Native filter formation supplies genuine relevant facts:
`row_effect.rs:925–934` generates paired comparisons of actual family/filter
arguments with empty weights, including B's beta/filter comparisons when its
registered check runs. It calls `row_effect.rs:71–86`'s
`enqueue_row_invariant_args`, which emits both directions through
`entry.rs:1617–1701`'s `enqueue_row_derived_subtype` admission path;
`propagate.rs:104–129` accumulates their Var lower and upper bounds. Opposite
replay at `bounds.rs:3452–3473` retains the real parents, composes the actual
weights and submits the replay constraint. This is the constructional route
to proving that each coordinate's required comparisons are already justified.

However, the complete compact operands do not provide that native derivation.
In particular, `collect/mod.rs:964–1009` can emit an unweighted negative alias
from a native bound having pop-only context, so a plain upper occurrence in
the complete Debug value does not certify an empty-weight native edge. The err
lower-only119/123 cases must follow their actual call/provider route; they
cannot be replaced by a symmetric20-variable equality class. The generated
substitution's identification of them with29 does not supply those missing
source premises.

The alternative prior-canonical route is grounded but narrower. For the actual
prepass direct call at epoch3178, `changed=false` plus append-only occupied/
vacant admission (`entry.rs:676–699,1092–1118,1357–1424`) implies no new
canonical bare pair key was added by that call. Hash-consing at
`poly/types.rs:676–692` fixes the exact Var endpoint IDs. The occupied branch
can add root origins and projection carriers; `bounds.rs:2373–2555` shows
these operations explicitly. Projection publication evaluates inclusion and
invalidates affected owners (`constraints/mod.rs:2119–2150,2356–2375`), and
3178 is below the epoch saturation boundary (`339–356`). This rules out
claiming a newly added type constraint merely because a weighted operand was
seen. It does **not** establish the original source origin, activation or
weighted observation meaning of the previously stored keys. Moreover, this
prepass's full operands are still truncated; it is not the complete3352 input.
Matching prefixes or numeric IDs cannot identify their entire pair sets.

Both methods therefore stop at the same precise native judgment: **for the
actual four ordered coordinate classes above, the original filter and complete
call/role constructors and their retained replay clauses must discharge (or
correctly represent) every skipped weighted comparison and the actual direct
bare relations, while retaining B's check-compatible unit-return contribution
under the observed shared substitution and stack cleanup.** The first omitted
owning justification is at the multi-variable merge-key reuse/weighted direct
consumer; its necessary native witnesses belong to filter comparisons, the
119/123 error-call route and qualified replay, not the compact image alone.
No wrong final scheme, alternative provider or source-qualified contradiction
was established.

Economy audit after these two different methods: independent B survival and
joint ordinary annotated inference remain A/B. Reconstructing native weights,
parents and admission from a compact alias or centerless key is D: the bound,
collector and comparison constructors already know those facts. The next
useful action is a native proof of the exact directional class saturation and
weighted/check consequences above, using the source filter/call/replay owners;
another complete final-image dump or count lemma leaves that premise untouched.
No new semantic layer, arbitrary pre-intrusion fiber requirement, empty-weight
restriction, source-domain narrowing or proof-status change is adopted.

### Freeze and commit packet

Only §11 was appended. Pinned source reads/searches, bounded static decoding,
object length/hash rechecks and leased-note whitespace checking ran. No
compiler execution, build/test, solver probe, measurement, network request,
Git mutation, delegation or other path write ran. At most two light read
processes; this pass used sequential reads. CPU/RSS were not instrumented;
20-minute assignment bound retained. Requested Sol/high; observed runtime
settings unknown. A fresh independent `compiler_referee` review found no
blocking or major issue and one minor citation mismatch; this repair replaces
the root-invariant citation with the actual row-invariant owner and extends the
replay citation through weight composition and replay admission. The substantive
paired-comparison claim was confirmed. See the review summary below.

- Lease: this note only; writes stop at handoff. Preserved §§1–10 SHA-256:
  `a89d697897a230e2690abd90fb154650c0bdec99715023eb9ceebc02fcd1ff39`,
  equal to its baseline67830dce1 bytes.
- Baseline: `67830dce1`; Oracle pin above. §10 partitioned objects retain
  their recorded hashes. No dependency edited.
- New pinned source hashes: `compact/merge/mod.rs`
  `272b2ad1609a2e5fe8e17ca9f7924cd2211cb1196a72f94d6118f70d1d886569`;
  `generalize/simplification.rs`
  `13936efe8423630581ccf7f813ee9b3fcc82ca2cbba4a7fd9284fc741b53536a`.
- Claim/review: exact joint structural image, actual pair/memo consumer and
  native obstruction, independently reviewed after the citation repair;
  original theorem/refutation not established.
- Proposed checkpoint: `research: map complete choice tuple and native merge omission`.
- Shared-record delta for primary/curator: record the one shared four-coordinate
  output/substitution bridge and the actual centerless-key omission with its
  exact native remainder. Keep fixture hygiene/H, complete Call, principality,
  soundness, future-use and production gates OPEN; no shared records edited.

### Independent review and repair

The fresh `compiler_referee` review independently decoded the complete objects
and confirmed the joint row image, shared substitution, all 156 memo-key
collisions, the four exact pair sets, and index-0-only activation. It found no
blocking or major issue. Its minor finding was that the first draft cited the
root invariant helper instead of the row filter's actual invariant helper and
stopped the replay citation before composition/admission. The repair above
traces `row_effect.rs:927–933` through the two-direction row helper and its
row-derived subtype admission, and cites lower replay through `bounds.rs:3473`.
The reviewer
confirmed the substantive claim; it did not reprove §§1–10, reconstruct
truncated native support, establish future-use/publication, or prove/refute the
original fixture theorem, H, soundness, principality or complete Call.
