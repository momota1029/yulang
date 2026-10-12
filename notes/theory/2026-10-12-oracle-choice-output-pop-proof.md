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

The current patch SHA-256 is
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
