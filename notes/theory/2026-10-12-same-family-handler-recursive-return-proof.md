# Same-family arm contribution through the recursive Oracle return

Date: 2026-10-12
Status: frozen bounded derivation; independently reviewed after narrow repair; original H/P+ output OPEN
Claim class: bounded native source-to-selected-return derivation; same-witness export OPEN
Primary input checkpoint: `7b663d1bb`
Oracle source: immutable `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen statement and dependencies

Continue the same P+ candidate, B occurrence, original lexical scope and
binders in [reviewed handler derivation](2026-10-12-same-family-handler-output-proof.md)
§§1–7. The original universal H from that note §1 retains every source,
annotation occurrence, original scope/binder, actual copy/use, complete
provider/Call/output route, independent same-family contribution, symbolic
tail and current/future lower. Neither H's domain nor its conclusion is
narrowed. A bounded P+ result cannot close universal H.

The assigned continuation starts from its independently reviewed actual
projectable E lower at K_B and native source-to-T ReplayConjunction tree.
Derive the actual T-to-R recursive-skeleton forwarding and retain that same
correlated parent tree through actual Function/root selection, compaction,
generalization and the later/current outer Call output. No chosen provider,
selected Q_M member, P+ acceptance or output membership is a hypothesis.
If the complete conclusion fails, stop at the first exact source/operational
fact not established and report a reduced derivation as such.

Shared assumptions are the immutable source bytes, normal completed owning
calls and valid fresh allocation before exhaustion, with the preceding note's
explicit limits on rejected/resource-terminal/incomplete-evidence paths.
The direct signature constructor's success and source-to-T tree are consumed
within that reviewed scope, rather than reconstructed or reclassified.
The original source-route note is a complementary input, not another proof
of an assumed output. This packet authorizes no execution or instrumentation.

Governing authority remains annotation hygiene §§1–4; contextual
attachment/admission §§3–6; selected residual lineage; complete Call §§2–5;
and top-level inference principles §§1–5, as linked in the preceding note.
Complete Call, soundness, required principality, source acceptance and all
uncovered parent-H cases remain separate obligations. No semantic change,
residual merging, independent marginal witness or fresh-use map is adopted.

## 2. Actual roots, recursive skeleton, and construction order

All Oracle locators below are relative to `crates/infer/src/` at the immutable
revision. A coordinate names an allocation by its owner; it is not an
arena-local ID, effect-family origin, or independently selected witness.

| Coordinate | Allocation/use owner |
| --- | --- |
| G | public `run` Value root, `lowering/body/mod.rs:2282–2288` |
| S | internal named-self Value, `lowering/expr/mod.rs:309–327` |
| L, L_v | single skeleton layer's output Effect/Value, `expr/lambda.rs:1132–1137` |
| R, R_v | skeleton body's Effect/Value, `expr/lambda.rs:1140–1141` |
| T | reviewed catch result Effect |
| W | final lambda wrapper's Value, `expr/lambda.rs:954` |
| b_T, b_R | actual ordinary concrete E-row lower records at T/R |
| u_TR | actual upper `Neg::Var(R)` admitted at T |
| p_T | reviewed B-derived lower/projection derivation at b_T |

The distinction between G and S is necessary. The header-argument branch
calls `lower_binding_body_with_args_to_named_self` with G
(`body/mod.rs:2309–2318`). That owner creates S and installs a local `run`
binding with `scheme: None`, `call_return_effect: Annotated`, empty predicate
subtracts, no call projection, and no recursive effect passthrough
(`expr/mod.rs:309–327`). The body is lowered with S as its self Value
(329–334). On successful return, the owner connects the **final computation
Value** to G (335–338). Consequently, the recursive arm call uses the local
S; it is not an already published G scheme. The later outer reference uses
the actual public definition. `name_ref.rs:146–187` owns the local branch;
the public branch at 83–115 queues the resolved definition/use. Sharing a
DefId for reference resolution does not identify their Value allocations.

For one parameter the lambda owner allocates the skeleton before entering
the body's child inference level (`expr/lambda.rs:745–776`). Its positive
self Function has the actual parameter argument ports, return Effect L, and
return Value L_v, and is constrained to S (1146–1173). The initial frame is
Defined and empty. The reviewed source-route calculation finds no output
predicate for this annotated `action` or Value-only result `'a`; this result
is consumed within that calculation's scope. `KnownBeforeBody` connects an
empty predicate for an Annotated parameter (`lowering/local.rs:133–143`).
Therefore 1176–1240 emits, before body lowering:

```text
R   <: L
R_v <: L_v
L_v <: R_v
```

The reverse constraint is a **Value** constraint. It does not put a negative
R Effect into the graph. The recursive call returns L to its own return slot,
then to C_C and the block/catch results. The continuation `k` instead has
return Effect V (`lowering/control.rs:1596–1629`). These facts distinguish
the skeleton's self interface from the final Function return coordinate.
Its actual annotated argument Effect is not `Neg::Bot`, so the self call's
argument Effect is not forwarded to its return by the pure-argument
passthrough rule (`expr/lambda.rs:1244–1341`;
`constraints/machine/propagate.rs:230–263`). No complete Call theorem is
inferred from that local constructor fact.

## 3. Native T-to-R forwarding and the same B parent derivation

### 3.1 Why the preallocated R permits this particular Direct claim

R is preallocated, but **its incoming Effect side is first exposed by
`T <: R`**. This is stronger and more specific than claiming that R is a
fresh allocation at the catch boundary.

The prefix before `expr/lambda.rs:797` uses R positively for R-to-L; its
skeleton shape uses L as the return port. The active-skeleton record contains
the parameters, not R (768–772). P+ has no local binding/generalization,
method, guard, ascription, or sub-return owner in its arm block. The
continuation's port is V. The catch's row receivers are T and its own
residual coordinates, not R. Native alias replay may propagate **positive**
R through L and the recursive call's return slots; this does not introduce
negative R. In the row structural owner, variable row items are separated
from reversible concrete tail items, so the variable's upper tail is not
reversed to that variable (`machine/propagate.rs:708–829`, especially
799–801). Concrete marker reversal at 1044–1141 involves the nullary E
marker; E's arguments do not contain R. Thus it supplies no missing negative
R occurrence. Value/result constraints remain separate from Effect ports.

It follows from this prefix inventory that no prior canonical producer has
the exact `Pos::Var(T) <: Neg::Var(R)` key, and R has no earlier lower record
with positive endpoint T. T and R are distinct actual allocations. This
argument allows R's existing outgoing upper records and recursive alias
cycles; it does not require R to have no bounds or no outgoing consumers.

`expr/lambda.rs:788–808` emits this root before connecting the result
annotation and replaces the computation Effect by R. A root admission has
no structural/replay/row parent merely because a reverse path already exists
(`machine/entry.rs:1357–1424`). In `step_subtype`, lower T is installed at R
before upper R is installed at T (`machine/propagate.rs:104–129`). The new
lower can queue consequences through R's outgoing uppers, but the step does
not drain that queue between its two installations. Registration of u_TR
therefore sees this actual root's empty qualified-parent list, registers its
original Direct claim q_TR, and registers a Standalone Claimed(q_TR) clause
on the alias lower (`machine/bounds.rs:630–755,815–920,962–1029`;
`constraints/mod.rs:1717–1813`). Existing positive self aliases are not
qualified parents of this root by inference.

The original producer is Var-to-Var. As in the reviewed original-claim
lemma, production live row-reduction coverage is activated by an actual
Var-to-Row producer at `constraints/row_effect.rs:490–540`. Producer-keyed
original claims are distinct; derived claims preserve their actual root.
That activation owner cannot activate q_TR's original root from a different
row producer. Consequently `eval_root_coverage(q_TR)` is IncludedExact
(`constraints/proof/mod.rs:11879–11915`). Its Standalone clause includes
the actual alias lower. This conclusion uses the actual Claimed Direct
clause, not an assumed Independent carrier or an Internal-origin slogan.

### 3.2 Concrete replay, including both arrival orders

Consume the reviewed b_T/p_T. For b_T and u_TR the actual replay planner sees
an uncovered q_TR, sets `requires_generic`, and retains the lower and upper
parent blocks (`constraints/proof/mod.rs:9448–9515`). The upper-arrival route
iterates T's actual projection lower records and supplies
`BinaryReplayDerivation { pivot: T, lower: b_T, upper: u_TR,
rule: UpperBoundAdded }` (`machine/bounds.rs:3582–3645`). The lower-arrival
route performs the same pairing against the actual registered upper, with
`LowerBoundAdded` (3450–3473). Thus the result does not depend on assuming
that stored constraints are eventually replayed by an unspecified consumer.
In P+'s initial completed body the B row is present before the final root;
the second route covers a subsequently admitted lower against that root.

Both produce the same positive `Row([Con(E,[])])` against negative R, with
the actual ordered composed weights. This B path has empty weights. The
result cannot be omitted as Bot, equal-Var self, or evidence-only Var-to-Var
replay (`machine/entry.rs:1092–1118`; `machine/bounds.rs:3814–3829`). A new
canonical result is queued; an existing one receives the actual replay
provenance/qualified-parent consequences (entry 1165–1259; bounds
3033–3053,3832–3848). In particular, coalescence with a same-shaped row does
not justify replacing B's binary derivation by that row's other origin.

The positive-row-to-Var branch installs b_R
(`machine/propagate.rs:150–160`). Lower alias cycle subsumption applies only
to `Pos::Var`, not this row (`machine/bounds.rs:4274–4294`). Bound insertion
retains the ordinary concrete record (`constraints/mod.rs:2420–2439`);
projection iteration includes ordinary/evidence records (2656–2678).
Extrusion visits E's nullary constructor and the Row without changing them
(bounds 4523–4532,4547–4593). At the T/R level crossing, Oracle lowers
reachable variable levels in place (4701–4727); it does not allocate an
extrusion copy of E, identify T with R, or infer a qualifying parent/copy pair.

The admission registers the actual ReplayConjunction with lower premise
b_T and upper premise u_TR (bounds 1179–1243,2332–2370). Applying the
reviewed p_T and q_TR inclusion proves this **particular registered clause**
included (proof 11735–11763). Call this retained clause/derivation p_R:

```text
B's actual K_B seed
  -> reviewed C_B/B_eff/T derivations p_T
  -> ReplayConjunction(b_T, u_TR) at b_R
```

All links are actual producer/record/weight links. No family-equality step
or independent replacement of a lower premise appears. This proves that
b_R has an included B-derived clause and is a projectable E-row record.
It does not yet say which decisive clause a subsequent query returns when
that record has more than one included clause; §5 keeps that distinction.

### 3.3 Lexical nesting and recursive owners

Nothing here requires recursive declarations or Value SCC members to share
an inference level. The user's separate nested odd/even example supplies
Value-owner edges O-to-E and E-to-O and hence a nontrivial SCC across lexical
levels. Such an SCC alone is not an extrusion parent/copy qualification.
P+ has the concrete G/S/L/R allocation route above and in-place Oracle
extrusion. The nested example adds no premise or new source case to this
fixed discriminator; it refutes using same-level declarations as a general
recursion assumption. No Y3 parent/copy theorem is imported from Oracle's
different extrusion owner.

## 4. The actual selected Function return port

After the body Effect has been replaced by R, the result annotation is
connected at `expr/lambda.rs:810–834`. Its actual `'a` is a Value-only result
in the reviewed source-route calculation, not an output Effect subtraction.
After restoring the body level, the single parameter is wrapped at 852–864.
`wrap_lambda_param` allocates W and admits its actual positive Function
(946–975). The empty output-predicate branch of
`expr/tail.rs:1084–1101` returns `Pos::Var(body.effect)`. Therefore:

```text
F_final = Fun(actual_arg, actual_arg_eff, Var(R), actual_ret)
F_final <: W
W       <: G
```

This is the final wrapper's Function; it is not S's Function with return L.
It is also not the control P0 scheme. The named-self owner emits W-to-G only
after this successful wrapper (`expr/mod.rs:335–338`). The header-argument
binding's `finish_binding` has `connect_body = false`
(`body/mod.rs:2358`), so no second guessed body-to-G route is needed.

W is fresh when F_final is installed and its ordinary Function lower is
unclaimed, hence projectable. G is freshly allocated before this body; P+'s
prefix has no reference to G. Recursive calls use S. W-to-G is therefore
a new root with empty qualified parents and a Direct q_WG, using the same
actual-root admission argument as §3.1. Its original producer is Var-to-Var,
so q_WG has no live row coverage. Actual replay of F_final against W's
registered upper G installs the Function lower f_G and its included
ReplayConjunction. A Function is not subject to lower Var alias subsumption
or evidence-only Var-to-Var replay. Extra compatible lowers or upper
compatibility checks do not erase this ordinary lower on a normally
completed, nonterminal path.

For any actual successful scoped scheme query at G,
`constraints/structural_kernel/access.rs:862–895` iterates f_G and includes
it: membership follows from its actual admission/clause, rather than being
assumed in Q_M(G). Its `ret_eff` is the exact allocated `Pos::Var(R)`.
For the subsequent actual query at R, §3 supplies membership of b_R in
Q_M(R). These two queries are connected by the selected Function's own
return port; they are not separately selected provider and output witnesses.
This closes the preceding note's T-to-R and actual selected-port premise
within the normal-completion scope. It does not establish P+ acceptance or
prove that its deferred result check succeeds.

`compact/collect/type_nodes.rs:13–22,196–225` sends that selected return
port to positive Effect collection. At b_R, the actual
`Row([Con(E,[])])` bound maps to a CompactRow with the resolved E key and
empty argument list (261–286,404–445). This local materialization follows
from the selected concrete bound; a secondary Var alias is not substituted
for it (`compact/collect/mod.rs:1099–1128`). Positive row/function merge
retains the concrete key (`compact/merge/entries.rs:288–306,409–432`).
This states the exact local constructor image, not a completed generalized
root or exported outer-Call inclusion theorem.

## 5. First remaining bound-to-image preservation premise

The native result above proves an included B-derived clause and membership
of its concrete record. The first OPEN parent obligation is preservation of
**B's actual b_R endpoint through its compact/generalized image and the
actual later/current use and Call output**, with the original occurrence,
annotation, provider/use and residual correlations. The actual bound-to-image
route can establish this preservation regardless of which included clause
the projection query selects as its decisive certificate.

Exact selection of p_R's certificate was one attempted proof route. This
note does not establish that selection, but no inspected consumer dependency
makes it necessary for the structural image route. Independent review
identified the earlier claim of necessity as an overstatement; this narrow
repair removes that claim without changing §§2–4 or closing the parent gate.

`constraints/proof/mod.rs:11703–11725` walks the formula bucket's canonical
run, returns at an included exact arm, and records its decisive claimed
incidence. `eval_record_memo` stores this incidence (11547–11577);
`resolve_record_evidence` materializes that selected certificate
(11580–11610; 6268–6330). A ReplayConjunction evaluates its premise
**record summaries**, not a request for a designated source origin
(11735–11763). The scoped scheme query returns this decision/evidence for
the concrete record (`constraints/structural_kernel/access.rs:871–894`).

Thus the implication justified so far is:

```text
an included B-derived clause at b_R
  => b_R is in the actual successful Q_M(R).
```

The required continuation remains unproved:

```text
B's actual endpoint b_R is in Q_M(R)
  => its actual compact/generalized/use image preserves B's contribution
     on the correlated route to the later/current outer Call output.
```

No uniqueness or canonical-order premise for all included clauses of b_R
has been proved. Such a premise would be relevant to the attempted exact
certificate route, but it is not required to pass b_R's actual endpoint to
collection. The recursive route can add derivations to the same concrete
record; that coalescence does not change the endpoint consumed from that
record. The forward image proof must follow this actual B-to-b_R-to-image
construction, rather than identify origins solely by an equal E head. This
note neither asserts a different decisive arm nor substitutes a manually
preferred certificate for an actual consumer input.

The following downstream source facts make this a concrete seam rather
than an undefined “generalization problem”:

1. `compact/collect/mod.rs:848–879` receives the actual selected entries,
   then maps them to `entry.bound.clone()`. Thus membership of b_R passes
   its actual endpoint to compact lower collection regardless of the chosen
   included clause. Its record identity, reason and projection evidence are
   not fields of that bound. This supports a forward structural image proof;
   evidence erasure does not itself show contribution loss or require recovery
   of the decisive certificate. §4 proves the local concrete-row image. The
   unproved continuation must carry that image through the complete actual
   compact/generalized/use transformations, with its source correlations.
2. The separate generalized-witness owner does capture a selected
   `BoundClaimProjectionProof` when it visits a qualified positive Var
   (`generalize/provenance.rs:219–280`). However its positive Function
   branch visits the argument and deliberately skips the root return,
   argument Effect, and return Effect when `path.depth() == 0`
   (309–338). Since f_G is the root Function just proved, this owner does
   **not** register p_R at a root FunctionReturnEffect path. A nested
   Function witness cannot be substituted for this skipped root path in the
   attempted recorded-witness route. This omission does not establish that
   the structural image route needs such a witness.
3. `analysis/session/instantiate.rs:54–82` captures these witnesses,
   finalizes the generalized compact root, records the witnesses, and
   installs the exact definition scheme. `generalize/provenance.rs:26–84`
   explicitly leaves whole-scheme coverage incomplete. The later actual
   use collects the recorded witness paths and creates derivations only
   for the projected mappings (`analysis/session/instantiate.rs:389–409,
   447–490`). These owners provide no automatic root-return fallback.

These certificate/provenance facts characterize one attempted route; they
are not prerequisites imposed on the alternative forward image proof. No
actual consumer dependency on exact p_R certificate selection has been
proved. Relabeling b_R as Independent supplies neither route. The known
downstream structural operations preserve already materialized E
keys in their local cases: variable rewrites and sandwich traversals
(`generalize/simplification.rs:100–152,283–367`), stack-weight pruning
(`generalize/core/prune.rs:504–557`), row finalization
(`compact/finalize.rs:641–689`), and consistent Function/Row cloning
(`instantiate.rs:788–808,832–845`). Those facts do not supply the missing
source-qualified bound-to-image map over the complete selected root's
transformations, root POPs, publication and use. Establishing that map may
discharge the bounded preservation claim without storing p_R's certificate.

For the real outer reference, lifecycle retains its parent/target/use
(`analysis/session/lifecycle.rs:1092–1101`). SCC selection distinguishes
quantified InstantiateUse from actual open routes (`scc.rs:266–288`).
The relevant consumers read G's actual installed scheme or connect its
actual open root (`analysis/session/instantiate.rs:4–11,342–519`), then
Function comparison emits the selected provider's return Effect
(`machine/propagate.rs:257–263`). None permits replacing that provider with
F_final reconstructed independently of the actual publication/selection.
Outer `K_O <: O` forwarding at `expr/tail.rs:615–627` alone does not prove
the missing B-return image route. No outer output inclusion is concluded here.

## 6. Result, parent gates, and economy audit

Claim class: **bounded native source-to-selected-return derivation**, with
an exact remaining bound-to-compact/generalized/use preservation premise. Under the frozen
normal-constructor hypotheses, B's actual E-row derivation extends from T
to R with a registered included ReplayConjunction, and the actual final
Function admitted at the public root has return Effect R. Its Function and
the concrete R lower are members of actual successful scoped scheme queries.
This solves an incoming-side/skeleton-owner question left open by the
preceding reviewed note; it does not assume a fresh allocation at T-to-R,
same-level recursion, a control scheme or a generic replay-completeness law.

The same correlated B derivation is retained at the native bound/claim
owners through R. Preservation of its actual bound-to-generalized return
image and current/later outer Call consumption remains unproved. Exact
decisive certificate correspondence is an unproved attempted route, not a
necessary parent premise established by this note. No emitted
row loss, source rejection, execution result, or accepted counterexample has
been produced. Absence of a root-return witness is not a proof of semantic
row loss, and a surviving nominal head alone is not the requested complete
identity/lineage result. Original universal H, complete Call, soundness,
required principality, successful acceptance and production/cutover gates
remain OPEN with their original domains and owners.

Economy audit: this packet changes the method at a concrete owner by proving
the actual named-self allocation, construction order, first incoming R side,
Direct claim, both replay orders, and final public Function. It does not
repeat an isolated row valuation or a general transitivity assertion. The
remaining A/B preservation obligation cannot be discharged by another
equivalent set/head lemma. Explicitly recovering missing root-return source
provenance from compact bounds is D reconstruction debt; it does not permit
narrowing H, adding a new annotation restriction, or inventing an inference
edge. A constructive source-to-transformation proof may avoid a runtime
record change and exact certificate selection, but it must establish the
actual correlated bound-to-image route.

One next action: the primary assign the localized forward image proof at
`compact_scheme_lower_bounds` and the actual compact/generalize/finalize/use
constructors: carry B's actual b_R endpoint and its local §4 image through
that route to the outer Call output. Use exact certificate correspondence
only if an actual consumer dependency requires it. Consume §§2–4 as
established producer evidence, preserve all
original quantifiers, and stop at an authentic exclusion/loss or that map.
No new job, instrumentation permission, implementation strategy or semantic
decision is authorized by this note.

## 7. Checks, dependencies, and resource use

Static immutable `git show`, `git grep` and `git ls-tree` reads, bounded
repository note reads, SHA-256 dependency snapshots, and leased-document
whitespace/local-link checks only. No Oracle invocation, build, Cargo/test,
executable inference model, measurement, network request, Git mutation,
shared-record change, specialist contact or delegation occurred. A guessed
`structural_kernel/access.rs` path was absent; its actual
`constraints/structural_kernel/access.rs` owner was then located and read.
No inference evidence is claimed from shell success.

Input dependency hashes are recorded in the final commit packet below. The
parent reports independent clean review of the two frozen input artifacts;
this producer does not independently certify them or this continuation.
Independent review found the major certificate-necessity overstatement
described in §5. This continuation is narrowly repaired and frozen for
primary-assigned delta review; no clean review or theorem closure is claimed.

Wall-time ceiling: 45 minutes. Start: 2026-10-11 23:56:09 UTC. The primary
requested freeze at this bounded result; no further proof expansion followed.
Final freeze time and static-check results are recorded below. At most
three lightweight static shell reads ran concurrently; no CPU-intensive
process or inference process ran, and sample count is zero. CPU/RAM were not
instrumented. Requested runtime: `gpt-6.1-sol` / `high`; actual runtime
model/effort metadata were not exposed, so observed settings are unknown.
No Astra escalation was used.

## 8. Primary commit packet

- Exact leased changed path: `notes/theory/2026-10-12-same-family-handler-recursive-return-proof.md`.
- Primary input checkpoint: `7b663d1bb`; previous producer's Y3 source baseline
  remains `0ef6b49ef401df9fa24e94007869d0c03fc80cc2`.
- Immutable Oracle dependency: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Frozen dependencies (SHA-256):

  | Input | SHA-256 |
  | --- | --- |
  | preceding reviewed proof | `d4d77622765d986cb46cbbe0b79fdfa6b18d9099ec53129c877b4cfc0e6f367f` |
  | clean-reviewed source-route input | `5b797e286e5ce787e31d4a63a2a70981f03c0b3d1077677cfd4c216c223efa70` |
  | original H attempt | `686d0970affd4c16aa82d87156fdae96ee6a48548a886212059d824e53651a48` |
  | global H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
  | annotation hygiene | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
  | attachment/admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
  | residual lineage | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
  | complete Call | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
  | top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

  No input dependency was edited by this leaf; final dependency comparison
  and leased-document checks are recorded below.
- Review: independent compiler-referee review found one major overstatement,
  repaired narrowly and delta-reviewed closed with no new findings. The
  reviewer confirmed the T-to-R/Direct-claim construction and public Function
  return in §§2–4; §§5–6 now correctly leave the B-bound-to-compact/
  generalized/use image as the first OPEN parent obligation. Prior clean
  reviews remain dependencies, not closure of H.
- Proposed checkpoint message: `research: derive same-family arm row through Oracle recursive return`.
- Shared-record delta for primary/curator: record the completed native
  T-to-R / actual public Function-return slice; retain H OPEN with the
  preservation of B's actual bound-to-compact/generalized/use image above.
  Exact certificate correspondence is only one attempted route. This leaf
  changed no shared record.

Final mechanical checks: the leased document's whitespace, final newline,
fence balance, local link, and draft-residue check passed; all nine frozen
dependency hashes matched the recorded snapshot. These are document checks,
not inference verification or independent proof review. Freeze checkpoint:
2026-10-12 00:17:14 UTC, approximately 21 minutes after packet start and
within the 45-minute ceiling. The final recording added no derivation.

Narrow review repair checkpoint: 2026-10-12 00:20:29 UTC. The major
overstatement was removed: exact decisive-certificate correspondence is an
attempted route, while preservation of B's actual bound-to-compact/generalized/use
image is the first OPEN parent obligation. The structural forward image route
remains available without an unproved certificate-consumer requirement.
No proof expansion or new semantic-source read followed the review packet;
only this leased note was repaired. Post-repair mechanical document checks
passed. Independent delta review closed the finding with no further issue.
