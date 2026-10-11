# Ancestor call, genuine extrusion, and the returned fresh descendant

Date: 2026-10-11
Status: **superseded for semantic SCC conclusions**. The independent review
covered only the bounded native payload construction below, not the user's
semantic value-reference graph; the parent theorem remains open.
Original all-source normal-inference/intrusion theorem: **OPEN**.
Compiler baseline: `9d2bdce2f9c1cb4d619f4c5889b84ebd5e48c009`.
Direct compiler/HIR dependencies are unchanged from
`330d5432aff4b1f9655d501e17a9eefb7e75e098` (read-only path comparison).
Ordinary Simple-sub reference: `9bae772624c23b52a93c1b226157e16898b4d9db`,
`/home/momota1029/rust/simple-sub-reference`.
Exclusive lease: this file; leaf, no children, compiler writes, executable
probes, tests, builds, Oracle, Git mutation, or shared-record writes.

## Frozen question, source, binders and exclusions

The primary's source-context correction fixes a parameterized **local**
ancestor in an enclosing Block:

```yulang
my host z = {
  my outer x = {
    my g y = outer y;
    g
  };
  outer
}
```

`outer` in `g` is the active ancestor's local identity; `y` is `g`'s formal;
the final `g` is a later use after publication. Keep these distinct binders,
their scopes and occurrences. There are no annotations, operations, shadowing,
mutual groups, synthetic bounds or custom contexts. The smaller displayed
`my outer x = { my g y = outer y; g }` is interpreted here as that local binding
within `host`, not as a module definition. Module references use a separate
scheme route and are not covered by the local-self theorem.

Question: does this source force a retained Value extrusion parent/copy pair
to enter the selected Value-reference SCC? In particular, after descendant
publication, does the required return path reach the **original** extruded
parent P, or only its ordinary fresh-use instance P*? Does the original source
judgment require identifying P* with P?

Bounded claim: for the ordinary successful native constructor trace of this
fixed source, the ancestor call genuinely extrudes the descendant formal and
call-result rows. The ancestor's returned descendant produces a cycle through
the shared extruded result copy and the fresh call-result instance. That
cycle does not contain the original retained parent. The ordinary reference's
actual freshening and arrow inequalities require the shared approximation,
not P*=P. This eliminates this candidate as the desired parent/copy SCC
witness. It neither refutes the all-source theorem nor proves general
soundness, principality, complete Call, hygiene or intrusion adequacy.

Quantification is over the fixed source identities and normal owning action
schedule, up to alpha renaming, with successful allocation/admission and
completion of the named drain children. These operational success hypotheses
do not assert a complete normal-progress theorem. The payload identities,
copy provenance, capture decisions and finite replay consequences are derived
below rather than assumed. No unrestricted future source continuation or
failed-state reuse is covered.

## Governing sources and first source constructor

Exact authority:

- `notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source
  behavior”, “Proposed source-to-solver seam”, “Implementation checkpoint”.
- `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation
  and compiler responsibility”, “Value-reference SCC clarification”.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–3,
  “Evaluation”, “Authority and integration”.
- `rules/compiler-engineering.md`, “Natural compiler behavior and
  proof-obligation economy”, “Deterministic Simple-sub inference”;
  `rules/agent-orchestration.md`, “Proof delegation and decomposition”,
  “Model routing and Astra escalation”; `rules/research-lab.md`, “One semantic
  baseline, explicit dependency invalidation”, “Evidence quality and stopping
  unproductive loops”; `rules/git-concurrency.md`, “Disjoint-file mode”;
  `rules/design-authority.md`, “Authority order”.

The reviewed source-required note
`2026-10-11-source-required-value-parent-copy-cycle.md` supplies the previous
lexical-return result and remaining extrusion seam. The Value-reference note
`2026-10-11-simple-sub-value-reference-scc.md` supplies the actual reference
representation and distinguishes its bounded trace from parsed source.
Their conclusions are inputs, not evidence closing this new bridge.

HIR `module/local_source.rs:329–362` publishes the parameterized initializer's
local binder temporarily before its formal and body. Thus `outer` is still in
the lexical stack when `g`'s body forms; lookup at `:637–647` resolves that
Name to outer's `HirLocalId`. Publication at `:366–373` restores and publishes
`g`, leaving the enclosing active binder visible. Application tails become
`LocalSourceForm::Apply` at `:524–563`; `outer y` needs no new source rule.
Parameter `y` resolves to its own `HirParameterId` and becomes the actual
parameter endpoint (`candidate_source.rs:209–216`), not a fresh Name Value.

Deleting outer's header parameter changes the first rule: `count == 0` does
not install the temporary self binder. With no same-name module definition,
the inner Name is Unresolved. That variant is outside the completed local
self-binding slice. This is a recorded carrier boundary, not a restriction
invented to prove this packet.

## Ordinary reference: actual extrusion and required sharing

Translate the relevant local shape with the reference's native recursive lets:

```text
λz. let rec outer = λx. (let rec g = λy. outer y in g) in outer
```

For comparison with native levels, type the host body at reference level 1.
Then outer placeholder A and formal X have level 2; g placeholder D, formal
Y and call-result P have level 3. `typeLetRhs` allocates the recursive
placeholder at the next level and installs it monomorphically
(`Typer.scala:48–55`); `SimpleType.instantiate` returns that very object
(`:205–207`). The inner ancestor reference is therefore A, not A*.

The application constructor (`:68–72`) emits:

```text
A <: Function(Y, P)
```

The Function's level exceeds A's. `constrain:115–125` reaches negative
extrusion at target 2. `extrude:131–159` flips polarity in the domain and
preserves it in the result. It allocates:

```text
C = extrude(Y,+,2)       Y.upper += C    // retained-reference analogue Y → C
Q = extrude(P,-,2)       P.lower += Q    // retained-reference analogue P → Q
A.upper += Function(C,Q)
```

Y and P initially have no Value bounds, so C has no copied lowers and Q has
no copied uppers. **The ancestor A is not the extrusion parent.** It is the
older row receiving the copied demand. Scala does not retain genealogy;
the native owner below records these actual two creation events.

The descendant initializer gives D.lower = Function(Y,P). Its scheme limit
is 2. The final `g` calls `freshenAbove(2,D)` (`:166–185,201–202`), with one
joint fresh map:

```text
D ↦ D* at 2; Y ↦ Y* at 2; P ↦ P* at 2
C ↦ C; Q ↦ Q
D*.lower += Function(Y*,P*)
Y*.upper += C
P*.lower += Q
```

Freshening copies **both** bound lists of quantified rows but stops at C,Q
whose levels equal the limit. It does not identify P* with P. Typing outer's
initializer then emits Function(X,D*) <: A. Replaying A's demand produces
C <: X and D* <: Q. At equal levels the latter installs Q in D*.upper and
replays D*'s lower Function into Q.lower:

```text
Q.lower += Function(Y*,P*)
```

Consequently Q → P* → Q is an actual occurrence cycle. P → Q is real,
but neither Q nor P* points back to P. This is direct execution of the native
reference constructors, not a rank-invariant proof or arbitrary restoration.

## Native source trace: identities, levels, writes and consumers

All native solver locators below are under `crates/yu-solver/src/`.
The source traversal starts at 1, increases levels for Block initializers,
and preserves a Lambda's level in its body (`candidate_source.rs:251–298`).

| Handle | Actual owner | Level |
| --- | --- | --- |
| A | outer initializer Lambda root | 2 |
| X | outer formal x | 2 |
| B | outer body Block result | 2 |
| D | g initializer Lambda root | 3 |
| Y | g formal y | 3 |
| N | outer Name used as call callee | 3 |
| P | Apply `outer y` result | 3 |
| J | final published-g Name in outer body | 2 |
| C | positive Value extrusion copy of Y | 2 |
| Q | negative Value extrusion copy of P | 2 |

1. `Work::Initializer` keeps A in `active_initializers`; the ancestor Name
   emits `Action::Link(A,N)` (`candidate_source.rs:294–298,381–385`). Its
   executor at `:657–661` admits A <: N. Row selection
   (`candidate_extrusion.rs:815–830`) physically installs A in N.lower:
   **N → A**. This lexical link is not extrusion.

2. The Apply action retains the exact callee N, argument Y and result P
   (`candidate_source.rs:392–413`). `shadow_apply.rs:1332–1383` constructs
   the negative four-port demand with Y as argument, the argument's actual
   computation Effect, a fresh invocation Effect at 3, and P as result.
   Its `NativeInterface` retains the original callee/argument/result/demand
   and the invocation/application Effect handles. Admission at `:1389–1403`
   drains N <: demand. There is no Value copy at N's level 3. Physical
   insertion gives N.upper containing that Function, hence N → Y,P.

3. N already has lower A. `candidate_replay_bound:763–802` enumerates it
   against the newly admitted upper demand and creates the concrete
   A <: demand replay task. Dispatch (`lib.rs:12418–12490`) extrudes the
   structural upper at A's level 2 with negative polarity. The greater-level
   row branch at `candidate_extrusion.rs:83–124` allocates C,Q and invokes
   `retain_extrusion_parent` with exactly `(C,Y,+,2)` and `(Q,P,-,2)`.
   It physically inserts C into Y.upper and Q into P.lower. Their selected
   copied Value lists are empty. Function reconstruction at `:325–355`
   uses C in the domain and Q in the result, while retaining/remapping the
   real Effect ports. The rewritten admission installs the copied negative
   Function in A.upper. Actual Value edges: **Y → C**, **P → Q**, **A → C,Q**.

4. g Lambda admission (`lib.rs:11233–11362`) constructs the positive
   four-port Function from Y, its actual entry/return Effects, and P, then
   installs it in D.lower. No Value port has a higher level than D.
   g installation stores `{root=D,boundary=2}`
   (`candidate_scheme.rs:1315–1334`). Installation creates no reference or
   extrusion event.

5. The final g Name is a Local use. Capture from D
   (`candidate_scheme.rs:691,726–794`) reaches the Function's Y,P, then
   Y.upper's C and P.lower's Q. At `:300–326`, D,Y,P are local; C,Q are
   shared. Expansion stops at shared rows (`:566–570`). In particular it
   **does not traverse P's extrusion genealogy to P again from Q**, and
   N is not a Function Value port or a bound of D,Y,P. Context payload
   expansion at `:762–784` interns Effect tails, not hidden Value callee
   references. Thus no provenance/context shortcut captures N or A as a
   Value dependency from this root.

6. Fresh preparation (`candidate_scheme.rs:1008–1021`) jointly maps D,Y,P
   to D*,Y*,P* at 2 and retains C,Q. Function reconstruction at `:1141–1157`
   preserves all four mapped ports. Bound restoration at `:1227–1266`
   preserves captured owner and side:

   ```text
   D*.lower contains Function(Y*, effects*, P*)
   Y*.upper contains C
   P*.lower contains Q
   ```

   These allocations call `fresh_value_at_level`; they do not retain
   `(P*,P)` or `(P*,Q)` as an extrusion pair. Captured relation/evidence
   transport is retained separately; it is not a Value payload edge.

7. The Local cursor admits D* <: J after restoration
   (`candidate_scheme.rs:1500–1519`). Equal-level insertion stores J in
   D*.upper and replays its lower Function into J.lower. Block finishing
   emits J <: B (`candidate_source.rs:459–467`,
   `shadow_apply.rs:1327–1330`), stores B in J.upper, and replays the same
   positive Function into B.lower. Thus **D* → J**, **J → B**, and each
   of D*,J,B contains Value ports Y*,P*. No new Value extrusion is needed.

8. Outer Lambda admission installs Function(X,effects,B) in A.lower.
   Replaying it against A.upper's actual copied demand emits four children
   (`lib.rs:12493–12541`): Value **C <: X**, the argument Effect child,
   the result Effect child, and Value **B <: Q**. The Effect children remain
   real obligations; this note does not infer their full semantics by
   deleting them. Equal-level stores give C.upper containing X and B.upper
   containing Q. B's already installed positive Function then replays into
   Q.lower, preserving its argument Y* and result P*.

The actual row-reference cycle is therefore:

```text
Q → (positive returned-g Function) → P* → Q
```

B,J,D* also point into that cycle. A reaches it through B and Q. Original P
points into it through Q; original Y points to C. The cycle has **P*** as the
returned Function's result port, not **P**. No new comparison or reference to
P is manufactured by calling P* its fresh instance.

### Activation evidence and ordinary original-call obligation

These replay statements are not inferred from stored bounds alone.
`candidate_insert_bound_with_evidence:445–501` records the admission origin
before appending the physical bound. `candidate_replay_bound:763–802` supplies
the lower/upper origin keys; `candidate_context_begin_replay:2911–2987`
enumerates their actual fibers and retains the concrete task. The scalar
consumer queues the typed child (`candidate_context.rs:3060–3101`); actual
dispatch owns structural extrusion and the four Function children. Fresh
restoration physically installs with its transported evidence and saves the
opposite count (`candidate_extrusion.rs:659–677`); its cursor drives the
actual live-index child replay at `:697–760`. Outer Lambda's lower bound and
the copied upper demand both have real origins, as do B's lower Function
and its new upper Q. They therefore activate the two critical products in
step 8 under the stated completed-drain hypothesis.

Do not add an unsupported later rule saying every original pair must be
reprocessed into a direct lower Function on N or a direct B lower on P.
The required original call is already carried by the jointly retained
inequalities:

```text
Y <: C                 Q <: P
A <: Function(C,Q)
```

For the reference Value preorder, arrow contravariance/covariance imply
Function(C,Q) <: Function(Y,P), hence the original A <: Function(Y,P).
For the fresh descendant, Y* <: C and Q <: P* give the corresponding
A <: Function(Y*,P*). Later step 8 supplies B <: Q, so both original and
fresh call results accept the same actual outer result through that shared
Q. This uses one constructor/capture map and one shared C,Q pair, without
choosing independent argument/result witnesses. It does **not** claim
complete Call merely from this Value projection; the original native demand,
Effect slots and Call interface remain their exact separate owners.

The reference extrusion comment (`Typer.scala:135–141`) explicitly describes
these polar copies as conservative approximations within which later
instantiations receive additional constraints independently. Together with
actual freshening above limit 2, this establishes that this ordinary source
judgment does not demand P*=P. Forcing that identification would add a
sharing condition not generated by this source/algorithm trace.

## SCC qualification and faithful controls

The actual scanner follows direct bounds and Function ports
(`candidate_intrusion.rs:390–413,445–468`). It sees Q/P*'s cycle, but pair
qualification separately examines retained creation events at `:477–491`.
Neither retained Value pair (C,Y) nor (Q,P) lies in that cycle. This conclusion
comes from the displayed concrete payloads and creation records, not from a
second rank proof. There is no missing original P reference to recover from
lexical ancestry. Native Effect-only paths do not lead back to Value rows in
this scanner; no Effect SCC adequacy is claimed.

Publishing outer at boundary 1 and using it in host's final expression
freshens its reachable level-2 payload jointly. The original level-3 P,Y are
not reached from A's Value payload in this trace. Ordinary freshening creates
no additional Value parent event. Detailed public host export is excluded.

Two minimal controls retain the source character:

- Alpha renaming changes neither identity resolution nor the operation trace.
- `my g y = outer x` retains the active-ancestor call and returned descendant,
  while isolating result extrusion. Argument X is already at 2, so no Value
  domain copy C is created. P still produces the genuine negative copy Q at
  2; fresh g use maps P to P* and shares Q. The resulting replay again closes
  Q → P* → Q without the original P. This is a static constructor control,
  not a parsed/executed test.

An extra Group around the Apply changes the returned administrative row and
must be traced as its own owner; it is not permission to rename that row P.
No claim for additional nested binding boundaries is inferred from these
controls.

## Exact remaining premise and economy audit

This packet resolves the candidate's actual extrusion seam: real retained
parents exist, but the return path reaches a fresh quantified instance and
the shared approximation. Its semantic Value dependency is represented by
the same shared C,Q inequalities generated by ordinary Simple-sub.
It is not a genuine source-qualified counterexample to the implementation,
nor an existential witness of qualifying parent/copy intrusion.

The universal remaining premise is still the source/operational bridge:
whether every required ordinary source dependency and generalization use is
represented adequately across actual extrusion and qualifying intrusion,
with complete Call, effects, soundness and required principality. A source
construction requiring an original higher-level parent to occur in its
copy's reachable Value payload, or an independently required equality/level
transition producing that qualification, remains to be supplied or excluded
by a full theorem. This fixed program supplies neither.

The earlier rank proof and lexical-return investigation left that premise
open. Applying the existing economy audit before another equivalent attempt:
adequacy needed for correctness/natural inference remains A/B; an arbitrary
copy-family converse without source requirement is C; identifying originals
from lexical ancestry or fresh-use allocation instead of retained creation
facts would be D. Here the constructor facts are already retained, and the
reference's selected freshening is decisive. No new certificate, semantic
layer, source restriction or production change is proposed. Another witness
whose only reverse path is through P* repeats this obstruction.

Next action: the primary should use this reviewed finite witness to target the
remaining source-generalization adequacy premise; keep the parent theorem OPEN.

## Independent review and status

An independent `compiler_referee` reviewed the frozen source identities,
extrusion polarity and parent records, capture/freshening boundary, replay
owners, SCC membership, and the Value-preorder entailment above. It found no
blocking, major, or minor issue in this bounded derivation. The review agrees
that the returned cycle reaches the fresh result instance P* through the shared
copy Q, not the original parent P, and that this source's Value constraints do
not require P*=P. It also confirms that this is not evidence of complete Call,
Effect adequacy, all-source intrusion adequacy, soundness, principality, or
unconditional normal progress. Exact parsing and execution of the displayed
source remain unverified. The original theorem stays **OPEN**.

## Checks, resource use and runtime settings

Static commands: bounded `cat`, `sed`, `rg`, `head`, `sha256sum`; one
read-only `git rev-parse HEAD` and one read-only path-limited
`git diff --name-only 330d5432... 9d2bdce... -- <direct compiler/HIR paths>`.
The latter returned no paths. The primary explicitly instructed this baseline
verification after the initial packet. No Git mutation ran. One leased-file
patch writes only this note. Source locators and hashes are documentary
evidence; no parser, source acceptance, executable replay, probe, test, build,
Oracle, runtime measurement or child ran.

At most three lightweight read shells were concurrent during initial reads;
later owning-source reads were bounded and sequential. Zero heavy processes
and zero measurement samples. CPU/RAM peaks and aggregate wall time were not
measured; no numeric per-leaf resource allocation was supplied. The primary
retains verification ownership and independent review assignment.
Requested routing: normal `gpt-6.1-sol`/high. Role file omits model/effort pins
and registered defaults are Sol/high. Observed model/effort metadata is
unavailable to this leaf and remains **unknown**; no Astra escalation.

### Frozen direct dependency SHA-256

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615  crates/yu-solver/src/term.rs
a2bb01f8b18f25ad5da4fce65be5d9245a531718181bac8913c4ae2eb77979fb  notes/theory/2026-10-11-source-required-value-parent-copy-cycle.md
8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6  notes/theory/2026-10-11-simple-sub-value-reference-scc.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

No dependency file was changed by this leaf. Policy/configuration reads are
not model-execution evidence.

## Commit packet for the primary

- Exact leased path: `notes/theory/2026-10-11-ancestor-call-extrusion-scc.md`.
- Baseline: `9d2bdce2f9c1cb4d619f4c5889b84ebd5e48c009`; direct compiler/HIR
  paths unchanged from `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
- Changed dependency hashes: none; exact inspected hashes above.
- Claim/review status: independently reviewed bounded source/algorithm
  derivation; no established all-source theorem or producer self-certification.
- Checks already run: static owning-source reads, direct path baseline
  comparison, dependency hashes. No executable verification.
- Proposed message: `research: trace ancestor-call extrusion through fresh descendant return`.
- Shared-record delta left to primary/curator: link this finite candidate
  result; record genuine Value parents Y/P, return cycle Q/P*, and absence
  of required P*=P; keep the original source/normal-inference theorem OPEN.
  No task/index/theory-status edits made by the leaf.

## Later graph-definition correction

The user clarified that this payload-only SCC is not the intended graph. The
analysis above follows solver-stored bound payloads but omits source-value
references such as `host → outer`. Therefore the displayed `Q/P*` cycle is an
operational payload cycle only; it is not evidence about the semantic SCC used
by intrusion and does not establish absence of an SCC in the source graph.
Treat all SCC qualification claims in this note as superseded until source
value-reference adjacency is derived from actual source constructors.
