# Cross-level odd/even: forced port extrusion and the remaining reference bridge

Date: 2026-10-12
Status: frozen, unreviewed bounded constructive derivation; parent gates OPEN
Baseline: `264bf0158c986579739964289450bb70cbe57a71`, `research/simple-sub-intrusion`
Exclusive lease: this file; one leaf, no delegation

## 1. Frozen objective, quantifiers and authority

The original parent gate ranges over every supported source program, every
lawful finite native inference/use history at the original lexical, type and
event scopes, and every retained distinct Value extrusion pair `(c,p)`.
The approved graph has actual Value variables as vertices and actual references
in their owned values as edges. Qualification requires both paths `p ->* c`
and `c ->* p` before the equality being justified. The required conclusion is
that selected same-SCC parent/copy equality preserves the joint source typing,
complete Call, effect/attachment/residual evidence and required principality,
and that the compiler's construction and consumer implement that operation.
No bound, comparison, type port, containment, or parent record alone supplies
a graph edge. This packet does not replace or narrow that parent claim.

The local question is whether the following intended source structure supplies
an authentic retained pair and its two reference paths:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

`n_outer` and `n_inner` denote the two distinct binders spelled `n`; the inner
one shadows the outer one only in `even`'s initializer. `odd` is the enclosing
module binder; `even` is the sequential local binder, visible at the outer
final expression after its initializer is published. These scopes remain
fixed. The accepted source-owner incidence result is `even -> odd` and
`odd -> even`. It does not identify either binder with a copied port row.

Governing sections: parent-copy decision **Selected operation and compiler
responsibility**, **Value-reference SCC clarification**, **Retained boundary**;
top-level inference principles §§1–5 and **Evaluation**; local self-recursion
**Selected source behavior** and **Proposed source-to-solver seam**; source
Generalize §§2–4; contextual Function membership §§2–4. Complete Call and
effects remain required; a two-port Simple-sub calculation below is only a
Value constraint calculation, never an erasure or adequacy claim for Call.

Method: hand-derive original Simple-sub generation, insertion, opposite-bound
replay, polar extrusion and use freshening; then follow the corresponding
actual Rust constructors through the first retained copies. No supplied graph
checker, rank argument, `Fam_delta`, `EmittedGenCall0`, static content owner,
or assumed SCC adjacency is used.

## 2. Admission and the Call-bearing analogue

The exact text is not an admitted ordinary Yulang3 HIR/candidate history.
The existing task record identifies both its syntax/indented-body limitations
and the absence of conditional/infix forms in LocalSource. This packet preserves
that limitation and supplies no runtime result for the exact text.

The more discriminating carrier-shaped analogue is:

```yulang
my odd n = { my even n = odd(n); even(n) }
```

Static constructor inspection supports two actual Apply forms: adjacent `(`
selects `call_tail_normalized` (`operator_chain.rs:632–647`), which constructs
`CallTail` (`tails/delimited_tail.rs:19–61`). LocalSource accepts `CallTail`,
requires its single argument child, and constructs `LocalSourceForm::Apply`
with separate callee and argument slots (`module/local_source.rs:529–581`).
The brace block constructor supports sequential local bindings and a final
expression (`:697` onward); the initializer/publication and shadowing owners
are `:322–367` and the Name lookup at `:635–656`.

This is static representability from these constructors, conditional on the
expected recovery-free syntax tree and successful checked formation. No parser,
HIR lowering, candidate solve, build or test was executed on the string. Ordinary
HIR admission is not asserted. The analogue changes the computation by removing
the conditional/arithmetic; it is used to isolate the two Calls, not to certify
the original program.

The earlier spelling `odd n; even n` does not intrinsically omit Apply:
the same LocalSource arm also accepts `MlArgument` and creates Apply. The
explicit parentheses here select the inspected CallTail route unambiguously.

## 3. A complete original Simple-sub constraint derivation

Use the original grammar term with exactly this recursive/nested Call structure:

```text
let rec odd = lambda n_outer.
  let even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

This uses only `Let`, `Lam`, `Var` and `App` in original `syntax.scala:7–14`.
It is an original-grammar structural analogue, not a translation theorem for
Yulang's complete Call. Original reference commit:
`9bae772624c23b52a93c1b226157e16898b4d9db`.

Freeze the store just before the final `in odd` scheme use. Initially all rows
introduced below have empty bounds. `L(x)` and `U(x)` are the actual lower and
upper bound lists; the lists below ignore order where no outcome depends on it.

1. `typeLetRhs(true,odd,...)` at boundary 0 allocates monomorphic recursive
   row `O` at level 1. The outer Lambda allocates formal `A` at level 1.
   The inner nonrecursive `even` initializer is inferred at level 2 and its
   Lambda allocates distinct formal `B` at level 2 (`Typer.scala:48–67`).
2. The inner Name `odd` returns exactly `O`, without scheme freshening. Name
   `n_inner` returns `B`. Its App allocates fresh result `R` at level 2 and
   generates `O <: Function(B,R)` (`:62–72`). The Function has level 2.
3. Since `O` has level 1, `constrain` negatively extrudes the right Function
   to level 1 (`:121–123`). Function arguments reverse polarity, results
   preserve it (`:144`). The actual polar memo keys are `(B,+)` and `(R,-)`.
   It creates distinct level-1 rows `C` and `D`, with origins `(C,B,+,1)` and
   `(D,R,-,1)`. Positive extrusion inserts `C` into `U(B)` and copies empty
   `L(B)` to `L(C)`; negative extrusion inserts `D` into `L(R)` and copies
   empty `U(R)` to `U(D)` (`:146–154`). The rewritten demand is
   `O <: Function(C,D)`, inserted into `U(O)`. `L(O)` is still empty, so this
   insertion activates no lower/upper pair.
4. The inner Lambda has type `Function(B,R)`. Its local scheme boundary is
   1. The outer Name `even` invokes `freshenAbove(1,Function(B,R))` at level
   1 (`:55,:81–83,:166–188,:201–202`). One shared memo creates `B'` and `R'`
   at level 1, retaining the old level-1 anchors `C,D`. It restores
   `U(B')=[C]` and `L(R')=[D]`. These use copies are not extrusion events.
5. The outer Name `n_outer` returns `A`. Its App allocates result `S` at
   level 1 and generates `Function(B',R') <: Function(A,S)`. Function
   comparison generates `A <: B'` and `R' <: S` (`:106–108`). With equal
   levels, left-variable insertion stores `B'` in `U(A)`. Inserting `S` in
   `U(R')` replays its already present lower `D`, generating `D <: S` and
   storing `S` in `U(D)` (`:115–117`). No new extrusion occurs.
6. The outer Lambda produces `Function(A,S)`. Recursive-let completion
   generates `Function(A,S) <: O`, inserts this into `L(O)`, then replays
   `U(O)=[Function(C,D)]` (`:52,:118–120`). Function comparison generates
   `C <: A` and `S <: D`, stored respectively in `U(C)` and `U(S)`. These
   rows have level 1, so neither comparison extrudes.

The entire Value-variable store at this cut is therefore:

| Row | Level | Lower bounds | Upper bounds |
| --- | --- | --- | --- |
| O | 1 | Function(A,S) | Function(C,D) |
| A | 1 | empty | B' |
| B | 2 | empty | C |
| R | 2 | D | empty |
| C | 1 | empty | A |
| D | 1 | empty | S |
| B' | 1 | empty | C |
| R' | 1 | D | S |
| S | 1 | empty | D |

This is a finite native-rule derivation with no supplied starting bounds.
The original implementation does not retain selected Yulang `Parent` records;
the displayed parent origins are read directly from its fresh-copy creations.
The final Name `odd` uses the outer boundary-0 scheme and coherently freshens
its reachable generic graph at level 0; that is also use freshening, not a
new extrusion-parent creation.

For clarity only, the bound-payload projection of this store contains the
cycles `C -> A -> B' -> C` and `D -> S -> D`. Neither cycle contains its
original extrusion parent `B` or `R`. These are **not** approved Value-reference
SCCs. In particular, the type inequalities `D <: S <: D` do not equate `R`
with `D`, nor make `B'` an extrusion child of `B`. No source-qualified
counterexample or qualifying SCC is obtained from this store.

## 4. Actual candidate construction up to the two retained Value pairs

Now use names for actual candidate allocation outputs of the carrier-shaped
analogue; no numerical row IDs or equality of unrelated rows is prescribed:

| Endpoint | Owning construction | Level |
| --- | --- | --- |
| O | module definition root for odd | 1 |
| A | outer formal n_outer | 1 |
| E | local initializer Lambda root for even | 2 |
| B | inner formal n_inner | 2 |
| U | inner module Name odd occurrence | 2 |
| R | inner Apply result | 2 |
| V | later local Name even occurrence | 1 |
| S | outer Apply result | 1 |

These levels follow from `candidate_source.rs:253–278`: root traversal starts
at 1; Lambda retains the traversal level; a block initializer increases it
to 2 (`:294–307`), while the final expression stays at 1. Component/parameter
maps are installed by `initialize_candidate_source_levels` (`:532–557`).
Definition roots are initially allocated at 1 (`lib.rs:10047–10114`). Parameter
Names alias their actual formal endpoint (`candidate_source.rs:209–216`), so
the inner argument is B and the outer argument is A, despite the same spelling.

Conditional operational scope: the expected LocalSource has successfully
formed; allocations and the selected normal source actions complete without
resource failure; no annotation or foreign constraint changes these fresh
Value ports. This does not assume any owned-reference graph. The derivation
characterizes those authentic constructors; it is not a recorded execution.

The nested Name odd emits a Module action with the enclosing definition's
parent ordinal (`candidate_source.rs:375–378`). Its endpoint pass resolves
the target to the same module odd and retains its root, occurrence, use row
and level jointly (`lib.rs:1275–1327`). Thus this use is the module's internal
self use, even though lexically inside even. The component driver activates
member roots/internal uses before executing schedules
(`candidate_scheme.rs:861–883`). Module execution selects the open route
(`candidate_source.rs:672–677`), which admits `O <: U` (`lib.rs:15765–15787`).
The row/row dispatcher stores O in U's lower side because `level(O)<level(U)`
(`candidate_extrusion.rs:817–825`). This route allocates no fresh Value copy.

The inner Apply's actual recipe retains callee U, argument B, result R and
their effect endpoints (`candidate_source.rs:394–411`). The native admission
constructs the negative four-port demand

```text
F_minus(B, argument_effect_2, invocation_effect_2, R)
U <: F_minus(B, argument_effect_2, invocation_effect_2, R).
```

Both Effect ports remain in the actual term (`shadow_apply.rs:1331–1383`).
The demand fits U's level. Inserting it on U's upper side activates the already
stored lower O through `candidate_apply_value`/`candidate_replay_bound`
(`candidate_extrusion.rs:809–841`), reaching the structural comparison
`O <: F_minus(...)`. This is activation by the opposite-bound consumer,
not a claim inferred from stored constraints alone.

The structural guard negatively extrudes this demand to O's level 1
(`lib.rs:12412–12454`). `candidate_extrude` flips the argument's polarity,
retains the result's polarity, and visits both Effect ports separately
(`candidate_extrusion.rs:224–249`). Its wrong-level Value visits allocate:

```text
C at level 1; retain Parent(copy=C, parent=B, polarity=+, target=1)
D at level 1; retain Parent(copy=D, parent=R, polarity=-, target=1)
```

They insert `B <: C` on B's upper side and `D <: R` on R's lower side,
with initially empty selected Value bounds copied to C and D
(`candidate_extrusion.rs:94–163`). Parent retention is the actual call to
`retain_extrusion_parent`, whose typed record has copy, parent, polarity and
target (`candidate_intrusion.rs:23–28,:171` onward). Function reconstruction
keeps all four mapped ports. The rewritten demand is enqueued and ultimately
stored as O's upper Function bound. Effect copies may also be created by the
same traversal; they are separate typed events, not additional Value parents.

At this cut, **the actual retained Value parents are B and R**. Neither O nor
E has been copied by this event. An E/O binder SCC therefore does not even
name the two parent/copy pairs just constructed.

Afterward, the inner Lambda forms a positive four-port Function using B and R
and admits it against E (`lib.rs:11233–11370`). Installation records the live
E root and boundary 1, without extrusion
(`candidate_scheme.rs:1316–1338`). The later local Name captures this live
graph and uses one shared map to freshen generic E/B/R at level 1 while
retaining level-1 C/D (`:1356–1382,:981–1019`). Captured bound orientation
is restored by `begin_candidate_fresh_bound` (`:1221–1266`); this must not be
replaced by a new independently chosen row/row orientation. The fresh root
is then linked to V (`:1516–1519`). These are use copies with no retained
extrusion-parent creation in that allocation branch.

The outer Apply demands a Function with argument A and result S at level 1.
Its fresh callee Function leads to the corresponding argument/result
comparisons, with both Effect comparisons retained
(`lib.rs:12493–12536`). Later block/root forwarding may add bounds; it does
not retroactively turn E's use-fresh root into C or D. This packet establishes
the first forced pair prefix and the use distinction, not every subsequent
candidate worklist/effect/SCC transition.

## 5. Exact intended-source Call skeleton and the first missing law

For the original example, the inner and outer binder/formal levels are the
same. If the arithmetic source constructor law realizes `n_inner - 1` as
an ordinary App result `T` at level 2, the inner call generates
`O <: Function(T,R)` with fresh R at level 2. Its negative extrusion has
`(T,+) -> C_T` and `(R,-) -> D_R` at level 1; selected bounds of T may force
additional polar copies. R's result copy is forced by its freshly allocated
level, even when the argument type is already ground. A later conditional
consumer can add bounds to R; it cannot justify treating the previous App
result as the even binder root. The outer call uses even's published local
scheme at level 1, its outer arithmetic argument, and a fresh outer result S.

These are conditional rule instances. No native lowering law for the original
conditional/infix source was established here. In particular, no primitive
minus/comparison signature, branch join, or synthetic conditional is invented
to claim a complete exact-source store. The first actual-source gap for the
literal text is admission/generation for those constructors.

For the Call-bearing representable analogue, that gap is bypassed by a genuine
smaller source structure, and the retained port pairs above follow. The next
missing premise is exactly:

> Given the actual inner Apply input `(callee=U, argument=B, result=R)`, its
> resolved target O, and the Lambda/root introduction `(root=E, formal=B,
> body=R)`, what semantic Value content does R own, what references does that
> content introduce or forward, and how is that same jointly scoped content
> assigned to the retained negative copy D? Correspondingly, what does B own
> and how does the retained positive copy C transport its actual reference
> targets? Published even uses must specify binding identity versus the same
> use's fresh description identity jointly, preserving nongeneric anchors.

Neither actual demand construction nor the above bound operations give these
equations. In particular, they supply neither `B ->* C ->* B` nor
`R ->* D ->* R`. The accepted binder paths `E -> O -> E` have endpoints of
a different kind of construction; equating E with R, O with D, or a scheme
use with an extrusion copy would assume the bridge being requested.

The actual SCC consumer scans both bound sides, Function ports and Effect
dependencies, then compares retained parent/copy component numbers
(`candidate_intrusion.rs:358–488`). It does not consume an established
Apply-result owned-content equation. Its adjacency cannot be declared the
approved Value-reference graph solely because these copies and type cycles
exist. This is a precise construction/consumer boundary, not proof that the
current representation cannot implement the selected operation.

Result: the supplied exact example establishes the accepted cross-level
binder SCC; the Call-bearing analogue additionally forces authentic port
extrusion. **No actual retained pair's approved same-SCC membership or
nonmembership is established.** No soundness counterexample, equality
preservation proof, principality proof, complete Call proof, or cutover closure
is claimed. The original parent gate stays OPEN.

## 6. Obligation economy and next action

The prior type-route reconstruction and separate identity-map approaches both
stopped at owned-content/target transport. This pass changes the evidence by
deriving a concrete forced native extrusion rather than adding another rank
or graph-copy lemma. It still leaves that semantic equation untouched.

Correct approved SCC qualification and equality preservation remain A/B.
Recovering callee/argument/result/target identities from later bounds is D;
the actual Apply/Name/Lambda records already retain them. Keeping canonical
evidence can remove that recovery debt, but it cannot decide what R owns.
A mathematical copy-graph lemma would remain conditional until this source
law is supplied. No parent obligation is reclassified or retired.

One next action: the primary's source/Value-construction authority resolves
the displayed Apply-result/formal owned-content and copy/use transport law
using these exact registered ports, then hands its consumer correspondence
and qualifying equality preservation to their existing owners. No further
equivalent SCC derivation is proposed before that law is available.

## 7. Checks, resources and dependency snapshot

Only bounded source/rule reads, clock lookup, SHA-256 capture and this leased
note write were used. Branch/commit identities were inspected by reading
`.git/HEAD` and the selected loose ref, without invoking Git. The Yulang ref
matched the full baseline above; the reference ref matched its supplied commit.
The assigned transport-note locator under `notes/theory/` does not exist; the
actual note is `notes/progress/2026-10-11-value-reference-transport-proof.md`.
Initial combined captures that truncated were reread in decisive narrow windows.

Zero tests, builds, Scala execution, Oracle runs, executable probes,
measurements, Git operations, shared-record writes or delegated jobs. Reads
and proof construction stayed within the 45-minute packet; exact CPU, RAM and
reasoning elapsed time were not measured. The primary remains verification
and integration owner. Requested normal policy route: `gpt-6.1-sol/high`;
effective model/effort metadata is unavailable to this leaf, so observed
runtime settings are unknown. No Astra or hot-reload claim. No independent
review has occurred.

Direct dependency SHA-256 snapshot (no dependency was edited by this leaf):

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/progress/2026-10-11-value-reference-transport-proof.md` | `4081b6ef45c21007ce2246840e64538b9bddaf4c30f453fb8a88350317ab6789` |
| `notes/theory/2026-10-11-mutual-recursion-native-value-reference-bridge.md` | `9f83f10566b11861a8b8079efff3bcb7dabd153287583d00e6ba71e50c988caa` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs` | `349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference `syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |

## Commit packet

Exact leased/changed path:
`notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md`.
Baseline: `264bf0158c986579739964289450bb70cbe57a71`; reference baseline:
`9bae772624c23b52a93c1b226157e16898b4d9db`. Changed dependency hashes: none
caused by this leaf; listed live inputs are the frozen read snapshot, with
baseline-content comparison/integration retained by the primary. Claim/review:
unreviewed finite original derivation and conditional native constructor
characterization, no theorem/implementation closure. Checks: exact source
reads, identity/hash inspection and note integrity only; no tests/builds.
Proposed checkpoint message:
`research: derive odd-even Call port extrusion and isolate its reference bridge`.
Shared-record deltas left to the primary/curator: record the two forced native
port parents, distinguish E/O binder SCC from C/B and D/R qualification,
correct the claim that the MLArgument analogue intrinsically omits Apply,
and preserve exact-source admission, Value ownership/transport, equality,
complete Call, hygiene and principality as OPEN. No shared record was edited.
