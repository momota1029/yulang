# Oracle direct return: retention through compact simplification

Date: 2026-10-12
Status: frozen producer derivation; independent review pending; original H OPEN
Claim class: bounded source-to-consumer preservation lemma
Y3 baseline: `52f44a1a2bfe9a39c6780b76b8098795b70ace9e`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file; leaf; no delegation or Git mutations

## Frozen statement and boundary

Apply the accepted [projection lemma P](2026-10-12-oracle-direct-return-projection-proof.md)
to the ordinary declaration `my direct(cb: (() -> [tick] ())) = cb`.
The [projection audit](../progress/2026-10-12-oracle-direct-return-projection-audit.md)
is a separate input. Governing authority is annotation-effect-hygiene-integration
§§1–2 and top-level-inference-principles §§1–5. Original
[H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 keeps every original
source-program, occurrence, scope, binder, actual copy/use/call/output-route
quantifier and independent-contribution requirement. H remains OPEN.

**S.** In P's fresh ordinary named-definition construction, take the first
scheme collection of this declaration's public root, after normal native
admission/replay completion and before external uses add constraints to it.
Let x and α be the *same* fresh callback result-Effect coordinate and SubtractId
constructed by its parameter annotation. The complete merged compact root has
one positive x occurrence carrying PUSH α, and one negative x occurrence in
the tail of Row(tick). The simplifier's pinned-interval phase, first
polar/co-occurrence fixed point, structural sandwich phase, and second
polar/co-occurrence fixed point preserve the positive occurrence and its
weight. This proves literal retention at the simplifier's return, before
`generalize/mod.rs:805–834` stack cleanup.

The operational hypotheses are P's normal completed queue/query admission,
fresh allocation without exhaustion, and successful ordinary annotation/name
resolution. The declaration has the displayed single parameter and bare Name
body, with no result annotation, self application, impl requirement or external
use in this snapshot. These identify the bounded constructor slice; they do
not restrict H's source domain or claim that an arbitrary surrounding program
has this snapshot. No runtime execution or numeric-ID census is asserted.

## 1. Actual constructors close the x incidence

Oracle citations are relative to `crates/infer/src/` unless explicitly marked
`crates/poly/src/`. These are constructor and consumer owners, not an assumed
compact input supplied independently of the source.

`lowering/body/mod.rs:2250–2335` enters the definition child level, creates
public root R and selects the named header-argument path. `lowering/expr/mod.rs:309–341`
creates internal self I, passes it to that path, and connects the final wrapped
value V to R. `method_body.rs:55–87` starts **empty** annotation-variable and
closed-effect-row maps. This single annotation therefore cannot reuse another
closed-row coordinate. `annotation/constraints.rs:602–620` allocates fresh x
for the first closed [tick] key. Its positive and negative companions share
that x; they are not separately chosen witnesses.

At `annotation/constraints.rs:363–389,424–470`, the callback companions are:

| Port | Positive A | Negative N |
| --- | --- | --- |
| argument Value | Unit negative | Unit positive |
| argument Effect | empty negative Row | positive Bot |
| result Effect | Stack(PosVar(x), PUSH α) | Stack(NegVar(x), filter tick) |
| result Value | NonSubtract(Unit positive, corresponding pop/filter) | Unit negative |

`()` is the Unit builtin (`annotation/builder.rs:264–280`), lowered as a nullary
constructor (`constraints.rs:771–801`). Connection emits A→c and c→N
(`constraints.rs:124–137`). The Function replay owner
`constraints/machine/propagate.rs:210–267` compares these four ports. The only
nontrivial Effect comparison involving x is its stacked self comparison.
Positive-stack and negative-stack normalization strip the wrappers and retain
the filter check (`propagate.rs:1–60`); the resulting x→x is discarded by
`machine/entry.rs:1092–1110` irrespective of its weights. Thus this comparison
does not admit a semantic lower or upper bound on x. The nullary Unit ports
produce no nested variable relation, and the Bot Effect is trivial.

`register_stack_facts` (`constraints.rs:593–600`) declares x's subtract fact.
`machine/entry.rs:901–940,1820–1866` records subtract-table/provenance/event
information; this work does not insert a type bound or enqueue another
subtype. A filter/check and a subtract fact are not a positive type lower.

The parameter's public/erased call-upper metadata is constructed at
`lambda.rs:1244–1341`; it is not connected merely by allocating its NegId.
The public companion uses its separate public row/filter construction
(`annotation/constraints.rs:475–489`); the erased companion's fresh coordinate
is distinct. A bare local Name performs no application and does not set
`call_erased_used`. Consequently the public-argument constructor keeps
NegVar(c) (`lambda.rs:980–1050`), rather than attaching those call uppers.
They create no additional occurrence of x in the compact root and no x bound.

`lambda.rs:1127–1143` separately allocates skeleton body Value Y, layer output
Value O, body Effect B and layer output Effect D. The annotation makes the
empty skeleton predicate connectable (`lowering/local.rs:133–145`). Its actual
links are Y→O, O→Y and B→D (`lambda.rs:1190–1228`). Its Function lower reaches
internal self I, which the Name body never uses. It has no edge to public R.
Name(cb) gives c and a fresh exact-pure evaluation Effect p; the latter has
only Bot below and empty Row above (`expr/constraints.rs:7–23`).
`lambda.rs:797–808` emits c→Y and p→B, then replaces body coordinates by Y/B.
`lambda.rs:954–978` creates the exported Function at V with argument c,
result Value Y and result Effect B. The enclosing predicate is empty.

Therefore the closure can copy A among c,Y,O and copy N upward along their
native alias links, but cannot create a different callback Effect port. Every
such copied A has the same nested x/PUSH α, and every N has the same x/filter.
The alias relation and its replay weights are empty outside those nested
ports. No other source operation in this slice has x as an endpoint.
Extrusion does not allocate an alternative port here: all targets are at the
definition level, and x was born there. Body p is born in the additional body
child level; p→B extrusion introduces no x connection. P establishes included
A at the *returned* Y, rather than assuming that the original A at c is enough.

## 2. Complete merged port shapes and weights

The compact root below includes the enclosing Function and its **negative**
callback companion. Omitting that companion gives the wrong polarity input.
Write E for empty `CompactType`, U for Unit builtin, and K for value aliases
from the actual c,Y,O component. The native unweighted closure gives Y's
positive component A with its c/O secondary aliases and c's negative component
N with its Y/O secondary aliases. Scheme queries may discard redundant
projection arms; the following x incidence is identical whether such a
redundant alias arm is retained. This does not select a replacement A witness:
P fixes the included A-at-Y used here.

| Complete root location | Merged constructors | Variable component |
| --- | --- | --- |
| public root | one enclosing Function | R and V, positive, empty weights |
| enclosing argument Value | one negative callback N̄ | aliases from K, negative, empty weights |
| enclosing argument Effect | Never | none |
| enclosing result Effect | E | B and p, positive, empty weights |
| enclosing result Value | one positive callback Ā | aliases from K, positive, empty weights |
| N̄ argument Value / Effect / result Value | U / E / U | none |
| N̄ result Effect | Row(tick, tail=E) | x negative in its tail, empty weight |
| Ā argument Value / Effect / result Value | U / empty Row / U | none |
| Ā result Effect | E | x positive, weight Pα |

Pα has filter All, empty floor, one active stack entry Set(tick) at α, and no
pop. Its positive compact occurrence count is one after same-var merging;
the negative tail occurrence count is one. No role roots, recursive bounds,
invariant intervals, neutral constructor arguments or other compact x
occurrences are generated by these constructors.

`compact/collect/mod.rs:746–843` collects a variable side and merges its self
occurrence with the selected bounds. Bound variables become *secondary*
occurrences (`1099–1159`), without recursively following value-alias cycles.
`compact/collect/type_nodes.rs:13–24,84–95` visits the Function and carries
PUSH α into its positive Effect variable. Unit's nullary builtin compaction
discards the separate result-Value wrapper weight (`175–193`); it does not
change the sibling result-Effect port.

The negative stack filter becomes the concrete Row prefix at
`type_nodes.rs:543–585`. With nonempty tick prefix its tail is collected using
the *outer* empty weight, so x's negative tail weight is empty. x has no type
bounds to add any shape or second variable to that tail.

Same-var merge at `compact/merge/entries.rs:124–139` leaves equal weights
unchanged; repeated copies of A merge the same Pα. Function merge at 288–307
merges each corresponding port. `crates/poly/src/types.rs:412–421,565–599`
parallel-unions actual entries: an absent α entry does not supply an Empty
floor. In particular there is no independently supplied unweighted positive
x in this return port. No α floor erasure follows from merging the two Value
aliases with A: Value aliases are not variables in A's result-Effect port.

Stack/Row coexistence collection (`collect/mod.rs:368–407`) can produce neutral
argument constraints, but tick and Unit have zero such arguments. No new
bound is introduced in this graph. The session's merge, role and dominance
restart lanes (`analysis/session/generalize.rs:13–180`) consequently add no x
incidence: there are no owner roles or invariant intervals. Cast collection
(`compact/casts.rs:31–116`) requires constructor-pair entries; this graph has
no such pair. Ordinary header lowering also does not register the impl-member
simplifications read at `session/generalize.rs:418–445`.

The floor passes there operate below the root-level guard, whereas these
variables are at or above the definition child level. Positive alias expansion
(`generalize/mod.rs:283–404,662–699`) adds eligible variable aliases, not Function
bounds; x has no variable lower to expand. It cannot add x to another port.
Thus x incidence and Pα are unchanged at the actual simplifier input.

## 3. Actual groups and every rewrite image of x

The actual session uses simplification boundary root.child and empty
non_generic (`session/generalize.rs:32,476–485`). No local scheme is introduced
by this bare Name. `compact/analysis/mod.rs:506–514` therefore permits the
ordinary local simplifications; retention below does not rely on level
protection.

`occurrence/mod.rs:490–507,543–595` visits all Function ports with argument
polarity flipped, including the nested callbacks. Its `record_group` at
245–269 **intersects** all groups for the same variable and polarity. Weight
contents do not contribute an `AlongItem::Exact`.

The positive x location records exactly `{Var(x)}`. The negative Row records
`{Var(x), Exact(Con(tick,0))}` through `row_along_group` and then separately
visits its singleton tail, recording `{Var(x)}`. The intersection is therefore
also `{Var(x)}`. These are the complete tables for x, derived from both actual
companions, not an assumption that a bipolar variable survives simplification.

| Actual phase | Decision at x | Image of positive x/Pα |
| --- | --- | --- |
| pinned-interval collapse | no intervals | x/Pα |
| first fixed point, each polar pass | x occurs in both polarity sets | x/Pα |
| first fixed point, each co-occurrence pass | both tables singleton; no distinct Var pair, common Exact or interval equality | x/Pα |
| structural sandwich | singleton occurrences have no liftable kind; NoLift | x/Pα |
| second fixed point, each polar pass | same two occurrences | x/Pα |
| second fixed point, each co-occurrence pass | same singleton tables | x/Pα |

`register_co_occurrence_table` and `register_sandwich_flattening`
(`occurrence/mod.rs:330–453`) have no pair/removal candidate involving x.
No other variable's group contains x, so x cannot become another variable's
representative either. `substitution.rs:32–63` leaves x absent from the
substitution map, hence rewrites it to Some(x). `109–137` preserves its weight;
there is no second positive x weight with which it could parallel-union.

For the full unweighted c/Y/O alias component, the first co-occurrence pass
unions Y and O into earliest-born c, and the following pass removes c using
the common Exact(Fun). R,V,B,p are positive-only and disappear at the first
polar pass. Where redundant alias arms were omitted, these non-x alias images
can shorten; none can cross into x because no group shares it. The retained
callback constructors themselves are untouched by variable substitution.
Thus every iteration changes only non-x aliases or stops. At the first fixed
point, and throughout the second, the only effect variable is x with precisely
the two incidences above. This argument covers the actual fixed points even
without claiming numeric record multiplicity or a particular hash iteration
order for redundant aliases.

The structural pass's `sandwich_kinds` and occurrence merge
(`sandwich.rs:165–192,268–316`) give NoLift at both singleton x locations. Row
is itself ConcreteButNotLiftable and cannot rescue a lift. NoLift is absorbing;
the pass cannot lift x, create a new x occurrence or alter Pα. The second fixed
point therefore reaches its unchanged exit. After normalized substitutions,
the positive returned callback's result-Effect still literally contains x/Pα.
This establishes S's required observation at simplifier return.

## 4. What remains OPEN

S is neither H nor a source-qualified pure-result counterexample. Its last
consumer boundary is the return from `simplify_compact_root...`, not the
published scheme. The next exact obligation is the image of this retained
x/Pα and its subtract fact through `generalize/mod.rs:805–834`:
quantifier census, dead quantified subtract pruning and stack cleanup.
Ancestor finalization, fresh-use instantiation/provider binding and the final
callback call/output route are also unproved here. No positive Effect absence
after one of those later owners is inferred from this result.

For a surrounding program that connects uses before this collection snapshot,
the first additional premise is its actual incoming constraint/copy incidence
at the scheme consumer, owned by the relevant Name/application/instantiation
path and session schedule. S does not establish that all such snapshots equal
this fresh declaration slice. This is a broader H obligation, not an assumed
input hidden in S's local incidence derivation.

## Checks, dependencies and handoff

Method: static constructor closure and actual consumer case analysis. No
Oracle invocation, tests, builds, instrumentation, benchmark samples or Git
mutation. Verification is leased Markdown integrity and dependency hashes;
it is not independent proof review. Source reads used at most three concurrent
short read-only shell commands; no delegated workers or long-running process.
Requested model/effort: `gpt-6.1-sol` / `high`. Observed runtime model/effort:
unknown; repository role/default configuration does not establish runtime pins.

Pinned Y3 dependency SHA-256 values:

| Dependency | SHA-256 |
| --- | --- |
| accepted P note | `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7` |
| projection audit | `b0879d15e8fac7a107a610973444df07b6203747045f7506c59c5d084d5d40ae` |
| original H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |

Decisive inspected Oracle file SHA-256 values:

| Owner | SHA-256 |
| --- | --- |
| annotation/constraints.rs | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| lowering/expr/lambda.rs | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| lowering/expr/method_body.rs | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| compact/collect/mod.rs | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| compact/collect/type_nodes.rs | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| compact/analysis/mod.rs | `9c5e7a863f25ad94b10b7c7865af523e30c6ac361847f20f58307f1025432463` |
| compact/analysis/occurrence/mod.rs | `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2` |
| compact/analysis/occurrence/substitution.rs | `b6d04c187a870892239db84a16360f700f7efaef4c0ba7b731d1389db31f9bf2` |
| compact/analysis/sandwich.rs | `8935b5f295e6c6bda2838385ac1fca8298fe964061a7c6d800f612b2bbcd16f2` |
| analysis/session/generalize.rs | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |

Commit packet: this leased path only; baseline
`52f44a1a2bfe9a39c6780b76b8098795b70ace9e`; no dependency edits. Review status:
producer-frozen, primary to assign fresh independent review. Proposed checkpoint
message: `research: derive direct callback retention through compact simplification`.
Proposed shared-record delta for the primary: record bounded S through simplifier
return, keep H OPEN, and assign the retained x/Pα stack-cleanup image. No shared
record is changed by this leaf. Next action: independently review the complete
x incidence and fixed-point preservation before promoting bounded S.
