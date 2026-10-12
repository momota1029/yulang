# Simple-sub intrusion correspondence audit

Status: frozen, independently reviewed research checkpoint; source characterization and
conditional falsifier, not a source-qualified refutation or theorem closure
Y3 baseline: `f29de555cfb845b6c6622ffcc6de09f4cbdbe160`
Yulang Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Original Scala reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Lease: this note only; static audit, 30-minute allocation

## Objective, authority and source separation

Test the proposed preservation premise: an actual extrusion parent/copy pair
in one qualifying **Value-reference** SCC may be equated without losing
supported source typings or required principal schemes. Equality, the selected
source-reference meaning, and the distinction from comparison judgments are
fixed by [parent-copy SCC intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md),
“Selected operation and compiler responsibility”, “Value-reference SCC
clarification”, “Apply-result source-fragment ownership” and “Definition-root
Value ownership”. The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1, 3 and “Authority and integration” require the actual source/proof bridge.
This audit changes no selected meaning.

The assigned import path under `notes/progress/` is absent. The actual import
is [notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md](../theory/2026-10-11-parreaux-simple-sub-proof-import.md).
It pins **original Simple-sub** Typer.scala at `9bae772…`; that Scala code is
not Yulang Oracle `a58eefc…`. Both checkout HEADs were checked. No Oracle
implementation or runtime behavior is inferred from the Scala pin. The Oracle
checkout was inspected only to establish its revision, not its typing algorithm.

Primary paper: Parreaux, *The Simple Essence of Algebraic Subtyping*,
DOI `10.1145/3409006`, persistent PDF
`/home/momota1029/rust/simple-sub-reference-paper.pdf`. Sections §3.5,
Figs.6–9, and §5.3 were read from its existing text extraction. The PDF hash
matches the imported snapshot. Paper §5, printed p.124:24, explicitly excludes
let polymorphism from its soundness/principality proof sketches; footnote 15
proposes definition duplication as a separate proof route. Thus §5.3's
Theorems 1–2 do not prove recursive-let extrusion, a new Value graph, or
parent/copy equality preservation. The complete proofs are also explicitly
outside the paper's scope. These are coverage limitations, not a rejection
of the paper's stated non-let theorem claims.

## What the original operations actually preserve

Pinned `shared/src/main/scala/simplesub/Typer.scala`:

- `:48–55`: recursive RHS uses one fresh monomorphic placeholder at `l+1`,
  constrains the completed RHS below it, then publishes `PolymorphicType(l,…)`.
- `:62–84`: names instantiate; Lambda shares its one parameter; Apply emits
  a Function demand; projection emits a Record demand.
- `:106–126`: arrow arguments reverse comparison; variable bounds insert
  before opposite-bound replay; wrong-level structure is extruded and retried.
- `:134–159`: extrusion memoizes `(variable,polarity)` before descent.
  Positive copies get original lowers and an original-to-copy upper link;
  negative copies get original uppers and a copy-to-original lower link.
  Arrow arguments flip polarity. The original variable's level is immutable.
- `:166–189,201–207`: each scheme use creates one new identity per variable
  above the generalization boundary, preserving sharing inside that use and
  retaining lower-level anchors across uses.
- `:239–257`: coalescing retains the variable and the selected bounds;
  recursive binders are keyed by identity and polarity.

These statements are direct source characterization. Typer has no extrusion
parent record, Value-reference SCC qualification or intrusion quotient.
Its recursive caches avoid infinite traversal; they do not equate cached
variables. A source-reference cycle is therefore not an original operational
reason to identify two variables.

## Source-derived shared Function discriminator

Use the original supported term constructors, with ordered Record fields:

```text
t = λf.
      let rec g = { id = λx.x, run = f(g.id) }
      in { one = (g.id)(1), two = (g.id)(true) }
```

This is an original `Lam/Let(true)/Rcd/App/Sel/Var/Lit` term, not a claim
that Y3 parses this spelling. `true` is the pinned canonical Bool builtin
(`Typer.scala:20–25`). The method is a manual constructor trace, not execution.
The recursion and level crossing are material: `g.id` is inspected during its
own monomorphic initializer, before its identity-function lower is supplied.

At outer level 0, let `F` be the `f` parameter. Recursive `g` placeholder `G`,
identity parameter `α`, projection result `P`, and call result `R` are fresh
at level 1. Their initial bounds are empty.

1. `g.id` adds `Record(id:P)` to `G.upper`. No lower exists yet.
2. `f(g.id)` demands `F <: Function(P,R)`. Its negative extrusion to level 0
   creates positive `P+` and negative `R-`, giving `P.upper=[P+]`,
   `R.lower=[R-]`, and `F.upper=[Function(P+,R-)]`.
3. Recursive RHS publication inserts
   `Record(id:Function(α,α),run:R)` into `G.lower`. Replay of its existing
   upper submits `Function(α,α) <: P`. This inserts that lower into `P`
   and replays it against `P+` at level 0.
4. Positive extrusion of the shared `Function(α,α)` creates distinct copies:
   argument first, `N = copy(α,negative,0)`; result second,
   `Q = copy(α,positive,0)`. The exact resulting local bound lists are

   ```text
   α.lower=[N]       α.upper=[Q]       level(α)=1
   N.upper=[]        Q.lower=[N]       level(N)=level(Q)=0
   P+.lower=[Function(N,Q)]
   ```

   The explicit `Q.lower=[N]` comes from the argument-first side effect already
   present when the result copy traverses `α.lower`. This is not two unrelated
   variables replacing a shared source parameter by fiat. No listed subtype
   relation is used as a Value-reference edge.

5. Publication gives `g` a boundary-0 scheme whose Record lower still contains
   `Function(α,α)`. Original `freshenAbove(0,…)` creates distinct `α1` and `α2`
   for the two body uses, while both retain anchors `N,Q`. Both occurrences
   of a given `αi` in its own Function remain shared.

There is a concrete declarative typing for this term:

```text
((⊥ → ⊤) → Int) → {one:Int, two:Bool}
```

Under `f:(⊥→⊤)→Int`, type the recursive initializer with monomorphic
`g:{id:α→α,run:Int}`. The identity has `α→α`; arrow subtyping gives
`α→α <: ⊥→⊤`; `run` therefore has Int. Since `α` is absent from the outside
context, recursive T-Let may generalize it. Its two body uses instantiate
`α:=Int` and `α:=Bool`. T-Proj, T-App, T-Rcd and T-Abs yield the displayed
typing. This derivation uses the paper's declarative rules, not §5.3's
excluded let completeness claim.

The original bound trace also distinguishes these choices: tight demands
on the two outputs constrain `α1` below Int and `α2` below Bool separately.
Their shared `N` can receive both uppers without a conflicting primitive
lower; shared `Q` can receive both primitive lowers without a conflicting
upper. This preserves the admissible interval rather than equating its ends.

## Conditional quotient attack and exact missing premise

Supply, as a **candidate hypothesis**, a qualifying source Value graph with
actual incidences `α → Q` and `Q → α`, and the retained positive-copy parent
record `(Q,α,+,0)`. This is the smallest two-vertex qualifying SCC. These two
edges are expressly *not* derived from `α.upper`, `Q.lower`, subtype direction,
or the parent record. The audit has no source constructor establishing these
incidences for `t`; decorating the trace with them does not establish source
reachability.

If such qualification causes the canonical equality `α=Q` **and gives the
canonical variable level 0**, future `freshenAbove(0,…)` keeps that variable
in both g uses. Int and Bool become lowers of the same parameter/result row.
Each application result depends on that same row. Demanding `one:Int` and
`two:Bool` therefore replays a Bool-to-Int or Int-to-Bool comparison, rejected
by original `constrain`. The distinct original `α1,α2` derivation is lost.
Canonical equality cannot keep the high parent level while a low-level
Function still names it without separately repairing the original bound-level
invariant. The current Y3 merge chooses the minimum level
(`candidate_intrusion.rs:588–594`), so this level premise is implementation
behavior, not invented original Simple-sub behavior.

**Claim class:** conditional typing-loss discriminator for that precisely
stated quotient, with an actual original source extrusion trace. It refutes
the shortcut “any such quotient is harmless because original extrusion already
copies cycles.” It does **not** refute selected Yulang intrusion: the qualifying
source-incidence premise has not been established for these rows, and a
Yulang scheme consumer could require a separately proved preservation bridge.
No independent review or full principal-scheme equivalence proof is claimed.

The exact blocker is therefore not finding another bound-cycle model. It is
the source owner's construction/transport law that determines whether this
actual high-level `α` and low-level copy `Q` can qualify, and what independently
established representation invariant prevents the lost fresh-use typing if
they do. Cross-level `odd/even` definition-root references supply neither that
parent/copy identity nor that invariant.

## Current compiler correspondence boundary

Y3 `candidate_extrusion.rs:1–25,81–143,230–273` retains polarity/target-keyed
copies and creation provenance; its Function has four ports, including effects.
Those effect ports and later Yulang Call meaning are outside the original
two-port paper model.

`candidate_intrusion.rs:387–471` builds adjacency from bound-storage children
and Function/effect ports, then selects parent pairs in one component at
`:477–486`. This is the actual dependency graph it consumes. This audit does
not certify that those edges are the selected resolved-Name incidences.
Neither list placement nor comparison direction independently supplies that
source correspondence. The selected Apply/root incidence owners and their
transport to the consumed graph remain a distinct bridge. No production
implementation or semantic change is proposed here.

## Snapshot, checks, omissions and next owner

Five Y3 dependencies were hash-compared to the full baseline: both governing
designs, corrected import note, candidate_extrusion and candidate_intrusion;
all matched. Reference Typer's blob hash matched its own pinned revision.
Hashes at freeze:

| Dependency | SHA-256 |
| --- | --- |
| Parent-copy design | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| Inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Corrected proof import | `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113` |
| candidate_extrusion | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_intrusion | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| Original Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Original syntax.scala | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| Paper PDF | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |
| Existing paper extraction | `99ff99ab8166003c01fab1acc8cd0483e154732dbc2770549ec15df50bd7b24d` |

Commands: narrow `rg`/`sed` and paper-extraction reads; read-only revision/blob
checks; `sha256sum`; final note link/whitespace checks. No builds, tests,
runtime probes, Oracle invocation, randomized search, seeds/ranges or actual
mutations. The original source is independent evidence for its constructors;
the candidate quotient shares those constructors by explicit hypothesis and
does not provide an independent executable oracle. No other producer's proof
was reviewed or certified. At most three lightweight reads ran together; zero
heavyweight processes. CPU/RSS and exact wall time were not instrumented; work
stayed within the 30-minute allocation. Only this leased path was written.

Unverified: full symbolic coalescing/simplification of `t`, an executed
scheme comparison, actual selected Value-SCC membership, Y3 source admission,
effect/Call preservation, generalized publication, and global principality.

One recommended next action: primary assigns the source-reference
construction/transport owner the exact `(α,Q)` reachability premise above,
and gives the main prover this conditional fresh-use discriminator for the
original preservation obligation. Do not close the parent gate using a
paper citation or a supplied SCC annotation.

## Commit packet

- Exact lease: `notes/progress/2026-10-12-simple-sub-intrusion-correspondence-audit.md`.
- Baseline: `f29de555cfb845b6c6622ffcc6de09f4cbdbe160`; Oracle and original
  Scala pins as recorded above; changed checked dependency hashes: none.
- Review: independent compiler-referee review found no issue. It confirmed
  the ordinary declarative typing, polar-copy construction, separate fresh
  uses and conditional Int/Bool loss calculation; source qualification and
  full preservation remain open.
- Checks: pinned blob equality, SHA-256 snapshot, focused paper/source reads,
  Markdown link existence and trailing-whitespace checks; no executable checks.
- Message: `research: audit intrusion against original Simple-sub fresh uses`.
- Shared deltas left for primary/curator: correct the import locator; record
  the distinct Scala/Oracle pins and the missing parent/copy Value-incidence
  premise in the owning source gate; preserve the original proof gate as open.
