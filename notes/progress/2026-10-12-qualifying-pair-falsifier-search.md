# Qualifying parent/copy falsifier: bounded static source search

Status: frozen, unreviewed research-only characterization. No qualifying
counterexample found; this is not a proof of equality preservation or a parent
gate closure.

## Objective, baseline and method

Search the smallest source constructors that can both create a genuine
polarity-aware extrusion copy and relate it back to its parent through the
approved Value-reference graph. Distinguish function-argument extrusion,
Apply-result extrusion, recursive-root extrusion, and ordinary fresh use.
The method is a manual operational trace, not an executed enumeration.

Y3 baseline: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`.
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`, at
`/home/momota1029/rust/simple-sub-reference`.
Both HEAD values were checked and matched these pins. Read-only diff against
the Y3 pin showed no changes in the seven named Y3 dependency paths below.

Governing authority is the
[parent/copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
Selected operation and compiler responsibility, Value-reference clarification,
Apply-result ownership, Nested Apply membership, Definition-root ownership,
and Retained boundary; the
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; and
[local recursion](../design/2026-10-10-local-self-recursive-binding.md), Selected
source behavior and Proposed source-to-solver seam. These clauses were visible
in the final authority read. No language meaning is selected by this note.

The reference operational owners inspected are `Typer.scala:61–84`
(Lam/App/Let), `:105–127` (decomposition, accumulation and level violation),
`:134–159` (polar extrusion), `:166–188` (freshening), and `:201–207`
(scheme instantiation). Paper §3.2 and §3.5, including Figures 7–9, were
visible. Reference `typeLetRhs` itself was not visible in the narrow read;
the recursive-let operation is taken directly from paper Figure 8. Paper
§§3.3–3.4 were only partly visible; §§5.1–5.3 were not inspected successfully.
No metatheorem from those sections is invoked.

The broad [effect hygiene policy](../design/2026-09-29-intrude-effect-hygiene.md)
was requested in the read and hashed, but its text fell in truncated output.
The exact annotation-effect §§1–4 bridge was not audited. All candidates here
are in the pure function/let fragment; no effect/protection result is claimed.

The earlier
[native continuation counterexample](../theory/2026-10-11-inference-rebuild-native-spec-proof.md)
does not have the required SCC qualification and is not recycled as a
refutation. The
[Value-reference analysis](../theory/2026-10-11-simple-sub-value-reference-scc.md)
has no established source-qualified direct pair. Neither fact supplies an
edge to a fresh copy. The exact user odd/even text has the independently
recorded [source-admission gap](2026-10-12-odd-even-source-admission-audit.md).

## Claim boundary and bridge hypotheses

This is a bounded negative search over four constructor shapes below, not a
claim that all source programs lack a qualifying pair. The original target
remains equality preservation for an actual extrusion parent/copy lying in
one SCC of constructor-owned Value references.

For the traces, levels and type-variable identities follow the original
reference operations. Correspondence of a recursive placeholder with a
definition Value root, a parameter variable with its binder Value row, and
an App type-result variable with its Apply Value row is a **candidate source
bridge**, not an audited Y3 implementation theorem. A definition root is
kept distinct from its Lambda/body/Apply rows throughout.

Definition and Apply edges below are consequences of the selected source
ownership clauses, conditional on admitted source and resolved Names. They
are not inferred from subtype comparisons. No adjacency transport law for
extrusion or freshening is assumed. In particular, copying a type bound
does not prove how the Value-reference payload is copied or redirected.

Use `h = 1` for the outer initializer and `h+1 = 2` for an inner initializer.
`p+` and `p-` mean two different cache images of parent `p` at target 1.
The cache key is `(parent identity, polarity)` and is installed before bounds
are traversed. Each level-violation extrusion starts a fresh cache. Ordinary
scheme instantiation instead uses one nonpolar identity map per fresh use.

## Four discriminating source shapes

These are reference term schemas with Yulang-style binder names. Their exact
text was not parsed or executed in Y3. Sequential local visibility and one
open recursive root are retained; no mutual local group is introduced.

### 1. Identity and two independent uses

```text
let id = lambda x. x in id
```

At base level 0, `x` is `a1`; the initializer type is `a1 -> a1`.
Generalization at 0 followed by Name instantiation produces `a0 -> a0` with
one fresh image for both occurrences. There is no generated level-violating
comparison in this initializer or final Name use, hence no extrusion pair.
Two uses would create two independent instantiation maps. Treating either
map image as an extrusion child would change the selected parent relation.
The definition's reference to `x` targets the original parameter binder.

### 2. Same-level direct recursion

```text
let rec f = lambda x. f x in f
```

The open `F1`, parameter `X1`, and application result `R1` have the same level.
Generation gives `F <= X -> R` and `(X -> R) <= F`; no level violation is
needed. Source ownership gives root `F -> F`, `F -> X`, and result
`R -> F`, `R -> X`. A recursive root SCC is present, but no actual extrusion
parent/copy exists at this step. A later scheme instantiation is not extrusion.
A monomorphic witness is `F = Int -> Int`, `X = R = Int`.

### 3. Cross-level recursive call: argument and result copies

```text
let rec outer = lambda x.
  let rec inner = lambda y. outer y in inner x
in outer
```

Let the outer root be `O1`, outer parameter `X1`, inner root `I2`, inner
parameter `B2`, inner Apply result `R2`, and outer Apply result `S1`.
The inner recursive root is monomorphic while its initializer runs.

1. Inner `outer y` generates `O1 <= (B2 -> R2)`.
2. The level check extrudes that demand negatively to level 1. The Function
   argument reverses polarity: cache entries are `(B,+) -> P1` and
   `(R,-) -> C1`. The actual parents are respectively `B2` and `R2`.
3. Original extrusion records `B <= P` and `C <= R`, and installs the
   low-level demand `O <= (P -> C)`. Initially `B` has no lower bounds and
   `R` no upper bounds, so these first copies have empty copied sides.
4. Inner publication generates `(B -> R) <= I`; this is same-level.
5. The later `inner` occurrence instantiates the scheme at level 1. Its
   root/parameter/result images are `J1`, `B'1`, `R'1`. It retains
   `B' <= P` and `C <= R'`, since `P,C` are below the generalization
   boundary. These are fresh-use images, not new extrusion copies.
6. `inner x` generates `J <= (X -> S)`. Propagating the copied Function
   lower bound gives `X <= B'` and `R' <= S`.
7. Outer publication generates `(X -> S) <= O`. Its previously accumulated
   Function upper bound gives `P <= X` and `S <= C`.

Thus the demand copies, independently freshened inner use, and later bounds
are distinguished without eager source-level satisfiability checks. Every
displayed comparison is ordinary reference generation or propagation. One
original typing witness assigns `O,I,J = Int -> Int` and all the displayed
parameter/result variables and copies to `Int`. Hypothetical equality of
either actual pair preserves this particular witness, which does not prove
preservation of every required typing or principal scheme.

The complete edges licensed by the selected clauses for these fragments are:

```text
definition outer: O -> I, O -> X
definition inner: I -> O, I -> B
inner Apply:     R -> O, R -> B
outer Apply:     S -> I, S -> X
```

The nested declaration initializer belongs to `inner`, so its `outer` and
`y` occurrences do not add outer-owned edges. Both Name `inner` occurrences
outside that initializer target the resolved root `I`, not its type-use
image `J`. There is no syntactic-containment edge `O -> R` or `S -> R`.

In this listed source graph, the nontrivial SCC is `{O,I}`. The actual pairs
are `(B,P)` and `(R,C)`; neither pair lies in that SCC or in another shared
SCC. This is a calculation on the listed constructor incidences, not a claim
that the final transported native graph has no additional licensed edges.
The missing evidence is exactly how those incidences survive extrusion and
freshening. No comparison above licenses `R -> C` or `C -> R`.

### 4. Function-position recursive root rather than result extrusion

Replace the inner body in shape 3 by `outer inner`:

```text
let rec outer = lambda x.
  let rec inner = lambda y. outer inner in inner x
in outer
```

The recursive Name `inner` resolves to the open `I2`, not a scheme instance.
The inner App generates `O1 <= (I2 -> R2)`. Negative extrusion therefore
creates `(I,+) -> K1` and `(R,-) -> C1`, records `I <= K` and `C <= R`,
and installs `O <= (K -> C)`. This is a real recursive-root parent/copy
candidate `(I2,K1)`, unlike the result pair in shape 3.

This is the first extrusion, not the whole saturated state. Publication
`(B2 -> R2) <= I2` encounters the stored upper bound `K1` and propagates
`(B2 -> R2) <= K1`. A new positive-extrusion cache creates `(B,-) -> A1`
and `(R,+) -> D1`, records `A <= B` and `R <= D`, and installs
`(A -> D) <= K`. Thus `D1` is distinct from the earlier negative result
copy `C1`. Their presence is another reason not to identify a copied bound
with a source adjacency or to report this first root pair as a full-state
characterization. Further saturation/fresh-use constraints were not completely
enumerated for this variant; the displayed recursive witness satisfies these
additional comparisons too.

Here the selected source edges are:

```text
definition outer: O -> I, O -> X
definition inner: I -> O, I -> I
inner Apply:     R -> O, R -> I
outer Apply:     S -> I, S -> X
```

Again `{O,I}` is an SCC in these constructor incidences; `K` has no
constructor-owned incoming edge in the displayed graph. The later inner
Function lower bound does not itself add `I -> K` or `O -> K`.

The pure original constraints have a recursive typing witness: let
`T = mu t. (t -> Int)`, assign both function roots and their use images to
`T`, the parameter types and `K` to `T`, and result types and `C` to `Int`.
Function unfolding satisfies the generated demands and publication bounds.
This is a mathematical witness in the reference recursive-type fragment;
Y3 admission and complete Call/effect correspondence are unverified.

Even a candidate payload-copy hypothesis `I -> O` transported to `K -> O`
would give a path **from** `K` into `{O,I}`, without a path back to `K`.
The absent incoming path cannot be supplied by the genealogy record or
`I <= K`. A redirect such as `O -> K` would need its own owning transport
derivation, consistent with the approved Name target `I`; it cannot be
inserted here as an assumption to manufacture qualification.

## Result and earliest absent premise

The four traces separate three phenomena: root SCCs, genuine polar extrusion
pairs, and independent fresh uses. The smallest root-copy candidate reached
here is shape 4, but its source incidences do not qualify `(I,K)`.
There is no minimized genuine counterexample and no universal preservation
theorem. The hand search is incomplete outside these explicit shapes.

The earliest absent premise after the displayed source constructors is an
**operational Value-reference transport rule with exact row identities**:
which owner receives a copied incidence, which original binder target is
retained or transformed, which polarity cache controls that transformation,
and what independently owned source occurrence gives a return path to the
actual extrusion copy. Reference `extrude` traverses type bounds, not the
approved source-incidence payload, so reading its transition rules cannot
establish this premise. Its owner is the successor Value constructor and
extrusion/fresh-use transport seam, under the selected graph contract.

After the result-copy and root-copy variants leave that premise untouched,
another arbitrary graph or equivalent bound probe would not help. This is a
source-correspondence obstruction relevant to the original A/B parent gate;
the gate must stay OPEN. The obstruction is distinct from the odd/even
indented-body admission gap and does not invalidate that source's approved
root adjacency or select a narrower language domain.

Recommended next action: primary assigns a bounded audit of the owning
Value-reference transport constructor using shape 4, recording exact parent,
copy, payload owners and directed edges before intrusion; require either a
source-generated return path to `K` or its precise absence. Keep dependent
equality-preservation and implementation gates open meanwhile.

## Checks, coverage and resource use

Four synchronous shell read envelopes were used: the granted three plus one
explicitly approved narrow extension after output truncation. Utilities were
read-only `cat`, `rg`, `head`, `sha256sum`, `git rev-parse`, read-only
`git diff --name-only`, and `pdftotext` to stdout. No checker, compiler,
test, build, Oracle, random seed/range, mutation, or performance measurement
was run. There is no executed oracle and no oracle-independence claim.
The paper and Scala source are separate artifacts sharing the original
Simple-sub algorithm; neither contains the selected Y3 source Value graph.

The initial read of nonexistent reference `src/` failed and was redirected
to `shared/src/main/scala/simplesub/Typer.scala`. Large concatenated output
truncated part of the rules/current-task and theory reads. The relevant
agent orchestration restrictions and final exact authority text were visible;
full `tasks/current.md`, orchestration-budget text and prior theory notes were
not audited in full. No hidden theorem premise is imported from them.

Allocation: at most 35 minutes; no heavy processes or measurements. Exact
OS child-process count, CPU time and peak RSS are unknown. The four shell
envelopes were sequential; the `rg | head` locator pipeline had two lightweight
utility processes. There was no parallel build or delegated child.
The first separate integrity envelope used Python for link existence, trailing
whitespace and hashes, plus a read-only `git show` for reference-source pin
equality. All links existed, no trailing whitespace was found, and reference
`Typer.scala` exactly matched its pinned blob. A sixth shell envelope checked
the final repaired note's links, whitespace and hash lengths; all passed.
These two integrity envelopes were not additional source-context searches.
CPU/RSS/process totals for their Python/Git subprocesses were not measured.

SHA-256 dependency snapshot (Y3 pinned paths had no diff):

| Dependency | SHA-256 |
| --- | --- |
| parent/copy design | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| local recursion policy | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| broad effect hygiene policy | `509628603a93d94a2e3ac11c4e80e016469882672a1d45b3b261fa4321964800` |
| prior native-spec proof | `ea09a810be20984ca6c2711c4372e77cc7c360b2b208946465fcf6dad5bd4b33` |
| prior Value-reference note | `8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6` |
| odd/even admission audit | `2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06` |
| reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference paper | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

Unverified scope: all other source shapes, Y3 admission and execution of these
schemas, actual Value-row construction and transport, qualifying intrusion,
equality preservation for all required typings, principality, termination,
effects/protection, paper §§5.1–5.3 correspondence, and public/F5 cutover.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-qualifying-pair-falsifier-search.md`.
- Baseline: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`; reference:
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none observed for seven pinned Y3 dependencies;
  reference source matched its pinned blob; paper content hash recorded.
- Review: frozen unreviewed producer characterization; no independent review,
  authority promotion or theorem closure.
- Checks already run: the four bounded read envelopes, HEAD pin checks,
  seven-path pinned diff and dependency hashes; link existence, trailing
  whitespace and pinned reference-source equality. The final note-only repair
  added the explicitly incomplete later shape-4 propagation and corrected the
  reference hash without changing links. No tests/builds/Oracle.
- Proposed message: `research: distinguish root SCCs from qualifying extrusion pairs`.
- Shared-record deltas left to primary/curator: link this bounded falsifier
  result from the parent gate; name Value-reference transport/return-path
  evidence as the remaining source premise. No shared task/index/theory,
  production/test, question bundle or Git state was modified by this worker.
