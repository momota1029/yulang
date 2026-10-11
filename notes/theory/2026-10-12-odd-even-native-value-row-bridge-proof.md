# Odd/even: native row construction and the publication discriminator

Date: 2026-10-12
Status: frozen research-only source characterization and conditional model discriminator; independent review pending
Baseline: `d557bc183d393bd181325c96569785df8262376e`, `research/simple-sub-intrusion`
Exclusive lease: this file; one leaf, no delegation
Parent source/transport, intrusion equality, soundness and principality gates: OPEN

## Frozen objective and authority

The parent statement retains every supported source program, authentic finite
inference/use history, original lexical/type/event scope, and retained distinct
Value extrusion pair `(copy,parent)`. Its graph vertices are actual native
Value variables, its edges are references in their constructed values, and
qualification requires both directed paths before the proposed equality.
Required equality preserves the same joint typing, complete Call, effect
hygiene, attachment/provider/witness/residual evidence and required principality.
This note neither narrows that statement nor establishes its conclusion.

The local question is whether the accepted source-owner cycle for

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

forces a cycle between actual native Value rows. The binders spelled `n` are
distinct: A is the outer formal and B the inner formal. `even` is sequentially
published before the outer final expression. The accepted source abstraction
has `even -> odd` and `odd -> even`. Its native realization is the question;
that source abstraction is fixed in both models below.

Governing sections are the Authoritative parent-copy design's **Selected
operation and compiler responsibility**, **Value-reference SCC clarification**,
**Apply-result source-fragment ownership**, and **Retained boundary**, and
top-level inference principles §§1–5 and **Evaluation**. The approved Apply
answer is q1/a1 revision 1, approved by “OK.” Its direct Name targets belong to
the Apply result row before and after dispatch. Other constructor/transport
clauses of the value-content interpretation remain Draft. The source-value
repair draft separates the accepted binder abstraction from native vertices.

Method: inspect actual row producers, source schedules and consumers; apply
the selected Apply equation; discriminate graph completions at one publication
seam. Hypotheses for the operational analogue are successful recovery-free
LocalSource formation, checked allocation and the unannotated constructor
actions at the original scopes. No source restriction, eager solving rule,
provider selection, type-port edge, bound-storage edge or parent edge is added.
Complete Call and effects retain their separate obligations.

## Original Simple-sub does not supply this graph

The pinned original is `/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`, and the paper is the local
`simple-sub-reference-paper.pdf` (*The Simple Essence of Algebraic Subtyping*).
Paper §§3.1–3.3 and §3.6 define types, mutable lower/upper bounds and their
cyclic traversal/copying. They do not define the selected source-owned Value
reference graph or the selected same-SCC parent/copy equality operation.

The actual exhaustive `typeTerm` arms in `Typer.scala:59–83` confirm the
distinction. `Lam` allocates its formal and returns a structural
`Function(param,body_ty)`; it does not allocate a Lambda-owner variable.
`App` returns a fresh type variable after generating a Function constraint;
it retains no resolved Name incidence. Nonrecursive `even` consequently has
scheme body `Function(B,R)`, not a fresh binder variable E. Recursive `odd`
does have the row O from `typeLetRhs` (`:48–55`). `Variable` stores level,
bounds and type-printing metadata (`:194–230`), not source fragments or Name
occurrences. `constrain`, `extrude` and `freshenAbove` operate on that typed
structure (`:87–188`). The original graph is a type/bound graph, not the
approved Value graph. A one-variable-per-source-binder map is already false
as an account of original allocation.

The independently reviewed odd/even derivation supplies the original finite
constraint calculation and authentic Rust extrusion prefix. This note uses
those results only for their stated operational claims, without converting
their bound cycles into Value-reference edges.

## Actual Yulang constructor coordinates

The exact conditional/infix text has no established ordinary Y3 HIR admission
bridge. The inspected smaller Call-bearing structure is

```yulang
my odd n = { my even n = odd(n); even(n) }
```

This isolates two Calls; it is not an adequacy translation of the original
computation. Static constructor representation is conditional on authentic
formation; no parser or inference execution is claimed.

| Native row | Actual owner | Level |
| --- | --- | --- |
| O | module definition root for odd | 1 |
| L | outer Lambda expression component | 1 |
| H | outer block expression component | 1 |
| E | local even initializer Lambda component and installed unannotated root | 2 |
| A, B | distinct outer and inner formal registrations | 1, 2 |
| U, V | module odd Name facade and later local even Name facade | 2, 1 |
| R, S | inner and outer Apply result components | 2, 1 |

These are distinct allocation coordinates, not asserted final canonical
inequalities. `add_definition_root` and `candidate_component` allocate root
and expression components separately (`lib.rs:985,:1680`;
`shadow_apply.rs:1024`); checked live allocation assigns one row per component
(`lib.rs:10047–10114`). Parameter Names use registered parameter endpoints
(`candidate_source.rs:187–216`). No equality between O/L, H/S or E/R follows
from allocation or from a later comparison.

HIR installs outer formals, installs local initializer/self/formal scopes,
restores them, then publishes `even` (`local_source.rs:286–367`). Name lookup
selects lexical identities before module identities (`:636–657`). Apply
construction retains distinct callee/argument children (`:553–581`), and
Block retains initializer roots and its final expression (`:793–823`).
Candidate scheduling visits local initializers at the raised level and the
final expression at its enclosing level (`candidate_source.rs:253–307`).

The complete relevant Value construction skeleton is:

```text
inner module use:       O <: U
inner Apply:            U <: F_minus(B, argument_effect, invocation_effect, R)
inner Lambda:           F_plus(B, entry_effect, return_effect, R) <: E
local publication:     LocalScheme(even, root=E, boundary=1)
later local use:        fresh(E, one shared use map, level=1) <: V
outer Apply:            V <: F_minus(A, argument_effect, invocation_effect, S)
outer Block facade:    S <: H
outer Lambda:           F_plus(A, entry_effect, return_effect, H) <: L
module root forwarding:L <: O
```

The use endpoint join retains O versus U (`lib.rs:1273–1327`). Apply recipes
retain U/B/R and V/A/S (`candidate_source.rs:394–411`), and native admission
retains all four Function ports (`shadow_apply.rs:1331–1383`). LambdaRecipe
retains its distinct root/body/formal coordinates
(`candidate_source.rs:449–464`; `lib.rs:719,11233–11370`). Block emits a Group
recipe (`candidate_source.rs:467–474`); Group admission generates the Value
comparison (`shadow_apply.rs:1331–1335`). The final source action links the
outer expression endpoint to the separately allocated definition root
(`candidate_source.rs:478–494,663–670`). These facts establish typed links;
none supplies reference ownership forwarding.

Unannotated installation records E and boundary 1 exactly
(`candidate_scheme.rs:1316–1338`). Later local routing captures that live
root and constructs one coherent use map (`:1356–1382`); its fresh root is
neither the binder target E nor an extrusion copy by that fact. The inner
Call's opposite-bound replay reaches a negative structural extrusion and
retains `(C,B,+,1)` and `(D,R,-,1)`
(`candidate_extrusion.rs:94–163,224–249,809–841`;
`lib.rs:12412–12454`). These are the previously derived forced Value pairs;
neither O nor E is their parent.

For the direct Names, the approved Apply equation therefore requires

```text
R -> O, B
S -> E, A
```

The original targets are O and E, not U/V or a later fresh scheme root.
These two incidence sets are selected semantics applied to authentic
coordinates. Current recipes/native interfaces do not emit or consume such
per-result incidence records. They are not evidence that the implementation
already realizes those required edges.

## Minimal pair at the definition-publication seam

To make the discriminator stronger, provisionally grant the same favorable
Lambda/body and Block-final ownership forwarding in **both** completions.
These are shared additional hypotheses, not newly adopted authority:

```text
E owns the inner Lambda body Names:          E -> O, B
H forwards final-expression source Names:    H -> E, A
L owns its body excluding even initializer: L -> E, A
```

Keep the same source tree, binder abstraction, resolved Name occurrences,
native allocations, four-port terms, effects, typed comparisons, original
scheme publication and use maps, and retained parent metadata. Keep R/S's
approved incidence explicitly in each model. The completions differ only in
the as-yet-unspecified owned source description of the separately allocated
definition root O:

| Completion | O's outgoing references | Result on the displayed core |
| --- | --- | --- |
| M0: no declaration-root incidence forwarding | empty | `L -> E -> O` and `R -> O`; no nontrivial SCC |
| M1: publication forwards L's owned Names to O | E, A | `O -> E -> O`; O and E share a nontrivial SCC |

All unlisted references are empty in these finite completions. In particular,
formal rows and retained port-copy rows have no outgoing reference merely
because of a port or Parent record. Deleting the common formal sink edges
from the *display* leaves the minimal distinguishing edge `O -> E`;
the full models keep every listed Name occurrence and its original target.

These are models of the currently fixed local graph clauses plus the shared
explicit candidate premises, over actual constructor coordinates. They are
not two executed compiler implementations or complete sound/principal
language models. Both preserve the accepted **source-binder** SCC. M0's
failure to realize that SCC on O/E is precisely the missing correspondence,
not a change to the accepted source graph. Neither sets an edge from a
comparison, Function port, provider or parent. No displayed retained pair
qualifies in either completion, so the selected equality operation imposes
no further merge at this cut. Copy/reference transport and later histories
remain outside this discriminator.

Consequently selected Apply ownership and the actual typing constructors
alone do not determine the required native cycle. Even granting both
Lambda/body and Block-final forwarding does not settle the definition-root
seam. If the additional publication rule forwards those two original Names
to O, and the shared Lambda rule forwards the inner Names to E, then the
two-edge native cycle follows immediately. That is a conditional derivation;
the publication premise is not an established source rule.

There is no justified path `E -> R` or `O -> L -> H -> S` from the current
typing links. A design might separately select value-reference forwarding
edges, or directly retain the original Names on every owning root, but a
choice between those mechanisms is not a proof result of this packet.

## Consumer obstruction, economy audit and handoff

The current SCC consumer scans lower/upper bound payloads, Function ports
and Effect dependencies (`candidate_intrusion.rs:358–488`). It does not
consume the selected Apply incidence or a source-owner publication record.
Thus no cycle observed by that consumer establishes the approved graph.
Complete Call remains pending (`candidate_call.rs:213–247`); neither model
asserts dispatch completion, full replay, effect hygiene or equality safety.

Prior native-port derivation and original-incidence reconstruction left
ownership/transport unresolved. This pass supplies a different discriminator
at an actual constructor seam and stops. Under the existing economy audit,
faithful qualification/equality preservation remain A/B. Recovering the
original Name/scope/root join from later bounds is D: source construction
already knows it. Retaining it can remove reconstruction debt but cannot
decide whether L's body description belongs to O. No parent gate is relabeled
or closed, and no third equivalent SCC proof is proposed.

One next action: the primary resolves the native ownership forwarding
contract for Lambda/body, Block-final and definition publication at the
displayed coordinates, especially `L <: O`, then assigns its explicit
constructor/consumer correspondence. An approved O/E cycle would still not
qualify `(C,B)` or `(D,R)` or prove equality safe.

## Checks, resources and commit packet

Checks already run: bounded `cat`, `rg`, `sed`, local PDF-to-text reads;
read-only branch/reference SHA checks; SHA-256 and byte comparisons of all
15 direct Yulang semantic/source dependencies against the pinned baseline.
All 15 matched; no changed dependency hashes. The original reference HEAD
matched its pin. External SHA-256 values:

```text
paper       5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
Typer.scala f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
syntax.scala f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f
```

The 15 compared paths are the two governing Authoritative designs, both
Value-reference drafts, the approved Apply answer, both supplied odd/even
and Apply proof notes, `local_source.rs`, and solver `candidate_source.rs`,
`candidate_call.rs`, `candidate_scheme.rs`, `candidate_extrusion.rs`,
`candidate_intrusion.rs`, `shadow_apply.rs`, `lib.rs`. No dependency was edited.

Zero tests, builds, probes, Oracle calls or measurements. Up to seven tiny
static-read commands were requested concurrently; no heavyweight process
ran. CPU/RSS and exact reasoning wall time were not measured. The assignment
has a 45-minute bound; the primary requested the shortest frozen discriminator
and immediate return. Only this leased note was written. No Git mutations,
shared-record changes, delegation, external contact or self-certification.

Requested route: Sol `gpt-6.1-sol/high` proof leaf. The registered prover is
unpinned in `.codex/agents/prover.toml`; the callable schema supports it.
Observed effective role/model/effort metadata is unavailable to this leaf
and remains unknown. Configuration and packet text do not establish execution
settings. No Astra assignment or override was attempted.

Commit packet: exact changed lease
`notes/theory/2026-10-12-odd-even-native-value-row-bridge-proof.md`;
baseline `d557bc183d393bd181325c96569785df8262376e`; changed dependency
hashes: none. Claim/review: bounded constructor characterization and
conditional semantic discriminator, unreviewed research-only checkpoint;
parent gates OPEN. Checks: static reads and dependency byte/hash comparison;
no executable validation. Proposed checkpoint message:
`research: isolate odd-even Value cycle at definition publication`.
Shared-record deltas left to primary/curator: record distinct O/L/H/S rows;
record required R/S Apply incidence separately from missing emission;
retain Lambda/Block/publication forwarding and copy/use transport as exact
open premises; preserve equality, complete Call, hygiene, soundness,
principality and production gates. Writes stop at submission.
