# Correlated symbolic requests: a finite register quotient

Date: 2026-10-02
Status: Draft; independently reviewed research construction; no source or implementation authority
Scope: finite-control request-point kernels with equality and unary queries
Approved-by: none
Drafted-by: primary with bounded architecture audit
Reviewed-by: independent compiler_referee and spec_auditor package review; joint-register bound clarification closed by fresh compiler_referee delta review, 2026-10-02
Evidence audit: bounded read-only explorer inspected the frozen operation-local signature witness in §7; source applicability remains unproved
Supersedes: none

## 1. The question this construction answers

The open-row package represents membership for any future request point
`u`. A transition system may retain several such points and later relate
them. Enumerating new ground type arguments after each interaction does not
give one finite component presentation. Conversely, independently replacing
each occurrence with an arbitrary point can lose invariant sharing.

This package constructs a finite quotient for a kernel that retains a fixed
number of symbolic request points and observes only equality and finitely
many unary predicates. Unlike the prior supplied-`Q/P` theorem, it constructs
the state and predicate inventories from that instruction signature, without
enumerating the point universe or future client sites. It preserves
correlations between the retained points under one assignment.

The source application has explicit remaining premises (§7). In particular,
arbitrary source clients are not proved to fit a bounded register interface,
and complete `OpCompat` is not reduced to unary tests here. This is a **new
successor representation candidate**, not a Simple-sub-original result or
an Oracle-derived routing rule. The source semantics remains unchanged.

## 2. Kernel and observations

Fix one complete static parameter assignment `θ`. It contains the same type
endpoint assignment `ν`, the row assignments, and any rigid imports. A single
`θ` interprets the entire execution; it cannot change between requests.

Let `U` be the universe of typed request points. A point includes its family
and invariant argument tuple, not a dynamic event or activation identity.
The finite signature consists of:

- `N` named point terms `q_1(θ),...,q_N(θ)`, possibly equal;
- `m` unary predicates `P_1(θ,u),...,P_m(θ,u)`;
- finite control modes `L`, including all other finite data in this kernel;
- `k` registers containing points or an unset marker;
- finitely many transition schemas over old registers and new point
  witnesses, with a bound `b` covering all `k` pre-register positions plus
  every new witness variable, including positions not read by the guard.
  A safe bound is `b >= k + w_max`, where `w_max` is the maximum number of
  new witness variable names in one schema. These names need not denote
  distinct or fresh type identities.

Predicates include open-row membership compiled by the preceding package,
family-head tests, and membership in a fixed original capture contract.
They may be more general unary predicates provided their interpretations
are fixed by `θ`. Their effective type-theory interpretation is a separate
obligation; the quotient does not invent an oracle for it.

A schema's guard is a finite Boolean formula of equality between its point
variables/named terms, unary predicate applications, and fixed static
conditions. It can copy or clear registers, put a named point in a register,
or choose point witnesses satisfying that formula. Output registers reference
those variables or named terms. Schemas specify which old registers must be
set; unset checks are finite control tests, never comparisons with a point
of `U`. Initial-state formulas use the same signature on the initial registers
and mode; their point comparisons and unary queries require the queried
registers to be set. Choosing a witness is relational input, not
an allocation of a fresh type identity: equality with retained points remains
possible unless the actual guard excludes it.

Faults and observations have formulas in the same signature on the current
registers/control, with queried registers likewise required to be set for
point comparisons and unary queries; unset tests remain finite control.
This includes a selected-arm incompatibility observation
**only if** its predicate has been proved expressible in this signature.
The schema never turns `OpCompat` into a runtime dispatch filter: source
selection must precede its typing-failure observation as before.

Unbounded lists, stores, continuations, type terms or host predicates are
not hidden in `L` or one register. A point-construction operation `u -> F(u)`,
a general binary subtype query, or a store containing arbitrarily many
independently retained points is outside this kernel unless separately
normalized to the stated finite signature.

The theorem concerns these declared state observations and finite paths.
It does not preserve comparisons with arbitrarily many previously exported
points that are absent from its registers. A source client that remembers
those values is an additional interface obligation, not an instruction to
forget their symbolic `K,D`.

## 3. Finite static profiles without ground enumeration

At `θ`, partition the named points by equality and give each distinct named
point its `m` predicate truth values. An unnamed point has a **color**
`c∈{0,1}^m`, its vector of unary predicate values. Remove the named points
from each color class and record

```text
capacity_c(θ) = min(b, cardinality of unnamed points of color c).
```

The value `b` means "at least b", including infinite classes. These
capacities have finite symbolic definitions. For `1 <= j <= b`,

```text
AtLeast(c,j)(θ) iff exists u_1,...,u_j.
    all u_i are pairwise distinct,
    every u_i differs from every named q_l(θ),
    every u_i has color c.
```

These formulas are ordinary relational existence over the same row/type
assignment. They add no source cardinality operation, selector or capture
rule. Exact small capacities use `AtLeast(c,j) and not AtLeast(c,j+1)`;
capacity zero uses `not AtLeast(c,1)`, and saturation uses `AtLeast(c,b)`.
For `b=0` all capacities are zero and no point witness is available.

The finite static predicate inventory comprises named equalities, named
unary queries, the `AtLeast` formulas, and the finitely many static schema
conditions. Its size is bounded by

```text
N*N + m*N + b*2^m + number of static schema conditions.
```

Static profiles enumerate the equality partition, named colors and capped
capacities. Inconsistent profiles denote no actual `θ`; the construction
does not treat predicate bits as independently realizable type assignments.
This is a finite *symbolic* inventory. Deciding its satisfiability in the
underlying type/row theory is not established merely by the bound.

## 4. Constructing states and transitions

For each static profile and mode in `L`, a register descriptor records:

1. which registers are unset;
2. which refer to each named equivalence class;
3. the equality partition of the remaining anonymous register values;
4. the color of each anonymous block.

Exclude descriptors demanding more distinct anonymous values of a color
than its recorded capacity. The descriptor inventory is finite; a crude
upper bound per profile is
`|L| * (N+k+1)^k * 2^(m*k)` with the empty-register case interpreted as one
assignment. It overcounts impossible partitions and is used only as a finite
bound. No regular type is unfolded to enumerate these descriptors.

For each instruction, enumerate equality/color descriptors jointly for all
set pre-register positions and every new witness variable, including old
registers not referenced by the guard or output. Unset positions contribute
only finite control, never point blocks. Preserve named links and the whole
old register descriptor. There are at most `b` point variables. Keep precisely
the descriptors whose guard is true and whose anonymous block counts fit
the static capacities. Project the referenced variables into the output
register descriptor. This gives a finite transition graph for the profile.

For example, let old anonymous registers hold same-color points `a != b`,
choose `x != a` of that color, and replace the first register by `x`.
An output with `x != b` requires
three anonymous points in the joint diagram, although the guard mentions
only `x` and `a`. Counting the retained old `b` in the bound prevents that
edge when the color has only two points and preserves lifting from every
old representative.

**Forward coverage.** Every concrete kernel step assigns actual points to
the instruction variables. Their equality/color descriptor appears in the
enumeration, satisfies the guard and respects every capacity. Thus it gives
the corresponding graph edge and output descriptor.

**Uniform backward lifting.** Fix any concrete old register tuple described
by an enumerated source state at the same `θ`. Consider any outgoing graph
edge and its joint descriptor. Named witnesses are fixed by their named
class. Anonymous witnesses linked to old registers use those actual points.
For a color requiring `t` distinct anonymous blocks in total, some are
already represented by distinct old values. Since `t <= b` and the capacity
admits `t`, there are enough additional distinct points of that color to
fill every remaining block while avoiding the old ones. Different colors
cannot collide. The resulting tuple realizes all specified equalities,
inequalities and unary tests, hence the guard and the output descriptor.

This lifting holds from **every** representative, not merely from some
unreachable state merged into the descriptor. It is the premise missing
from an unsound existential may-edge argument. Inducting over graph paths
therefore realizes each finite path from any concrete initial representative
at that `θ`. Conversely every concrete path projects to the graph.
Observation/fault formulas are invariant under the descriptor, so the
kernel's reachable observation classes and reachable designated faults
are exact. In particular, the quotient creates no spurious selected-fault
path within this kernel. This is not an exactness claim about a prior
coarse heap abstraction or the whole source machine.

## 5. Symbolic saturation and principal certificates

Attach to each static profile its finite conjunction of inventory formulas.
Transitions and initial/observation conditions become formulas over the
finite inventory by enumerating their admissible profiles/descriptors.
Keep `Base(θ)` and all original symbolic dependencies with the graph.

The existing finite-certificate construction now has **constructed** graph
and predicate inputs for this kernel:

```text
R = least reachable state/profile relation
S = Base and not OR_q (R_q and Bad_q)
U_star = joint observation image of (S and R).
```

The prior proof gives termination and a principal certificate relative to
this declared kernel judgment. Forward coverage and uniform backward
lifting additionally make its designated-fault exclusion exact at each
realizable `θ`. One finite presentation handles arbitrary-length sequences
of new point inputs subject to the fixed register/query interface; it does
not collect a new lexical operation site for each such input.

The runtime event/activation identity universe is different from the type
point universe. This quotient neither merges events with equal family
arguments nor supplies the dynamic alias/lifetime abstraction. Those remain
in the common source/heap relation and must be included in a valid source
refinement. Joint `K,D` are not reconstructed from color labels. A source
application must prove each retained symbolic dependency is either present
in the finite signature/state or preserved as a shared parameter, rather
than independently resampled on each transition.

## 6. Precision, projection and conceptual cost

Nonempty colors alone do not suffice for this exact kernel quotient. Two
models with one versus two anonymous points of the same color agree on
nonemptiness. A kernel can retain `u`, choose a second point `v` of that
color with `u != v`, and reach an observation only in the second model.
`AtLeast(color,2)` derives exactly the missing existential distinction.
This is a kernel discriminator; no Yulang runtime type-equality instruction
or accepted source fixture is inferred from it.

A coarser alternative may assume arbitrarily many members of every nonempty
color. It has forward coverage but lacks the uniform lifting theorem; the
discriminator becomes a spurious path. With all failure paths retained,
the certificate remains conservative for that abstraction, at the cost of
possible rejection. This does not authorize such a source acceptance loss.
Both candidates use the same relation; exact capacities retain additional
joint existential information instead of adding source-site rules.

The `AtLeast` formulas are **nonpointwise** row dependencies. The earlier
open-row package's pointwise hiding theorem cannot eliminate a row variable
appearing in them. It must remain in `K,D` until a separate joint elimination
argument applies. Likewise a family endpoint used by a named term remains
shared through all colors, capacities and observations. The new construction
does not silently enlarge the scope of that previously reviewed theorem.

State/profile counts may be large: there are `2^m` colors and `b+1` capped
capacities per color, as well as named and register partitions. This is a
finite but unbounded construction over finite signatures, not an efficient
implementation claim or an approved resource threshold. Recursive control
uses graph back edges. No class-3 impossibility follows from this result.

## 7. Exact source-connection gate

The construction removes unbounded *point-name enumeration* as an obstacle
for its signature. A full source instantiation still must establish:

| Required premise | Current evidence / remaining work |
|---|---|
| finite signature for point queries | open-row membership, finite head tests and comparison to fixed original contract points fit; their slots/endpoints must come from source typing |
| complete `OpCompat` presentation | source compatibility also transports payload/response types and complete interfaces between two instances; this is not proved to reduce to equality/unary predicates |
| finite retained-point interface | arbitrary callers may retain values, requests and raw continuations; no source theorem yet bounds these by `k` or soundly abstracts them into this kernel |
| effective type/row predicates | finite formula names are not a decision procedure for their interpretation or satisfiability |
| common operational refinement | receiver entry, current store, ordered handlers, typed `Flow`, observation before dispatch, expiry and resumption must remain the existing source relation |
| acceptance and lifecycle | exactness/principality for this kernel is not final Oracle acceptance or full successor type principality; lifecycle gates remain downstream |

In particular, neither "there are finitely many source sites" nor the new
row-schema theorem establishes the retained-point premise for all future
clients. A future request related to a saved dependency must respect that
same dependency. Arbitrarily generating a matching row member is not by
itself its complete interface behavior.

The compatibility gap has concrete frozen-source evidence at `a58eefc3`.
`lib/std/testing.yu:10–17` declares the parameterless family `assertion`,
whose `assert_eq` signature contains

```text
(() -> ['left_eff] 'a, () -> ['right_eff] 'a,
 'a -> 'a -> bool, 'a -> str) -> ()
```

The local value/effect parameters are absent from the family parameter
list. The recorded acceptance fixture
`tests/yulang/regressions/effect/assert_eq_generic_public_signature.yu:1`
and `tests/yulang/cases.toml:3518–3525` expects a generic public operation
use under `[std::testing::assertion]`. These assertions were inspected,
not executed; their role constraints are not being resolved in this gate.

The owning declaration path confirms the distinction:
`crates/infer/src/lowering/body/act.rs:166–190` builds the full signature
separately from the family application using only `act_effect_type_var_names`;
`crates/infer/src/annotation/builder.rs:195–196,386–396` accepts named
signature variables independently of that family list. Signature insertion
(`lowering/body/signature_helpers.rs:217–235,247–255`) retains the
parameter/result types; `lowering/mod.rs:578–580,849–855` allocates named
signature variables. The latter two locators share the `crates/infer/src/`
prefix. This is characterization of a source capability, not authority for
the frozen inference algorithm.

Thus equal family instances can accompany different payload value types
and latent callback interfaces. Replacing complete `OpCompat` with family
equality would discard required information. The witness has a fixed Unit
response; it does not prove an operation-local response variable or that
every general binary subtype query is irreducible. The immediate source
normalization task must retain operation-local binder ownership and its
payload/interface substitutions, then prove which compatibility predicates
fit this kernel or require a richer joint presentation. This is an ordinary
operation-signature dependency, not a reason to start method resolution.

`2026-10-02-operation-instance-binding-package.md` now derives that binder
protocol and local payload/resumption preservation. Family-support
projection forgets operation-local coordinates even when operation identity
is retained. An application of this quotient to complete compatibility must
retain those coordinates and their dependencies separately; unary row
colors cannot reconstruct them. Effective compatibility and a finite
retained-point source abstraction remain open.

The next milestone work is to derive a typed interaction abstraction with
these premises, or exhibit a source dependency requiring a richer relational
signature. General binary predicates and point constructors need their own
normalization/finite-closure argument; treating them as unary by giving them
an opaque name is not a repair. This package supplies neither a source-level
counterexample to preservation semantics nor a reason to narrow the language.
