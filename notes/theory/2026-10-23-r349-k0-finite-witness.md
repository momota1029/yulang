# R349 — finite-term obstruction and the remaining actual-state premise

Status: **frozen producer candidate, revision 1; W0 OPEN**. This is a
conditional mathematical obstruction with a source/native owner audit. It is
**not** a source-qualified counterexample: this assignment has not supplied an
authenticated completed native state for the proposed source. No uniform
finite witness has been constructed. Fresh review and adjudication belong to
Luna.

Assignment: `R349-K0-FINITE-WITNESS`; author
`/root/r349_k0_finite_witness_prover`. Luna `/root` contributed the Boolean
separation interpretation in a task message. The source census and contracts
are Luna-authored. There are no descendants. Neither contributor can
independently certify the combined result.

## 1. Original claim and exact parent application

The unchanged parent is the original Simple-sub source/native A/B objective.
The only R349 target is the revision-3 contract's W0 supplier:

```text
∀ authentic s,S.
  ValidK0(s) ∧ CompleteK0Construction(s,C_s) ∧ NativeComplete₀(s,S)
    ⇒ ∃ρ∈Assign(R_S). ρ⊨H₀(S) ∧ Reifiable₀(ρ).
```

Use R336 rev4's **finite-term** least bounded-lattice preorder, its four-port
Function rule and finite Effect subsets; R341's actual occurrence-indexed
source family, row map, `NativeComplete₀`, and physical/live-work `H₀`; and
the same ordinary construction throughout. In particular, completion is not
an API `Ok`, an empty public projection, or an assumed satisfying valuation.

The result below proves that the displayed Omega **source formula family**
has no assignment in that finite carrier. Therefore, by accepted R341
retention, **if** this exact family is authenticated and has a genuine
`NativeComplete₀` state, every such state's exact `H₀` has no finite model.
This applies the obstruction directly to W0; it is not another proposed
replacement for W0. The unresolved discriminator is the existential
authentic-source/completed-state witness, specified in section 7. Without it
W0 is neither proved nor refuted, and original A/B remains OPEN.

## 2. Concrete source candidate and its entire source family

Proposed text, using the Lambda syntax also visible in pinned
`shadow_apply.rs:4381`:

```text
my r349 = (\x -> x x) (\y -> y y)
```

The intended authentic `LocalSource` tree is

```text
O = Apply(Gx, Gy)
Gx = Group(Lx)                 Gy = Group(Ly)
Lx = Lambda(x, X)              Ly = Lambda(y, Y)
X = Apply(x₁, x₂)              Y = Apply(y₁, y₂)
```

All eleven expression occurrences are distinct. Each `xᵢ` resolves to the
same enclosing HIR binder with formal Value row `a`; each `yᵢ` resolves to
the other binder with formal row `b`. This is a proposed source tree, not an
observed parser/HIR receipt. No parser, HIR lowerer, solver, or runtime was
executed. The node count and formulas below are conditional on that exact
authentic tree; a different actual lowering must be reconciled first.

Use the expression labels also for their semantic Value rows, except Names
whose endpoints are `a` or `b`. Let `e_z` be occurrence z's evaluation Effect;
let `i_x,r_x,i_y,r_y` be the two Lambdas' actual fresh entry/return Effect
rows; and let `k_x,k_y,k_o` be the three actual fresh invocation rows. Define
the **full**, distinct structural endpoints

```text
P = Fun(a,  i_x,  r_x, X)      Q = Fun(b,  i_y,  r_y, Y)
N = Fun(a,  e_x₂, k_x, X)      M = Fun(b,  e_y₂, k_y, Y)
T = Fun(Gy, e_Gy, k_o, O).
```

Positive/negative views of any one row use the same assignment. No two rows,
Function Terms, source occurrences, or relation/fiber incidences are equated.
Let `Z={x₁,x₂,y₁,y₂,Lx,Ly}`. The entire source family has eight Value and
twenty-four Effect inequalities:

```text
Value:
  a≤N, b≤M, P≤Lx, Lx≤Gx, Gx≤T, Q≤Ly, Ly≤Gy, O≤root.

Effect pure intervals:
  ∅≤e_z≤∅                                      (every z∈Z).
Effect row inclusions:
  i_x≤r_x, e_X≤r_x, i_y≤r_y, e_Y≤r_y;
  e_x₁≤e_X, k_x≤e_X, e_y₁≤e_Y, k_y≤e_Y;
  e_Lx≤e_Gx, e_Ly≤e_Gy, e_Gx≤e_O, k_o≤e_O.
```

These are direct instances of the frozen census, with all three calls, both
Lambdas, both Groups, four Name occurrences, and the Definition Link retained.
There is no Definition Effect row. Under this tree the exhaustive live-row
census is fourteen Values (eleven expression components, Definition Value,
and two formals) and eighteen Effects (eleven expression components, four
Lambda auxiliary rows, three invocation rows). The four separately allocated
Name Value components are unused, not the Names' types. R348's support
argument excludes them from every actual typing formula under its same-source
successful-construction premises; it does not identify them with `a` or `b`.

## 3. No finite source assignment: a separating algebra

Interpret every **finite Value term** in the bounded two-element lattice
`B={0<1}`. Send bottom/top to 0/1; joins/meets to max/min; base atoms and free
type variables to 0 (any fixed Boolean choices suffice); and define

```text
J(Fun(A,EA,ER,B)) = 1 − J(A).
```

This is an auxiliary mathematical interpretation of the fixed algebra, not
a proposed type meaning, new compiler semantics, or an inference algorithm.
Its total definition uses induction on finite syntax. It makes no recursive
type interpretation or coinductive unfolding assumption.

Every generating rule of R336's least preorder is sound for `J`:
reflexivity/transitivity and bounded-lattice rules hold in the Boolean lattice.
For the full Function inference, its argument premise `A'≤A` implies
`1−J(A)≤1−J(A')`. Hence the required comparison of the two Function images
holds whenever **all four** premises hold. Ignoring the other three ports in
this separating interpretation is permitted: validity requires preserving the
rule, not reflecting it. It neither removes their actual constraints nor
weakens their variance. Induction on a finite preorder derivation therefore
proves `t≤u ⇒ J(t)≤J(u)` for all finite terms, including derivations through
intermediate joins, meets, and transitivity.

Suppose a finite row assignment satisfies the section-2 Value family, and
apply `J` to its assigned terms. Write the Boolean images with the same
letters. The first two source call demands give

```text
a≤1−a and b≤1−b, hence a=b=0.
```

The two Lambda lower bounds and Groups give

```text
1=J(P)≤Lx≤Gx,             1=J(Q)≤Ly≤Gy.
```

Thus `Gx=Gy=1`. The outer call demand `Gx≤T` requires
`1≤1−Gy=0`, contradiction. This proves no finite Value assignment exists,
for **every** choice of finite Effect assignments. It does not start with a
source solution `σ`; the supposed finite assignment is eliminated.

This is stronger than reporting a cycle or an occurs-check. As a useful
negative control, the lone source `λx.x x` does have the finite assignment
`a=X=⊥V`, `Lx=P=Fun(⊥V,∅,∅,⊥V)`, with every Effect empty. Its self-use demand
holds by bottom. A suggested Omega assignment with the second formal `b=⊤V`
instead fails its own mandatory `b≤M` demand: `⊤V≤Fun(⊤V,∅,∅,⊥V)` is
separated by this same Boolean interpretation. Both self-use demands matter.

For a port-level check, R345 Function inversion applied to the source chain
`P≤Lx≤Gx≤T` gives `Gy≤a`; then `Q≤Ly≤Gy≤a≤N` gives `a≤b`, and thus
`Q≤b≤M`. This is the second formal's Function sandwich, not an assumed
equation or identification of native rows. The Boolean proof already handles
the sandwich without additional syntax normalization lemmas.

## 4. Pinned native endpoint and bound-formula audit

The following is a **conditional inventory for this exact construction**,
not a materialized final-state snapshot. It identifies the finite formulas
that the actual pinned consumers can add. It cannot be substituted for the
missing authentic completed-state witness.

`candidate_apply_value` at `candidate_extrusion.rs:1115–1148` stores a
nonreflexive equal-level row/row task on the lower owner as a negative upper;
Function/row on the upper owner as a positive exact lower; and row/Function
on the lower owner as a negative exact upper. Appending and full physical
slot readback are at `702–875`. Ordinary opposite-bound replay at `1070–1112`
generates the exact lower/upper pair from the two actual keys. Under R336 L0,
R337 J and R341/R348, representatives and extrusion endpoints are unchanged,
contexts are identity, and no copied-row intrusion occurs.

The closed distinct Value bound-formula inventory is:

| Physical lane | Formula projections |
|---|---|
| positive exact Function lower | `P≤Lx`, `P≤Gx`, `Q≤Ly`, `Q≤Gy`, `Q≤a`, `Q≤b` |
| negative row upper | `Lx≤Gx`, `Ly≤Gy`, `Gy≤a`, `a≤b`, `X≤O`, `Y≤X`, `O≤root` |
| negative exact Function upper | `a≤N`, `b≤M`, `Gx≤T` |

The only structural Function comparisons generated by these incidences are
`P≤T`, `Q≤N`, and `Q≤M`. The complete native four-port children are:

| Parent | Argument Value (Swap) | Argument Effect (Swap) | Return Effect (Preserve) | Result Value (Preserve) |
|---|---|---|---|---|
| `P≤T` | `Gy≤a` | `e_Gy≤i_x` | `r_x≤k_o` | `X≤O` |
| `Q≤N` | `a≤b` | `e_x₂≤i_y` | `r_y≤k_x` | `Y≤X` |
| `Q≤M` | `b≤b` | `e_y₂≤i_y` | `r_y≤k_y` | `Y≤Y` |

These are the actual dispatch orientations at `lib.rs:14821–14870` and
`candidate_context.rs:3505–3568`, not assumed Function transitions. Child
relation creation, pending handoff, and enqueue are distinct at
`lib.rs:14953–14990`. The final two reflexive Value children append no bound.
The resulting distinct Value task-key set has sixteen row-bound formulas,
three structural parents, and two reflexive children: twenty-one keys.

For Effects, let `E` be the twelve source row inclusions in section 2 plus
the six Effect children in the table. These eighteen directed row edges are
the entire possible nontrivial row/row Effect task family. From the six pure
positive seeds, every one of the eighteen Effect coordinates is reachable
along E. Under successful complete replay, the distinct Effect bound-formula
inventory is consequently

```text
{ ∅≤e | e is any of the eighteen Effect rows }
 ∪ { e_z≤∅ | z∈Z }
 ∪ E.                                                   (42 formulas)
```

The only no-row Effect task is `∅≤∅`; adding it gives forty-three distinct
Effect keys. Every one of these forty-two formulas and the no-row task holds
when **all eighteen separate Effect rows** receive the finite set ∅. Any
live Effect current/initial/processing/replay/Function-child formula from
this inventory also becomes `∅⊆∅`. This is an exhaustive satisfaction check
of this candidate's Effect theory, not a claim that arbitrary latent Effects
are semantically forced empty or that a Value model follows.

Every successful construction prefix has its exact `B,Q,P,R,D` formulas
interpreted as in R341/R345/R348. Transfers retain the actual request, saved
processing relation, local child, or replay slot. A true final completion
would retire the synchronous source frames and their acknowledgements;
capture reads live bounds and writes a separate graph. No historical memo,
receipt, diagnostic dependency or compact output is added as an H₀ formula.
Thus any completed state of this exact construction must retain the source
subset used by section 3, irrespective of whether additional duplicate
incidences are present. That subset alone makes its exact H₀ unsatisfiable.

**Incidence caveat.** Sixteen and forty-two count distinct formula
projections, not physical cells, bound fibers, relation identities, replay
operations, or dispatch counts. `pair_is_current` at `lib.rs:13507–13518`
requires memo membership **and the current relation's completion stamp**.
Equal endpoints with different source-set relations can miss and append
duplicate cells. The exact H₀ is still indexed by every actual physical and
live incidence; this audit does not quotient those identities. There is no
claimed concrete slot-number/multiplicity snapshot.

## 5. Finite relation closure and its precise limitation

The sixty-four distinct endpoint keys above are closed under the actual
ordinary source ingress, opposite-bound replay and Function child selection.
No further Value/Effect row allocator is reached beyond section 2 under
R348's exact K0 origin premises. These statements do not rely on a solution.

Let F be the finite set of static source events available in the same frozen
source construction. With R337's identity context/default scoped flow, each
relation key is `(typed pair, identity, source subset of F, default flow)`;
`relation_with_scoped` interns that complete key
(`candidate_context.rs:3062–3093`), and `intern_sources`/`union_sources` retain
unions of the same finite events (`3095–3117`). Thus at most `64·2^|F|`
distinct relation keys can arise. This is a mathematical bound using the
predecessors' finite-source premise, not a newly read event-graph dependency
or an observed event count.

Generation is stable. Successful K0 prefixes do not roll back the completion
map: its direct removal at `candidate_intrusion.rs:241` belongs to rollback;
the actual successful admission marks at `423–455` persist. Each exact
relation can execute the marked miss path at most once; a later same-relation
hit has its existing mark. A miss adds
at most one bound cell or four structural children. Relation-sensitive
misses, and the fibers they attach, remain finite. `begin_replay` walks a
finite pair of attachment chains and suppresses each already-recorded exact
ordinary Replay dependency (`candidate_context.rs:3992–4074`). Finite
repeated physical incidences may invoke an empty replay operation, but cannot
create infinitely many dispatch misses. Each published operation queues
finite children; actual acknowledgements consume those slots
(`4156–4228`, `2397–2454`). Diagnostic SCC traversals are finite over the
resulting finite diagnostic graph, and capture's endpoint/row interning
prevents cyclic bound incidence from requiring infinite unfolding
(`candidate_scheme.rs:1708–1760,2633–2693`).

This rules out an argument that a new *endpoint shape* must continually
appear in this candidate. It supports a finite hand-construction candidate
when every required elementary operation succeeds. It is not an observed
run, a complete availability proof, or the existential assertion that the
authentic proposed text successfully reaches S. All cited prior invariants
are successful-prefix results. `try_reserve`, checked identity/accounting,
preflight/collection, receipt checks, capture and finalization can return
availability failures; no failure is converted to completion here. In
particular the finite-key bound does not establish all actual source/HIR
receipts or all resource-success premises. No numerical fiber count or
resource-fit claim is inferred from it.

No declared typing-conflict class has a seed in this endpoint inventory:
Value comparisons involve a row or Function/Function of the same shape;
there is no non-Bottom incompatible structured shape. Effects contain no
Contribution, AnnotationMember or Allowance; all children remain same-sort;
and no record/variant constructor occurs. Diagnostic completion propagates
existing witnesses and cannot manufacture an incompatible-shape seed.
This source-owner classification is evidence about every successful prefix,
not an assertion of `NativeComplete₀` from an empty error list.

## 6. Reuse, rejected shortcuts, and authority boundaries

Reused within actual premises: R336's fixed finite algebra, source table and
L0; R337's successful-prefix identity/default-flow theorem; R341's persistent
source-bound witnesses and same-construction transport; R345's exact four
ports; R346's ordinary replay ownership/coverage through its accepted outcome;
and R348's coordinate/support census and completed-state correspondence.
R348's satisfying-assignment extension cannot supply a source solution here:
section 3 proves this source family has none. Its Lift statement is vacuous
on an empty source solution set. Only its independently justified support and
owner facts are used in the inventory.

Rejected: the single self-applying Lambda as a counterexample; treating a
cycle or a finite graph as finite-model impossibility/existence; a fabricated
transition model as actual source evidence; ordinary API success as
`NativeComplete₀`; memo membership alone as one-dispatch-per-endpoint;
collapsing relation/fiber/occurrence identities; all-bottom/all-top Value
assignments without checking the source demands; and assigning empty Effects
without checking all source/native ports. No withdrawn bypass is restored,
and no natural source or inference rule is weakened.

The newest TeX (hash below) is normative. This finite K0 algebra is not its
regular value graph semantics or evidence-hole H, world, Y_H, complete Call
graph, finite certificate, or BuildLocal search. The obstruction in a
finite-term carrier does not refute a theorem with a different regular
carrier. No alteration of either carrier is authorized. Q1–Q8, BuildLocal,
search completeness, principal packages, whole-language preservation,
independent F1/FK1/foreign-continuation quantifiers, original A/B, and
production all remain outside this result.

## 7. Exact remaining premise and handoff TODOs

`R349-AUTHENTIC-COMPLETION-1` — **Luna, source/actual native lifecycle owner**.
First missing evidence: an authentic ordinary `s_Ω` with the section-2
resolved HIR identities and an actual completed conflict-free S from that
same construction. Required receipts are genuine parser/HIR/binder ownership,
successful complete source collection/admission, and an exact pre-output
snapshot covering kind-tagged rows, every physical bound slot, pending typed
queue, drain/current/saved processing/local owners, and unconsumed replay
slots. Source owners are `yu_syntax::parse_file`,
`yu_hir::shadow::lower_module_with_local_source`, `HirModule::local_source_for`
(not newly inspected/pinned by this lane); consumers are
`step_candidate_source`, `run_candidate_typed_drain`,
`candidate_context_begin_replay`, `complete_replay_child`,
`capture_candidate_graph_inner`, and `finish_candidate`. The current census
maps these consumer boundaries generally; it does not exhibit this concrete
S. A failure/deferred result, unresolved concrete owner, different authentic
tree, or missing same-construction identity prevents promotion to a
source-qualified refuter. No repeated abstract finite-model pass can fill
this receipt by renaming the theorem.

`R349-H0-DISCRIMINATOR-1` — **Luna, only under a separately allocated evidence
packet if needed**. Minimal provisional implementation TODO: expose/read the
actual S immediately before `finish_observations` consumes the candidate
session, paired with the retained authentic source/occurrence/row map.
Capture all H₀ owners named above and availability/diagnostic results, not
only `SolvedProjection` or `candidate_conflicts()`. Exact falsifier for the
candidate inventory is an actual reachable bound/work formula outside the
listed sixty-four keys or an authenticated missing source inequality. A
genuine completed same-source S together with a finite model of exact H₀
would falsify section 3 or its R341 application. No compiler edits or probes
are authorized or performed in R349's current packet.

`R349-W0-REVIEW-1` — **Luna** owns fresh review of these frozen candidate
bytes and the receipt gap, with separate contributors excluded. If the
missing concrete witness is supplied and accepted, the finite-term W0 target
is refuted, and its dependent proof edge must return to authority review.
Do not repair it by excluding Omega, inserting an occurs check, narrowing
ordinary inference, or silently replacing finite terms with regular graphs.
If the witness is not supplied, retain W0 OPEN with the exact receipt above.

Implementation disposition: **NO_SAFE_CODE_SLICE**. Actual admission/dispatch
owners (`candidate_source.rs`, `lib.rs`, `candidate_extrusion.rs`) and
capture/finish owners (`candidate_scheme.rs`, `lib.rs`) were inspected. A
finite-carrier source obstruction alone establishes no compiler defect or
approved production repair. The next discriminating action is at the
source/completion owner, not a further conditional witness theorem. This is
the assignment boundary; no writer continues while waiting.

## 8. Frozen dependencies, provenance, checks, and resources

Compiler-source baseline supplied by Luna:
`60cdd28a3941b42d89f9cb602711b4859d2b737b`. No Git was used by this author.
All following actual SHA-256 values were read with `sha256sum` and match the
frozen contract/census. Older historical TeX pins do not replace the newest
normative file below.

| Direct input | SHA-256 |
|---|---|
| R349 rev3 contract | `f2446b85c2661abdfb03ace13055d22e9ac82e2c5b068c161b6649b1aa807dbc` |
| R349 Luna source census | `bd2d57fcc1b95dc89d258e46db997346b69900893f9ef878f384f4dbaed4472d` |
| R336 rev4 contract / proof | `080ab51650f88ddb7030e2a9bcb0ebfc9cc9b62de29204910e888365f7d03118` / `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R336 review | `d03b7a23bcec2bd0575bf391342f92353b46b840cbcfa70deea7500786fd892e` |
| R337 J / census | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` / `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a` |
| R341 proof / census / outcome | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` / `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb` / `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc` |
| R345 proof / census / outcome | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` / `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b` / `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce` |
| R346 outcome | `25748200d206c375a2e450aff688f692a4bfc5537ef7ba3fdc953423006b6512` |
| R348 proof / source check / outcome | `c4ee2c3cf36301f77c5ea6c941e9257ef52ebca0fd3e90e016d8d0f46b5f3a99` / `61ff50a919ff37f58bf098b87d4044d24cc63f230591e5fa91fb105e8d948829` / `e35d8c6139404da015e981dbc3bc203ece85199b920ce481284df7b3166fe6fd` |
| user audit | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| newest normative TeX | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

| Direct source in `crates/yu-solver/src/` | SHA-256 |
|---|---|
| `candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |

Historical proof authors: R336 Luna `/root` plus
`/root/r336_k0_algebra_prover`; R337 `/root/r337_k0_context_prover`; R341
`/root/r341_k0_source_retention_prover`; R345
`/root/r345_k0_initial_drain_prover`; R346 `/root/r346_k0_replay_prover`;
R348 `/root/r347_k0_end_state_prover`. Censuses/outcomes are Luna-authored.
Individual compiler-source and user-document authors are UNKNOWN. Historical
review/outcome receipts are reused only as supplied accepted dependencies,
not newly authenticated reviewer executions.

Requested role/model/effort: prover / `gpt-6.1-sol` / high. Observed effective
model/effort and own runtime session are **UNKNOWN**. Actual task identity is
`/root/r349_k0_finite_witness_prover`; containing primary session supplied in
the contract is `01a165ee-0212-7af3-8c99-1c1efcf367fe`, not an observed child
session. First observed clock: `2026-10-23 11:08:35 UTC`; exact launch clock
and total active seconds are UNKNOWN. One fixed 3000-second grant, fully
charged, no renewal/carryover. The handoff records the final observed clock.

Checks: direct pinned source reads, manual algebra/port/inventory reasoning,
and SHA-256 comparisons only. No tests, builds, Cargo, executable probes,
Git, network, external tool contact, descendants, model/config changes, or
production/expectation edits. A preliminary search for an unavailable
`docs/spec.md`/`spec/` produced no input and no output file; no dependency was
added. Only the two leased paths were created, this note and
`tasks/agent-loop/inbox/20261023-r349-k0-witness-prover.md`; there are no
scratch files. This note is frozen for intake with the handoff; all writing
stops on submission. No worker or descendant is claimed to continue during
review or while the concrete source/completion premise is outstanding.
