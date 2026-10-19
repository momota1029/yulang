# R137: a locally generalized identity returned through a closure

Status: **candidate conditional derivation and source/native correspondence**.
Author: `/root/r137_proof`, constructive proof leaf assigned by Luna `/root`.
This author cannot independently certify the result. Fresh review and adjudication
belong to Luna. Ordinary source preparation and actual CLI/WASM execution remain
separate, unobserved premises of this packet. All original A/B and production
gates remain OPEN.

Contract: `tasks/agent-loop/sprints/polymorphic-escaping-closure-20261020-r137-rev1.md`,
revision 1, SHA-256 `b9ad941e29dc650818b9da5468156b07ec41722c1616bdc90e97846857f2c5fc`.
Baseline supplied by Luna: `93385cb6ab1e83a769e84af4997d39b9f57c9684`.
Luna's assignment reports prospective spec and compiler/source reviews CLEAN;
their named receipt files were absent when inspected, so receipt hashes are
UNKNOWN here. This note does not independently re-adjudicate those reviews.

## Fixed parent application and premises

The original sprint outcome is a finite current-entrypoint example composing
local generalization, lexical capture, closure escape and three independent
clients. Its parent is proof-backed source correspondence for Yulang inference
and evaluation. The fixed source is:

```yu
my identity x = 0
my make seed = { my identity x = x; \unused -> identity }
my chooser = make ()
our int_result = chooser () 7
our bool_result = chooser () true
our string_result = chooser () "ok"
my main = int_result
```

The code block's contents with one final LF comprise 218 UTF-8 bytes, SHA-256
`cd7448c79b2997f1bfda9bf2533d2a2c0ff152aec886f19a03d36d831e3f0944`.
The quantifiers below range over these seven roots, their authentic occurrences,
and the three listed clients only. They do not range over arbitrary source,
environments, continuation frames or foreign continuations.

Separate the following premises and evidence:

- **P-FORM:** the ordinary parser and `lower_module_with_local_source` successfully
  form the authentic retained source for these exact bytes. This includes syntax,
  admission, source identities and all `our` roots. No constructor was run here.
- **P-PREPARE:** `yu_playground::prepare(source, name, false)` completes its ordinary
  `CandidateInference::solve` path without candidate conflicts. P-FORM alone does
  not imply this. It is the first unobserved end-to-end source/inference premise.
- **P-RUNTIME:** `RuntimeProgram::from_hir` accepts that same HIR; the selected
  definition exists; allocation and the supplied step budget suffice. The
  operational derivation below concerns this source-qualified program and the
  inspected machine, not an observed run.
- **E-RUN:** actual successful CLI selections and browser/WASM smoke results.
  These are implementation/verification evidence owned by Luna and NOT_RUN by
  this leaf. P-PREPARE and E-RUN are not inferred from source inspection.

Conditional conclusion: under P-FORM, the constructors select the inner local,
publish its scheme before the captured use and construct distinct FreshUse
instances for the three `chooser` occurrences. Under P-PREPARE and P-RUNTIME,
the evaluator derivation yields selected outputs `7\n`, `true\n`, and
`"ok"\n`; selecting `main` yields `7\n`. These are predictions pending E-RUN.
The proof below establishes the precise constructor/remap statements; it does
not promote them to general native soundness or arbitrary propagation
noninterference.

## 1. Authentic lexical join

Let `D_outer` be the module definition `identity`, `D_make` the module definition
`make`, `L_id` the local `identity` owned by `D_make`, and `P_x` its parameter.
These labels stand for actual constructor-owned IDs, not IDs synthesized by this
note. In `crates/yu-hir/src/module/local_source.rs`:

1. `form` (594) wraps named root parameters as retained Lambdas. `Builder::block`
   (1378) obtains the private local binding from its original statement, records
   `HirLocalId { owner, ordinal }` and its own parameter identities, and retains
   the final inline Lambda. Nested non-private bindings still fail at 1414.
2. The block's LIFO work schedule (1495 onward) processes the initializer before
   its final expression. `Work::Initializer` (703) temporarily installs `L_id`
   for a named function, then installs its parameters. Thus the initializer's
   `x` resolves to `Parameter(P_x)`, not a recursive `identity` occurrence.
3. `Work::Publish` (749) restores the temporary initializer scope and installs
   `Local(L_id)` into the enclosing block scope. `push_binding` (795) maintains
   the most recent lexical binding by spelling; `restore` (831) restores the
   saved predecessor rather than guessing a binder from spelling later.
4. The final inline Lambda temporarily pushes only `unused` (1040 onward).
   Its body `identity` is resolved at 1069 by `latest` before the fallback module
   namespace. The latest entry for `identity` is therefore `Local(L_id)`.
   `D_outer` is a different namespace definition and is not this reference.

This is a finite derivation from the authentic builder schedule conditional on
P-FORM. The outer shadow is intentionally distinguishable: invoking `D_outer`
would return integer zero, while the selected local initializer returns its
argument. No universal lexical-correctness claim is needed or obtained.

## 2. Local generalization occurs before the captured use

`candidate_source.rs::emit_candidate_source` (827) joins the carrier to the
actual HIR by owner and pointer identity (833 onward), verifies its occurrence
ownership, and allocates local slots from the retained binding IDs (888).
Parameter Names use their parameter endpoints directly (897); the body of
`L_id` therefore has the same value row as `P_x`.

The source worklist starts the definition at level 1 (963). Visiting a Block
(1050) schedules each initializer at boundary + 1, its Install at the boundary,
and the final expression after those Install actions. A Lambda visits its body
at the same level (1008); it does not introduce an artificial generalization
boundary. Hence the local identity initializer and `P_x` are at level 2, its
publication boundary is 1, and the returned inline Lambda/body use is at level 1.

`Work::Install` (1138) removes `L_id` from `active_initializers` before scheduling
the later body. It emits initializer computation effects into the block once
(1144); those effects are outside the generalized value interface. For this
unannotated local it schedules `Action::Install`. The later `identity` Name
(1318) therefore schedules `Action::Local`, not the active-initializer Link.
The function's authentic self-binding support has not been removed or bypassed;
this initializer simply contains no self reference.

The actual driver `step_candidate_source` (1679) handles Install in two stages:
it obtains the positive initializer endpoint, enters `Stage::PublishLocal`, and
only after `install_candidate_local_term` succeeds does it increment the action
cursor (1694). `candidate_scheme.rs::install_candidate_local_term` (1971)
publishes `LocalScheme { id: L_id, root, boundary: 1, capture_region }` exactly
once into that slot. A completed schedule thus cannot consume this Local action
before publication. Failure/suspension is not counted as publication.

This scheme is a retained live graph interface, not a closed F5 scheme. Its
**value projection** is the identity interface conventionally written
`forall a. a -> a`: `lib.rs::admit_lambda_fact` (11322) takes the negative
parameter row and positive same-row body endpoint, and constructs a Function.
The native Function retains four ordered ports: argument, argument effect,
result effect and result. Its entry-effect forcing edge and body-effect edge
are retained and propagated (11361 onward); no effect edge is erased by the
displayed value projection.

Apply this lemma immediately to the sprint: the `identity` captured by the
returned Lambda is a use of the already published local graph. It is neither
an open recursive initializer root nor a use of the outer zero-returning scheme.

## 3. FreshUse and the exact extent of independence

The Local action calls `route_candidate_local` (1998), which reads the published
root/boundary/ID, captures that graph, and invokes `prepare_candidate_fresh_use`
(1557). Graph capture canonicalizes a row and records
`local = level > boundary && !non_generic` (757–779). Reconstruction applies
the stronger current guard `row.local && current_level > graph.boundary &&
!current_non_generic` (1606). It uses a map private to this reconstruction:
one canonical source representative has one image within a use; eligible rows
in separate uses allocate separate fresh rows. The new `context_use` is minted
before reconstruction. A fresh-use map is not a provider, witness, original
source row, or extrusion-parent identity.

For this local initializer, the only value connection of `P_x` is its identity
Function at level 2. Neither `seed` nor an older value occurs in its body. Before
local capture, initialization relates its *computation effect* to the block
effect, not its parameter value row to an older parameter. Thus the identity
value coordinate is eligible at boundary 1; the Local use reconstructs it at
level 1. Latent Function ports and their bounds are carried with it; effects
that are legitimately older retain the native guard and are not declared fresh
merely because the value coordinate is fresh.

Each completed module SCC is subsequently captured at boundary **0** by
`execute_candidate_graph_plan` (1361, capture at 1422). The dependency graph for
this source is acyclic: `make -> chooser -> {int_result,bool_result,string_result}`
with edges written here in producer-to-client direction, and `int_result -> main`.
The outer `identity` has no edge to the captured inner reference. Dependency-first
execution publishes a completed producer graph before its incoming client use.

There is no level-zero source binder or annotation in this fixture. Collected
rows/parameters start at level 1 with `non_generic = false` (`lib.rs` 10130–10178);
source initialization assigns levels 1 or 2 (`candidate_source.rs` 1585).
FreshUse allocates at the corresponding source use level. Native extrusion
copies at the owning endpoint's target level (`candidate_extrusion.rs` 21,
115; endpoint ownership at 912/944), and qualifying intrusion combines existing
levels by minimum and flags by disjunction (`candidate_intrusion.rs` 667–683).
These operations preserve levels at least 1 and a false flag on these closed
unannotated coordinates. This arithmetic observation does not disable either
operation. In particular it establishes the boundary-0 eligibility of the
polymorphic identity value coordinates; a general rule that every captured
local coordinate is eligible at every boundary is neither assumed nor proved.

The `make` use in `chooser` is one module FreshUse; the three syntactically
different `chooser` Names are three further module FreshUses. Module routing
(`route_candidate_graph`, 1474; `instantiate_candidate_graph`, 1911) reconstructs
the producer graph with the use's occurrence, level and context-use, then links
the reconstructed root to that occurrence's own value component. The three
identity argument/result coordinates at reconstruction can therefore be named
`a_int`, `a_bool`, `a_string` with distinct allocated images, while each use
retains its own argument/result equality. The Unit argument of `make` constrains
`seed`; each Unit argument of `chooser` constrains `unused`; neither is the
identity's `x` coordinate.

This conclusion is stronger than counting routes: `prepare_candidate_fresh_use`
reconstructs Row nodes through its row map, reconstructs all four Function ports
through its term DAG (1717–1777), and retains context/bundle/evidence remaps.
`begin_candidate_fresh_bound` (1863) obtains both actual restored bound endpoints
from this same FreshUse, preserves owner polarity, and supplies the exact source
bound, mapped relation, imported antecedent and `context_use` to restoration.
`step_candidate_local_use` (2168) completes bound restoration before linking the
fresh root to the Local occurrence. The module path similarly restores bounds
before publishing its incoming route. These are native owner calls, not a model
checker whose input presupposes those calls were emitted.

The distinct route images establish **independent instantiation at these
constructors**. They do not by themselves establish a theorem that every later
contextual replay, qualification, extrusion equality and consumer preserves
arbitrary cross-route noninterference. This packet has not enumerated the exact
R137 restored-bound/parent-pair census or independently proved that stronger
native transport property. Its first missing source-level evidence is the
actual P-PREPARE run; the planned three-client integration is a finite falsifier
for interference, not proof of the general transport property. Keep the latter
parent A/B obligation OPEN at `prepare_candidate_fresh_use ->
begin_candidate_fresh_bound -> candidate_begin_bound_restoration/
candidate_context replay -> qualifying intrusion` and its owning solver lane.

For the finite mathematical value projection, distinct `a_int`, `a_bool` and
`a_string` admit the respective constraints `Int <: a_int`, `Bool <: a_bool`,
`Str <: a_string`, with each corresponding result following that same identity
coordinate. No client supplies a constraint to another client's coordinate at
these constructor joins. This is a compatibility derivation, not a claim of
principal types or proof of solver completion.

## 4. Runtime capture, escape, application and selection

`RuntimeProgram::from_hir` (program.rs 262) lowers the authentic retained forms.
At 478 it copies each Name's resolution; unannotated parameters and local names
are observed as values. At 510 it creates Lambda instructions with original
parameter IDs and body labels; these unannotated parameters have Value role.
At 531/537 it retains Apply and Block children with the original local binding
IDs and initializer labels. No runtime name search by spelling substitutes for
the HIR resolution.

Write `E0` for the initial runtime environment. Evaluating module `make` produces
closure `M = (seed, block_body, E0)`. Evaluating `make ()` uses the captured
environment of M and binds its Value parameter to Unit, producing `Eseed`.
This follows from `Machine::evaluate` Lambda/Apply (639/657), the Closure branch
of `Frame::Callee` (930), Value-role entry (982), and `Frame::ValueEntry` (1097).

`begin_local` (1935) evaluates `L_id`'s initializer, and `Frame::Local` (1119)
stores its resulting closure `I = (x, x_body, Eseed)` in its own cell. The local
binding is nonrecursive for this source: its initializer references `x`, not
`L_id`. The nonrecursive branch extends the environment after initialization
(1170). Even the recursive mechanism is retained; it is not used to explain
this finite nonrecursive binding.

The block's final Lambda is now evaluated in
`Eid = extend(Eseed, Local(L_id), cell(I))`, yielding
`C = (unused, identity_body, Eid)`. The module `chooser` caches C. Returning from
`make` does not rewrite C's environment or remove its cell: environments and
cells are machine-owned arenas, closure data stores an environment index (648),
and `extend`/`bind` append frames/cells (2017/2025). The frame stack returning is
distinct from the captured environment chain. This is the specific escape step
that a test of a still-active local invocation would not establish.

For each `v` in `7`, `true`, `"ok"`, evaluate the left-associated expression
`(chooser ()) v`:

1. `chooser` observes cached C; applying C to Unit binds `unused` in a fresh
   extension of **C's saved Eid**, then evaluates its body.
2. That body is `Name Local(L_id)`. `evaluate` (574) and `lookup` (2006) match
   the actual binder ID through the saved environment chain and obtain I.
   `NameConsumption::Observe` returns that received value (1904). Neither the
   caller's environment nor module `D_outer` is the lookup target.
3. Applying I to v uses **I's saved Eseed**, binds its original parameter `x`
   to v and evaluates `Name Parameter(P_x)`. It returns that same v. No earlier
   invocation mutates I, C, their saved environments or another invocation's
   parameter cell. Each bind allocates a new cell.

Unit, integer, Boolean and string constructors are ground values (526 onward).
These applications create no operation, handler, continuation or computation
formal. The ordinary Value argument is forced even when `seed` or `unused` is
unused; their Unit values make that forcing explicit rather than bypassing it.

`RuntimeProgram::from_hir` retains the source demand classifier (program.rs
616–643): Apply/If/Catch/nonempty Block roots are scheduled; value definitions
materialize on demand. Here `chooser` and the three result applications are
scheduled, while the outer identity and `make` are Lambda values. `main` is a
value Name root. `start_source_schedule`/`Machine::start` (292/302) retains that
source demand schedule, rather than replacing it with inference SCC order.
`begin_root` (1851) evaluates uncached definitions and returns the selected
definition's cached value after the schedule. `definition_named` (program.rs
243) matches a unique HIR definition name, independent of its `our` visibility.
All three result definitions therefore evaluate their own client applications
in one machine schedule; a separate selected-result invocation starts a fresh
machine. `main` reads `int_result` and returns the same integer value.

Finally, `yu_playground::execute` (lib.rs 167) first calls ordinary prepare,
constructs this runtime program, selects the root and runs the machine. Its
formatter (190) renders integer text, `true`, and a quoted debug string, then LF.
`apps/yulang-wasm/src/lib.rs::run` (11) calls this same execute function with
`scoped = false`. Thus CLI and WASM predicted value outputs have a shared source
consumer. This does not establish a built browser artifact or browser smoke pass.

## Reuse, exclusions and exact next evidence

Reused only within their premises: R134's note locates the earlier admitted-root
visibility/carrier disagreement; its historical conditional repair does not
prove present P-FORM. The existing `cli_demo_identity` source selects three
top-level identity clients; `cli_returned_closure` captures integer 7 through a
returned closure. They are useful adjacent falsifiers, not evidence that R137's
locally generalized identity escape ran. `candidate_context_tests` contains
authentic local capture/FreshUse inspection under different fixtures; those
tests were not run or imported as a proof of this consumer path. No old failed
ordinary-source packet is treated as an accepted R137 constructor receipt.

This applies the lexical/publication/FreshUse/runtime lemmas back to R137:
the finite expected path now has named authentic producers and consumers, and
the first missing evidence is localized to ordinary preparation, then execution.
No new semantics, annotation, source restriction, bypass or production edit was
introduced. Original constraint generation, accumulation, live propagation,
levels, extrusion, qualifying intrusion and generalization remain operative.
No residual/provider/witness or original/copy lineages are identified. F1, FK1,
foreign-continuation and every other independent parent quantifier are untouched.
General let-polymorphism, universal lexical correctness, soundness, principality,
all-environment contextual transport and production authority remain outside
this finite result and OPEN where required by their original owners.

**R137-PREPARE-RUN-1 — Luna implementation/verification.** Required input is the
exact 218-byte source above and the frozen source pins. Produce the approved
isolated CLI test selecting all three definitions, then the approved browser/WASM
build and smoke selections. First required evidence is successful ordinary
`prepare -> CandidateInference::solve`; next is actual selected completed values.
Falsifier: syntax/source admission fails, local scheme is unavailable, any
candidate conflict, wrong/cross-constrained client, outer-zero capture, missing
environment, runtime/inference disagreement, resource failure or unavailable
selection. Stop on the first failure and return its exact owner; do not revise
the source to make the conclusion true.

**R137-NATIVE-TRANSPORT-1 — solver proof/source owner, Luna to assign only if
needed.** The remaining stronger premise is preservation through the exact
restored native bounds/parent-pairs, beyond the inspected fresh-map joins.
Owners: `candidate_scheme::{prepare_candidate_fresh_use,
begin_candidate_fresh_bound}`, `candidate_extrusion::{candidate_begin_bound_restoration,
candidate_step_bound_restoration_child}`, contextual replay and qualifying
intrusion consumers. Inputs must include an authentic R137 HIR/session and its
actual retained remaps, not synthetic transitions. A minimal **provisional**
implementation TODO, only under a separately granted lease, is a read-only
retained-route observation of the three occurrence maps plus their restored
bound endpoints and canonical representatives. Falsifier: a client identity
coordinate is reused before permitted same-use canonicalization, a restored
endpoint escapes its use map, or a later equality joins distinct clients through
an unqualified/wrong lineage. This note does not authorize that instrumentation,
require it before the already approved finite checks, or claim it was run.

No production implementation TODO is justified by a currently observed failure.
Fresh independent review is the next evidence boundary for this frozen note;
the author's writing stops at handoff. Dependency hashes, read-only checks,
resource receipt and the single handoff are in
`tasks/agent-loop/inbox/20261020-r137-proof.md`.
