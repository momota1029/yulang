# Conditional value constraints: fresh-result join elimination

Status: independently reviewed local theorem and bounded source/action
correspondence; primary accepted the scoped conclusions in §7.
Baseline: `13c100980a75e294fb78200de51cf702d7499483`.
Exclusive output lease: this file. The baseline has no If/Boolean/String carrier
forms. The primary subsequently froze the implementation delta inspected in
§5.1; that delta establishes the bounded value construction bridge below.
Conditional-result Value-reference incidence remains **PENDING** authority.
Authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
§1.1(1), and `notes/design/2026-10-04-inference-research-playgrounds.md`
“Direction”, “Boundaries”, and “Source-driven playground, 2026-10-14”.
The primary reports explicit user approval for the next actual playground
If/Boolean/String feature: both branches of `if true { 1 } else { "str" }`
contribute, producing `int | str`, without evaluating the condition.

## 1. Frozen statement, scopes, hypotheses and exclusions

Fix one source conditional `if c { t } else { e }` at its original lexical
scope and selected inference level. Let `X` contain every existing value
variable/binder in the condition, both branches, and their shared environment.
Keep resolved ModuleDef/Local/Parameter identities and all original scopes.
Let `C` be the conjunction of every constraint generated for `c`, `t`, and
`e`, together with any pre-existing shared constraints; no branch constraint
is discarded. Let their positive value terms be `T_c`, `T_t`, `T_e`.

Use the ordinary value-subtyping interpretation: types form a preorder
`(D, <=)` with binary joins, modulo mutual subtyping if antisymmetry is absent.
`a | b` denotes its binary least upper bound `a ∨ b`; the only laws needed are
reflexivity, transitivity, `a <= a ∨ b`, `b <= a ∨ b`, and
`(a <= u and b <= u) => a ∨ b <= u`. No finite-model, decidability, structural
reconstruction, or particular type syntax assumption is used. This is an
explicit shared interpretation premise; the Rust bound vectors alone do not
establish a semantic model for all source types.

Allocate a value variable `rho` fresh for this expression, distinct from all
variables in `X`. It remains at the conditional's scope/level, with no
generalization boundary between construction of the two branch links.
For an arbitrary index set `J`, let each `U_j` be an upper consumer term whose
variables are in `X` and whose interpretation is fixed independently of rho.
The executable carrier uses finitely many consumers, but the algebra below
needs no meet or finite-index hypothesis. Consumers in this claim are exactly
inequalities `rho <: U_j`; a negative/invariant nested occurrence, equality,
additional lower bound, or a consumer mentioning rho on its right is not
silently included. Such later source uses remain valid compiler work, but this
local elimination law alone does not discharge their separate obligations.

For **every single shared assignment** `eta : X -> D`, the required conclusion
is the following equivalence, with the existential only over the new rho:

```text
C(eta) and eta(T_c) <= Bool and
exists r in D.
  eta(T_t) <= r and eta(T_e) <= r and forall j in J. r <= eta(U_j)
iff
C(eta) and eta(T_c) <= Bool and
forall j in J. (eta(T_t) ∨ eta(T_e)) <= eta(U_j).
```

The condition's literal value does not occur in either formula. Branch-local
fresh variables, if present, are still part of X with their original binders;
their shared assignment is not chosen separately for each consumer. One may
subsequently project any subset of X by existential quantification on both
sides of this pointwise equivalence, preserving all correlations in C.

Required construction: `C ∧ T_c <: Bool ∧ T_t <: rho ∧ T_e <: rho`, followed
by ordinary consumer constraints. This is the exact common-upper-bound
presentation. It does **not** impose the equality `rho = T_t | T_e` on every
solution: larger admissible result assignments remain possible. Its least
admissible assignment for each fixed eta is exactly the join.

Effects are excluded until the primary supplies the exact action map. This
note claims no effect mapping, effect union, runtime evaluation trace, complete
Call preservation, hygiene, extrusion/equality semantic preservation, global
source soundness, principality, termination, production acceptance, or F5
cutover. It proposes no new supported-source restriction. The full parent
obligations keep their existing status and owners.

## 2. Direct derivation

Write `a = eta(T_t)`, `b = eta(T_e)`, `q = eta(T_c)`, and `u_j = eta(U_j)`.
If C or `q <= Bool` fails, both complete formulas are false. Assume both hold.

Forward direction: take the one witness r supplied on the left. Both
`a <= r` and `b <= r` hold, so the join property gives `a ∨ b <= r`.
For every j, transitivity with `r <= u_j` gives `a ∨ b <= u_j`.
All j use the same r and eta. No marginal witness selection occurs.

Reverse direction: choose the single witness `r = a ∨ b`. The two join
injections give `a <= r` and `b <= r`; the right-hand hypotheses give each
`r <= u_j`. This establishes every original inequality, under the unchanged
assignment to X. The construction introduces no fresh value/effect providers
and edits no source binder or branch constraint. QED for the frozen local law.

In fact, for fixed eta satisfying C and the Boolean check, the complete rho
fiber is exactly

```text
{ r in D | a ∨ b <= r and forall j in J. r <= u_j }.
```

The forward implication uses join minimality; the reverse uses the injections
and transitivity. If the fiber is nonempty its least member is `a ∨ b`.
For J empty, it is the full upper cone of the join and is always nonempty.
Consequently an annotation is unnecessary for the local construction, and
absence of an upper consumer does not authorize choosing the first branch.
This least-result fact under fixed assignments is not a principal-scheme
theorem across all assignments, binders, effect fibers, or generalization.

The consumer formula also equals
`forall j. (a <= u_j and b <= u_j)` by the same join property. Thus
elimination creates exactly both branch-to-consumer inequalities, not a branch
choice, an equation between branch rows, or a new condition-dependent filter.
No solving or unification at generation time is needed.

## 3. Construction induction to be instantiated by source owners

### 3.1 Ordered finite arms and else

The implementation additionally retains ordered arms
`(c_1,t_1),...,(c_n,t_n)` and one else `e`, with n >= 1. Freeze their
original scopes/binders, all their child constraints in C, one assignment
eta to every old variable, and fresh rho exactly as in §1. Define

```text
A = eta(T_t1) ∨ ... ∨ eta(T_tn) ∨ eta(T_e)
B = C(eta) and forall i=1..n. eta(T_ci) <= Bool.
```

For every finite n >= 1 and every upper-consumer index set J:

```text
B and exists r.
  (forall i=1..n. eta(T_ti) <= r) and eta(T_e) <= r and
  (forall j in J. r <= eta(U_j))
iff
B and forall j in J. A <= eta(U_j).
```

Induct on the finite ordered branch list. For a singleton, its value is its
own least upper bound by reflexivity. If L is the least upper bound of the
prefix, binary join injections show `L ∨ a` bounds that prefix and the next
branch. Any upper bound r of the enlarged list bounds L by the induction
hypothesis and bounds a, so it bounds `L ∨ a` by binary minimality. Appending
the else gives A. The two directions now follow exactly as in §2, with the
single reverse witness r=A. Thus the rho fiber is precisely A's upper cone
intersected with every consumer downset, including J empty. Reordering or
rebracketing leaves the join equal modulo mutual subtyping, although the
source schedule retains the actual arm order. Every condition constraint
and child package remains conjunctive; no priority-based branch pruning occurs.

This extension proves arbitrary finite arms mathematically. The repaired
source representation in §5.1 uses each direct child's original occurrence
with fixed local slots, so u8 imposes no per-conditional arm cap.

### 3.2 Local generator induction

The intended local construction step extends the already generated child
constraint packages without deleting them:

1. Visit condition, then branch and else branch in the original source scopes.
   By the child construction hypotheses, retain their entire constraint
   packages and exact positive value endpoints in the same assignment space X.
2. Allocate the conditional's distinct component row at its enclosing level;
   do not alias it to either branch or identify the branch rows.
3. Append the Boolean negative check on the condition endpoint and the two
   positive-branch-to-negative-result inequalities. These are ordinary native
   constraint admissions, with distinct source occurrence slots.
4. Expose the result endpoint to the existing parent consumer. The pointwise
   lemma applies to upper consumer inequalities after fixing the existing
   assignments; effect and generalized/copy consumers require their own
   established premises.

Initially this was an induction step for a supplied generator. Section 5.1
now establishes these steps at the frozen source/action owners for the
explicitly accepted private fragment. An implementation using native worklist
admission can propagate while adding constraints; the step does not require
every variable to have a final type before its consumers are generated.

## 4. Baseline owner and consumer inventory

All locators here refer to the pinned baseline, read using `git show` to avoid
depending on unfinished concurrent implementation.

| Responsibility | Actual baseline owner | Evidence and scope |
| --- | --- | --- |
| Per-occurrence component | `crates/yu-solver/src/shadow_apply.rs`, `ConstraintBatch::candidate_component` | Creates Value/Effect occurrence components and records their positions; conditional must use its own occurrence, retaining the original binder identities. |
| Source traversal/scheduling | `crates/yu-solver/src/candidate_source.rs`, `ConstraintBatch::emit_candidate_source` | Visit/Finish stack visits existing children and constructs an immutable action schedule; no If/Boolean/String arms exist at baseline. |
| Positive endpoint meaning | same file, endpoint allocation and `Action::Link` execution | Formal Names use `CandidateEndpoint::Parameter`; ascriptions preserve exact child endpoints; links call `candidate_endpoint(..., Positive)`. A new branch link must preserve this route. |
| Stored fact activation | `crates/yu-solver/src/lib.rs:11170`, `admit_collected_fact` | Actual store admission/provenance is followed by `constrain_live_value` on positive lower/negative upper; stored records alone are not the operational premise. |
| Direct source link activation | `crates/yu-solver/src/candidate_scheme.rs:1337`, `admit_candidate_value_link` | Constructs occurrence/cause, records provenance, and invokes `constrain_live_value`. |
| Bound storage | `crates/yu-solver/src/candidate_extrusion.rs:811`, `candidate_apply_value`; `candidate_insert_bound_with_evidence` | Canonicalizes, selects directed bound owner/polarity according to levels, then inserts and replays. Same-level row `a <: b` may be stored as an upper of a; the lemma does not require two physical lower slots on rho. |
| Consumer replay | same file, `candidate_replay_bound` | Iterates every current opposite bound, builds the correctly ordered child inequality and drives the owned context replay. This is local loop evidence; all-path replay adequacy is not newly proved. |
| Parent without annotation | `candidate_source.rs`, final `Action::Link` | Links exact body endpoint to existing definition root. With annotation it calls the existing annotation route; no branch-specific bypass is needed. |
| Reference identities/reachability | `crates/yu-solver/src/candidate_value_graph.rs`, `Graph::retain_source` | Original tagged Value identities, owner traversal and Name/Apply fragment construction are retained; new conditional child traversal is pending. |

The independently reviewed
`notes/theory/2026-10-14-value-intrusion-activation-correspondence.md` is reused
for its actual immutable-event, group activation, settlement and complete-drain
mechanism conclusions. Its §1 source domain explicitly lacks these new
constructors. Extending a traversal must establish correspondence for the new
forms before asserting this lemma's source hypotheses there; review attribution
does not supply those missing constructor cases. The source-global event
applicability and typing/equality-preservation premises remain open.

## 5. Deliberate falsifiers and exact pending bridge

These are mathematical falsifiers, not executed probes. In a powerset subtype
interpretation choose `Int = {i}`, `String = {s}`, and `i != s`.

- Dropping the else branch for literal true admits result `{i}` and an Int
  consumer, whereas the required join `{i,s}` is not below `{i}`.
- Equating the two branch rows rejects the shared assignment having these
  distinct exact primitive types, although their union is a valid result.
- Selecting the first branch globally repeats the first counterexample even
  when there is no consumer: `{i}` is not an upper bound of `{s}`.
- Removing the Boolean check admits a condition assignment outside Bool.
  This concerns static checking, independent of which branch executes.
- Taking separate witnesses for branch constraints can accept impossible
  shared environments: if Cthen requires an existing x to be `{i}` and Celse
  requires the same x to be `{s}`, each marginal package is satisfiable while
  their retained conjunction is not. The frozen pointwise theorem preserves
  that incompatibility.

Historical initial bridge checklist, then all **PENDING** for the feature:
parser reachability and literal carriers; authenticated HIR If children and
original scope/binder allocation; immutable source Visit/Finish scheduling of
all three children; exact fresh result endpoint and Boolean/branch actions;
positive endpoint resolution including formals/ascriptions; activation through
actual action consumers; Value-reference owner and fragment traversal through
all three children without pruning; parent/generalization/rendering consumers.
Rendering a union is presentation evidence, not the semantic elimination proof.
No effect action is supplied or inferred here.

That emission/activation premise is supplied for the frozen finite-arm slice
in §5.1. It does not establish conditional-result SCC incidence, effect
semantics or the global parent obligations. One direct method completes the
local algebra and its owning construction bridge; no equivalent retry or
premise reclassification is needed.

### 5.1 Frozen implementation: actual construction and operational bridge

The primary supplied a frozen working-tree delta over the baseline, followed
by a frozen owning-constructor repair. The final source owner SHA-256 is
`4060efb4177b26d5afc395a138fb24c7ef2a641a64f547755775b2c9bd801fd7`.
The
correspondence domain is authenticated successfully formed private LocalSource
whose other constructors/annotations pass the existing source preflight, with
new non-interpolated String, lexical-unshadowed Boolean literals, and If having
any finite nonempty ordered list of complete condition/body arms and an
explicit else, provided ordinary identity/resource checks succeed. The source
builder supports the existing inline OperatorChain and indented statement
body shapes; each branch block follows the existing binding/final-expression
contract. Missing else, interpolated strings, unsupported child syntax and
source identity/resource failures are outside this successful formation and
completed-admission statement. These are observed current carrier boundaries,
not new semantic requirements on the complete language.

The algebra in §3.1 applies to arbitrary interpreted branch types, including
unknown variables. For executable source, assume only that the existing
child and consumer interpretation premises hold at their unchanged owners;
this note establishes the conditional's actual emitted inequalities and
activation, not soundness of every child constructor or solver transition.
Quantify operationally over finite runs in which collection succeeds and the
actual source schedule completes all actions without an availability failure.
Diagnostics may still report an incompatible constraint: completion does not
assert successful typing or publication of such an input.

**Parser and authenticated source construction.** The unchanged parser
`crates/yu-syntax/src/expression/operator_chain.rs` calls
`if_expr::if_nud_normalized`; `expression/if_expr.rs:50` starts IfExpression,
`if_arm_normalized` starts IfArm and its Condition/OperatorChain, and
`if_continuations_normalized` retains each encountered elsif, then the ElseArm
before returning. HIR's `Builder::expression` at `local_source.rs:649–724`
dispatches IdentifierExpression, StringLiteral and IfExpression. It resolves
existing lexical bindings first; only an unshadowed spelling true/false becomes
Boolean, and other identifiers use the original module/local/parameter route.
String rejects interpolation explicitly. `Builder::conditional` at `:728–779`
requires every IfArm before the one ElseArm, exactly its Condition and body,
at least one arm, and an explicit else. It allocates distinct original-owner
LocalSourceIndex slots with `slot`, and `set` records a fresh authenticated
HirOccurrenceId and source range. No type-variable identity replaces a Value
or a source binder.

All children are scheduled in source order, each with
`LocalSourceScope::Expression` of the original conditional, plus its own
Restore(depth) after its expression work. The LIFO stack places each entire
child and its nested work before that restoration, then the next sibling.
`restore` reinstates the existing latest-binding stack; branch-local binders
cannot escape into a sibling. Existing block/local initializer code retains
its own original local and parameter identities/scopes. This establishes one
shared enclosing environment rather than independently selected branch
environments. No condition value is inspected to schedule children.

**Exact result identity and child schedule.**
`emit_candidate_source` at `candidate_source.rs:203–251` calls
`candidate_component` for every original expression occurrence. The If result
is its own `Component(positions[index].value)`; only Ascription entries are
aliased to their exact child endpoints, never an If to a branch. Formal Names
retain Parameter endpoints. Visit at `:275–289` schedules Finish first, then
else, then the reversed arm list with body followed by condition pushes. LIFO
execution consequently completes `c1,t1,...,cn,tn,e` before If Finish. Each
child is visited at the same selected conditional level; child blocks still
use their existing level+1 initializer/generalization rules. Finish neither
installs nor generalizes a branch-specific replacement for rho. Every child's
actions/facts already reside in the same retained action list; the If arm
contains no removal, branch-value test or early selection.

**Native inequalities and unique original occurrences.** Finish at
`candidate_source.rs:378–403` prepares BoolNegative and the original result
component. For each original direct child, it appends exactly:

| Original source occurrence and local slot | Actual value action |
| --- | --- |
| each `c_i` occurrence, `50` | `ValueConstraint(condition endpoint, BoolNegative)` |
| each `t_i` occurrence, `50` | `ValueConstraint(body endpoint, result component)` |
| `e` occurrence, `50` | `ValueConstraint(else endpoint, result component)` |

Each child's effect fact uses that same child occurrence and slot 51; its
semantics is excluded below. Uniqueness follows from the actual authenticated
source tree construction, not the comment's assertion. `Builder::conditional`
calls `slot` separately for every condition/body/else, without reusing an
index. Each call appends a new empty expression slot; `set` assigns its
fresh occurrence. Existing child construction allocates descendants separately
and does not reuse a sibling index. Induction over this tree gives one parent
for each direct child and disjoint direct-child sets for different conditionals.
A nested If receives slot 50 from its parent at its own occurrence and emits
its own checks/links at its distinct children's occurrences; these cannot
collide. Group and Ascription endpoint aliases keep original occurrences
distinct. Value/effect slots 50/51 differ, while each child's own constructor,
export and annotation slots remain below 50 (root Link is 30). These facts
prove uniqueness of the added `(HirOccurrenceId, local_slot)` source constraint
identities without an arm-count-dependent u8 cast. The repaired source checks
`2*n+1` counter arithmetic and ordinary allocation/identity limits; it has no
51-arm rejection or silent truncation. All Boolean(true/false)
literals emit the same BoolPositive-to-literal-row and literal-row-to-
BoolNegative pair, regardless of the bool payload; String similarly emits
its Str pair (`:362–375`). The If therefore has no constant-value pruning.

**Activation rather than storage alone.** Immutable schedules are consumed
by `step_candidate_source`: the current action is executed before
its cursor advances; completion occurs only after the retained action list
is exhausted. New `Action::ValueConstraint` resolves its saved
endpoint via `candidate_endpoint(..., Positive)` and calls
`admit_candidate_value_link` with its exact occurrence and slot. The latter
at `candidate_scheme.rs:1369` constructs the occurrence/cause, admits it with
provenance, constructs the positive lower/negative upper pair, and invokes
`constrain_live_value`. `shadow_apply.rs:1409` maps Component to its original
live component row and Parameter to its original parameter-live-base row;
it does not infer a branch from shape or spelling. `lib.rs:11931–11980`
routes this through `constrain_live` to `run_candidate_typed_drain`. Thus
each retained source action reaches the real native solver entry, rather
than merely creating an inert constraint record. The unchanged bound
insertion/opposite replay owners in §4 remain its actual consumers. Complete
replay/semantic adequacy under every later copy/generalization path is not
inferred solely from this entrypoint call.

**Primitive and parent consumers.** `yu-types/src/lib.rs`, Leaf::component_kind
and Leaf::polarity, classify Bool/Str as the original Value kind with their
proper signs. `lib.rs::value_endpoint` preserves all four leaf tags.
`incompatible_value_shapes` at `:14073` preserves disjoint primitive shapes:
non-Bottom differing positive/negative shapes produce the incompatible
diagnostic witness. Consequently the condition's negative Bool constraint
does not silently admit an Int or Str primitive when that comparison reaches
the normal drain. Root Link at `candidate_source.rs:545` exposes the exact
If result to the existing definition root without an annotation. Annotation
preparation recurses through Function arguments/results to prepare Bool/Str;
`candidate_signature_value` and `candidate_formal_pair` preserve their signs.
The annotation route admits the existing `lower <: negative annotation`
check; its separate positive exposed-interface link remains unchanged.
The local elimination law applies to the upper check, not to a fabricated
equivalence of the entire annotation interface.

Graph capture `candidate_scheme.rs::Capture::intern/expand_node` maps Bool/Str
endpoints to their own Atom tags; `prepare_candidate_fresh_use` reconstructs
those same leaf terms while retaining the existing row remaps. Native Call
port admission and BranchTermArena endpoint matching retain the tags/signs.
`CandidateGraphNode::leaf/polarity` exports them unchanged, and playground
rendering prints that exact finite graph and retained bounds. F5c draft,
summary/walker, normalization, replay and materialization add distinct Bool/Str
cases and closed-arena nodes. These are a static constructor/consumer inventory,
not certification of legacy F5c semantics or of generalized principal schemes.
The playground renders graph constraints; this bridge does not falsely claim
that the renderer itself produces a canonical textual `int | str` type.

**Definition ownership and deliberately pending SCC seam.**
`candidate_value_graph.rs:80–88` pushes every condition/body and else with
the current definition owner. Existing Block traversal assigns nested
initializer work to its own Local Value. Induction on that actual work stack
extends the definition-owned resolved Name-reference coverage to the new
children, with no condition pruning. Its order differs from the source action
order but its exact child set/owner identities do not.

The fragment allocator at `:113–119` still allocates helpers only for Name
and Apply; Apply's child links use only existing helpers. Therefore this
snapshot does not supply an If-result helper or Apply-through-If incidence.
`notes/design/2026-10-14-conditional-value-references.md` is Draft and leaves
the condition-inclusive versus branches-only adjacency to user selection.
Do not interpret the missing edges as proved semantic absence. No claim of
conditional-result reachability/SCC completeness, source-global event
applicability or intrusion-preserving typing follows from this value bridge.
The existing reviewed activation theorem is reused only for its unchanged
bounded activation/settlement mechanism under authenticated event/graph
hypotheses; its old source-domain correspondence is not automatically extended
across this pending choice.

**Effects and remaining parents.** The actual constructor emits condition,
body and else computation-effect inequalities into the If effect component
at each original child's slot 51. They are named here solely to account for
slot identity and actual source actions. No operational effect-selection,
union, handler protection/release, witness/provider lineage, hygiene or effect
soundness theorem is claimed. Global soundness, required principality,
source-global extrusion/association applicability and equality preservation,
complete Call, hygiene, termination and production/cutover remain their
original open parent gates. The local source/action correspondence supplies
their necessary value-generation lemma; it does not close them.

## 6. Checks, runtime and commit packet

Static checks performed: scoped `rg`, read-only `git show` at the baseline,
and inspection of the role registration/pins and governing rules. There is
no `spec/` directory in this checkout; no missing file is used as a premise.
No compiler code, tests, expectations, shared records, configuration, questions
or Git state were mutated. No build, test, executable probe or measurement ran.
At most three lightweight shell reads ran concurrently; no heavyweight process
or child agent ran. Requested model/effort: `gpt-6.1-sol` / high; observed
effective runtime metadata: unknown. The registered prover role has no
model/effort pins; role configuration is not evidence of live routing.

Pinned direct dependencies (SHA-256 of the baseline blob, not unfinished
working-tree files):

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `e62256c55c68d815ef7f23f87bb7fe48d0f427571a836557e7314dd0f0616d1f` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `c94e66e1b1bae83bd604f00174128e21ef66c3f6e490697584e41daaaaadf4ec` |
| `crates/yu-solver/src/lib.rs` | `e5b4531d30e7b991abad6b6e688fd15fb0856b25495ff97c8b9fe6ccc2292e3c` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `a8449a11b1db02080c8c8cea536a23e07a79917951174971e65ba05be1e2073e` |
| `crates/yu-hir/src/module/local_source.rs` | `8008b84738990cb22199d386129ecb810f86c907e222da40411cddb18eb279f7` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-04-inference-research-playgrounds.md` | `072b864b0fbe034dc9b6a71eadfb1765bc19d8538d4d0c038c91f64310457ff6` |
| `notes/theory/2026-10-14-value-intrusion-activation-correspondence.md` | `72ac1d304a556fc1af1bfe8757aaac8b920338168553149e87def671b60ef4a1` |

Frozen implementation dependencies for §5.1 (SHA-256 of actual working-tree
files after the primary's owner repair; `delta` compares to the baseline):

| Path | SHA-256 | Baseline relation |
| --- | --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `fab5436a6f37b795c7fb6553c320e2ed942d2ab850d3a446c1fa3e2e3c6ceeaa` | delta |
| `crates/yu-hir/src/module/source_annotation.rs` | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` | delta |
| `crates/yu-types/src/lib.rs` | `c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b` | delta |
| `crates/yu-solver/src/candidate_source.rs` | `4060efb4177b26d5afc395a138fb24c7ef2a641a64f547755775b2c9bd801fd7` | delta |
| `crates/yu-solver/src/candidate_effect.rs` | `2539188fc293e476a38b489132b01f05d8c8de636f0cf435ace26c8a52ed92d3` | delta |
| `crates/yu-solver/src/candidate_scheme.rs` | `c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd` | delta |
| `crates/yu-solver/src/candidate_value_graph.rs` | `449b223d11a7b3c5286fd8c1277ff1d2c48ced52927622d98dbef173f0459346` | delta |
| `crates/yu-solver/src/lib.rs` | `91938447f78b6ca6b252a67641f30c2e20f05193d112aa7f0019a87caf6f93e3` | delta |
| `crates/yu-solver/src/term.rs` | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` | delta |
| `crates/yu-solver/src/candidate_call.rs` | `a04cb80e890da1885086249d03f769e1717cf0acedde2553c179be928844eb56` | delta |
| `crates/yu-solver/src/shadow_apply.rs` | `cd55eb486a17f5a2d487cfd3ef016a6334a625229f15784c88d6237aaafd87f7` | delta |
| `crates/yu-solver/src/f5c_draft.rs` | `cb67684c633214878c1795d896aca02b525ebf8de4e5cbd3aaf8de7a8e6c433d` | delta |
| `crates/yu-solver/src/f5c_generalization.rs` | `928607961bff9ab747fd759aed1dacd3aa13abc9e20bf3bb8a957a4c7bd12ffb` | delta |
| `crates/yu-solver/src/f5c_generalization/flat_source_arena.rs` | `0abc91b90303818bd372bc33d1e391e24a2bb747df70984cad8f54f5d60f3af7` | delta |
| `crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs` | `ff8b117e7578d93f1d441faec132df4859b7118c5a0d56d1044dbb3f2ab913b1` | delta |
| `crates/yu-solver/src/f5c_materialization.rs` | `a342860980dc14dd6dc10996adf992946e1b420b6d3d8ee176a77937d0c6a93b` | delta |
| `crates/yu-solver/src/f5c_normalization.rs` | `da57ee8fc3dd3a604ef5bf65457cf0c4d38fb976eb9e080e8520ea6a1e97728a` | delta |
| `crates/yu-solver/src/f5c_replay.rs` | `71fb166c38dbd93571abcbc3ff290b3b79fe2a4ecba8159edd5f60933c8b3b2a` | delta |
| `crates/yu-syntax/src/expression/if_expr.rs` | `77ae21897cf23988c394686cb823b4f3d731b53aa483566a73c67295a7326fba` | unchanged |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` | unchanged |
| `tools/inference-playground/src/render.rs` | `96640f6b604b920b2507c1e0ceb9779a0f4d04f4ad81cbddf4d6c8f0aa2f7da2` | unchanged |
| `notes/design/2026-10-14-conditional-value-references.md` | `48006bd81621486f6edcdfd479e8435530ba636f1253df92b716c314f60b162a` | new Draft, no authority |

The follow-up used only narrow static diff/owner inspection and hashing,
including verification of the exact repaired candidate_source hash. No
checks were delegated or duplicated. The primary reports ten conditional
integration tests and the exact child-occurrence test passed on its frozen
implementation; these are primary-owned executable evidence, not checks run
by this leaf or premises replacing the derivation. At producer freeze this
artifact was unreviewed; §7 records the subsequent independent review.

Commit packet (producer's frozen candidate before independent review): exact path
`notes/theory/2026-10-14-conditional-constraint-join.md`; baseline
`13c100980a75e294fb78200de51cf702d7499483`; local finite-arm derivation and
bounded source/action bridge unreviewed; direct dependency hashes above.
Conditional-result SCC incidence remains pending user authority. Proposed message:
`research: derive conditional fresh-result value join law`.
Shared-record deltas for the primary/curator: record local fixed-assignment
finite-arm fixed-assignment join elimination and actual bounded source/action
correspondence, pending independent compiler_referee review; record the exact
still-open conditional-result SCC choice and original global parent gates.
Keep soundness, required principality, complete Call, hygiene and cutover open.
Next action: fresh independent proof review of this frozen artifact and its
hashed dependency snapshot. No shared record is changed here; writes stop
before that review.

## 7. Independent review and primary consumption

The fresh `compiler_referee` reviewed the producer-frozen artifact at SHA-256
`3da339d88115270b1c5f0ece7eb932a4d4fbd1cd5788f04dc6f65eeb0a7b128c`
and independently checked all 22 implementation dependency hashes. Verdict:
PASS for the original finite-arm local theorem and bounded source/action
bridge, with no blocking, major or minor findings in that scope. The review
was read-only and used no test pass as a proof premise.

The primary accepts: pointwise elimination under one shared assignment; the
least-result fiber and empty-consumer case; actual all-child construction;
unique child-owned occurrence slots; operational native admission; and the
bounded primitive/root/annotation/fresh-use consumer correspondence stated
above. These results discharge this local value-generation obligation and
are available to the unchanged global parent proofs. No equivalent local
proof retry is needed.

Conditional-result and Apply-through-If incidence still await the separate
user decision and construction. Source-global event applicability, full
replay/copy semantic adequacy, soundness, required principality, complete Call,
effects/hygiene, termination and cutover remain open at their existing owners.
This acceptance changes neither their statements nor their required evidence.
The primary synchronized the current task, research queue, design index and
conditional implementation checkpoint. Only status/provenance was appended
after the reviewed artifact; its derivation and source correspondence remain
unchanged.
