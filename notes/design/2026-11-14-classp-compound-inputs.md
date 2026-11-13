# Class P: compound input producers and a larger recursive class

Status: proof companion, 2026-11-14. Continues
[recursive peeling](2026-11-13-classp-recursive-peeling.md) and the producer
table in [actual capture depth](2026-11-13-actual-capture-depth.md).
The owner decisions in `spec/06-roles.md` §6 remain unchanged, including
settled-output deferral, actual-input sharing and actual-position K2.

**Result:** unconditional accessibility for a strictly larger recursive
subclass with multiple arguments and compound child inputs. Separately, a
general local producer derives finite readback and actual root recovery for
nominal-rooted compound child inputs. General `ClassPProducer` is still open.
No Step, guard, emitter or previous definition is changed.

## 1. Exact scope of the closed accessibility theorem

`GeneralNominalSpineAccessibility.Spine` fixes a set A of active roles and a
unary nominal name L. Its declaration restrictions are:

1. Active roles have at least one unnamed argument. Their arities can differ.
2. Every active declaration with children has translated queries
   `L(v) :: rest`, where v does not occur in the variable-name list of rest.
   The remaining queries can contain arbitrary compound patterns.
3. Every child has an active role and its first argument is v. Its remaining
   arguments can be arbitrary checked patterns, including materialized
   compounds. There can be several children and recursive role cycles.

Active leaf declarations and unreachable declarations are unrestricted.
Associated equations, demanded outputs and output-only binders are
unrestricted subject to the existing `Checked` and Step guards.

The source conditions are `InitialSource`, an active root, a retained first
input `.source i`, and the initial semantic equation

    every initial source model m satisfies m(i) ≈ L^n b,

where b is a scalar and n is finite. This describes initial source data;
it assumes nothing about future traces, finite covers or installation depth.
The concrete families also satisfy `PointSource` and have models.

`peeling_spine` embeds the entire preceding peeling class.
`SpineExamples.not_unary_peeling` proves that the new binary example lies
outside it. Thus the increase is formal, rather than just a new fixture for
the same class. Restricting this class first to no outputs, then to no
output-only binders, then allowing both gives the ordered subfamilies below.

This is **not** unrestricted item (1) of the task. The decreasing first
argument must still be a forwarded variable from a unary nominal head.
It does not cover unary `Show (pair (list int) int)` with recursive descent
through several pair positions, or a compound expression in that first
child position. Those remain among the general producer obligations.

## 2. Actual capture and site production

`CaptureNames.inspect_named` and `many_named` prove by mutual induction on
the real inspector that every produced capture name occurs in the finite
query syntax. They allow arbitrary interval endpoints and arbitrary optional
origins. Deferred or conflicting inspection cannot fabricate a capture.

For the first query `L(v)`, the existing nominal-capture theorem puts every
capture at `.nominal parent L 0`. Since v is absent from all remaining
queries, `distinguished_capture` proves that **any** usable representative
of v has that origin. This handles the emitter's choice of representative;
it does not assume which witness the emitter chooses.

`SpineAccessibility.child_projection` follows actual production:

* extract a clause from the packet's emitted children;
* its first argument makes v `Needed`, hence the existing GenerationGuard
  supplies a usable capture;
* any `OriginAt` witness at position zero names v, since every clause has v
  there, including a different possible clause witness;
* `SharedEmission.retains` records the exact projected origin in the child.

Induction over every actual-inspection Step proves `sites_paths`. For each
registered site there is a literal birth depth d, an `AtDepth` certificate,
and first input `p(d)`, where p(0)=source i and p(d+1)=nominal(p(d),L,0).
Administrative updates and aliases preserve those recorded sites. Source
formation rules out enqueueing an unregistered generated demand.

## 3. Why this subclass has a source-fixed budget

Nominal argument invariance gives the following carrier fact:

    m(i) ≈ L^n b and Observes(m,p(d),x)
      imply n = d+k and x ≈ L^k b for some k.

At a successor, invert the actual nominal observation. At k=0 a scalar
cannot have a nominal head. Otherwise exact nominal argument invariance
removes one L. Therefore d ≤ n. Nominal bodies are never inspected.

For any prospective installing packet, the actual `Installable` certificate
provides a model of the current journal. Restrict that same model backward
along the trace to obtain the initial equation. `SiteHolds` supplies an
observation of p(d), so d ≤ n. This is the standalone theorem
`installed_depth_bound`, with no simulation or future-bound premise.

The argument does not require consistency preservation for every possible
state: an inconsistent state cannot supply this installation witness.
Repeated expansion of aliased demands does not defeat the bound. Each
literal child still increases birth depth and extends p by one projection.

Refinement cannot enlarge this distinguished input: every successor model
still satisfies the same closed initial equation. Source holes in other
arguments may be refined, but cannot increase this projection depth.
There are zero genuine hole eliminations in the input component used by
this proof. **This is not extraction of the requested general global
hole-elimination history.**

The existing invocation-depth construction then bounds invocation and
allocation identities, enumerates reports and exact signatures, and builds
`SignatureCover`. Its accessibility theorem combines the finite count of
missing signatures with accessibility of administrative steps. These are
the existing full-carrier bounds, not a new simplified executor.

## 4. Nominal compound roots: a general local producer

The old compound fallback is not, by itself, an obstruction. Its two source
IDs are distinct syntactically, but the existing recovery operation accepts
a proof that their values are equal in every current journal model.
The new modules construct that proof for the following precise class.

Let a normalized emitted argument translate to the quotation of a finite
`Expr Nat` with a nominal root. Its descendants can include arbitrary-arity
nominal nodes, canonical structural nodes and scalar nodes. Variable leaves
are shared declaration-variable names. The explicit quotation premise does
not cover deferred queries or multi-name variable queries automatically.

`CompoundReadback.quote_recipe` constructs the recipe by induction on this
finite term. `schemas_component` embeds each recursive recipe in the actual
folded schema. Entering a nominal node switches every nested variable use
to actual mode, including uses under structural descendants. Consequently
the root request schema is independent of its lower/upper mode.

`usable_same` proves that any two usable captures of one name agree in every
packet model. `representative` chooses one such capture per name, and
`input_coherent` uses the existing InputCoherence guard to substitute that
same origin at every actual variable use. The default in representative
is unreachable at every used recipe leaf: the guard supplies a usable
capture there. No interval interior is selected.

Thus `input_request_readback` derives a finite symbolic term for each
materialized endpoint from its actual schema. `input_over_basis` composes
this term with supplied capture readbacks over H; it introduces no leaves
beyond H. **Producing those capture readbacks over the fixed initial H is
still a premise**, not established by this composition theorem.

`ReadbackFunctionality` proves that two source IDs satisfying the same
canonical finite term have equivalent values. The intermediate theorem
requires unique root observations and canonical structural tests. Source
IDs supply uniqueness; projection uniqueness follows by nominal invariance
or the existing canonical structural payload theorem. These conditions
are explicit, rather than silently treating every possible Origin as unique.

The producer-to-consumer connection is complete locally:

1. `CompoundEmission.emitted_requests` derives the lower and upper request
   membership from the real canonical emitter for a particular clause and
   argument position, identifying their targets with that child's endpoints.
2. `CompoundRecovery.trace_coherence` retrieves InputCoherence from the
   actual transition history, rather than inferring it from packet membership.
3. `historical_child_endpoint_equal` combines both request readbacks in
   every current journal model to prove `EndpointEqual` for that exact child.
4. `historical_child_root_recovered` proves that, if its stored origin is
   missing, the existing recovery returns the lower source ID as an actual
   representative justified by this equality.

The translation premise uses the real double normalization: emission puts a
normalized pattern in a Request, and schema generation normalizes the
Request again. No normalization-idempotence theorem is presumed.

This does not equate overlapping intervals or equate different demands
merely because some endpoints coincide. It derives equality of the two
endpoints of **one constructed compound input**, using its actual shared
substitution. Same-input merging remains unchanged.

## 5. Concrete checked source families

The carrier declarations in `SpineExamples` represent these role fragments:

```yulang
impl ShowWith (list 'a) (list 'b):
    where 'a: ShowWith(list 'b)

impl ShowWith int 'ctx
```

The initial inputs are `(list^(k+1) int, list^(k+1) int)` for every k.
The second child input is a materialized compound; its size is unchanged
while the first decreases. The registry is checked, the initial source is
point and inhabited, and `accessible k` is closed.

`SpineOutputs` uses the same two-input recursion with a demanded associated
output. With `bind=false`, the recursive RHS is `list 'b`, and the terminal
RHS is its second input. There are no output-only binders. With `bind=true`,
the recursive clause requests `out = 'c` and the parent defines `out = 'c`;
'c is a real output-only binder linked to that clause's output equation.
Both versions demand `out` at source identity 0. `materialized_request`
proves the generated root request, and `binder_producer` proves the exact
binder/clause/equation linkage. Both have closed Acc theorems for every k.

These fragments describe the Lean declaration data; no parser or method
elaboration claim is made. The new examples prove inhabited initial states,
real request construction and accessibility. They do **not** construct an
actual compound installation or a complete successful dictionary execution.
The preceding Display fixture retains its separately proved real Step.

## 6. Remaining obligations

| Producer link | Proved in this change | Remaining for general Class P |
| --- | --- | --- |
| Dynamic captures | Names from actual query syntax; exact distinguished-origin producer | Simultaneous finite labels for arbitrary multi-position heads, including multi-name captures |
| Compound inputs | Actual nominal-root schema recipes, shared substitution, emitted endpoint equality and root recovery | Structural-root lower/upper containment and all new-ID readbacks over initial H |
| Refinements | Distinguished closed input survives all actual updates | Extract global genuine eliminations versus retained observations when relevant holes acquire structure |
| Outputs | Larger closed Acc class allows outputs and output-only binders; concrete checked examples | Construct general settled capture readbacks and binder-to-settlement-tree growth correspondence |
| Enumeration/Acc | Existing finite cover chain gives unconditional Acc for Spine | Discharge `ClassPProducer` for arbitrary recursive Class P |

No semantic gap or infinite counterexecution was established. No new owner
question, lazy restriction or implementation repair is proposed. The local
nominal materialization proofs already allow strict intervals at captured
leaves; structural-root interval facets remain a separate obligation.

The primary constructed these bounded proofs. The checkout lacks the skill's
registered prover configuration and no prover agent ran. A separate read-only
reviewer checked source/model quantifiers, representative sharing, canonical
functionality, actual emission ownership, historical guard production and
the exact limits of the example claims.

## 7. Validation

Commands from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalCaptureNames Yulang.GeneralNominalSpineAccessibility Yulang.GeneralNominalSpineExamples Yulang.GeneralNominalCompoundReadback Yulang.GeneralNominalReadbackFunctionality Yulang.GeneralNominalCompoundRecovery Yulang.GeneralNominalSpineOutputs Yulang.GeneralNominalCompoundEmission` | 0 |
| `lake build Yulang > /tmp/yulang-compound-inputs-build.log 2>&1` | 0 |
| `lake env lean Audit/GeneralNominalCompoundInputs.lean` | 0 |

The full build completed all 2179 jobs. The standalone audit lists only
`propext`, `Classical.choice` and `Quot.sound` (some declarations use fewer).
The earlier focused command
`lake build Yulang.GeneralNominalSpineOutputs Yulang.GeneralNominalCompoundEmission`
also exited 0; the eight-module command above validated the final code.
Development builds exposed ordinary elaboration errors, which were fixed;
no failed development build is counted as validation. One build was
accidentally invoked at the repository root and exited 1 for lack of a Lake
configuration there; all proof checks above used `lean/`.

From the repository root, `git diff --check` exited 0. A Python byte-prefix
check against `git show HEAD:<path>` verified that the only changed existing
files are `lean/Yulang.lean` and `notes/design/INDEX.md`, both append-only.
All eight new modules are imported. Prohibited proof-token scanning passed.
Frozen files and branch/head are unchanged (`astra/classp-producer-2`,
`47da90ca0483d773ec9f08efd95d4afb5c1aeb75`). No commits or ref updates were made.

