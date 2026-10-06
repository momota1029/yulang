# Exact captured-step formal: source position producer crosswalk

Date: 2026-10-06
Baseline: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`
Status: frozen, unreviewed research checkpoint; non-authoritative
Method: bounded source/implementation correspondence audit, no Oracle execution
Scope: P's original position inventory at the unannotated outer `f` root in
`my apply f = { my step x = f x; step }`
Implementation authority: none

## 1. Result and exact premise

The selected source contains one Function elimination of the outer formal,
no written annotation, and no second declaration/use of that formal. The
accepted source-call construction generates the initial original address
`p_0 = call.effect`. The existing HIR shadow slice independently retains the
same source binder, one local application, and its capture-use incidence;
its typed profile judgments remain explicitly pending. Production HIR and
collection do not provide a completed application/profile route for this
candidate. These observations are implementation correspondence, not a proof
that the complete original profile is singleton.

The remaining premise is exactly the left-to-right direction of:

```text
Applicable_original(C,d_f,R_f,p;xi)
  iff p = p_0 and ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c)).
```

The right-to-left initial incidence is accepted research evidence. The
left-to-right implication is unproved. A single original boundary
introduction accepts a signature profile parameter, which may describe
several positions. Counting source Calls, binders, boundary identifiers,
or currently implemented constructors does not determine that parameter.
No second source-applicable position, source-valid counterexample, or new
language choice is established here.

## 2. Fixed authority and dependency boundary

The governing sources are:

- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §§2–5: shared source component, stable `beta`/`Slots(beta)`, joint `nu,K,D`,
  provisional protected Handler treatment, ordinary-value formal refinement,
  annotation-dependent protection and the open formation judgment.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3,10: active whole-tuple relations, the supplied decorated envelope,
  emission inventory, certified whole generalization/use transport, and
  expressly open production/source coverage.
- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–4: sequential local binding, final `step` returns without invocation,
  local `f` resolves to the outer formal, retained capture, and exact-candidate
  scope. Broader local polymorphism and recursive groups remain undecided.
- [Accepted source-call construction](2026-10-06-source-call-generation-construction.md)
  §§3–5,7: one shared callee root, generated Call seed and interpreted
  existential constraint, with P/A retained as separate premises.
- [P source constructor](2026-10-06-profile-source-normal-form-construction.md)
  §§3–6: generated versus inherited provenance, least generated footprint,
  typed transport and the original applicability converse.

The existing typed-core §6 parameter-role table and typed-boundary §6
introduction/transport distinction are inspected supporting dependencies.
They retain admitted annotation/profile inputs; neither is promoted into a
raw-source formation theorem. Oracle behavior is neither input nor oracle for
this audit. Approved source meaning is taken from the integrated Authoritative
documents, without rereading or editing question bundles.

## 3. Source constructor correspondence derivation

Let the approved core be:

```text
lambda(f,
  bind(step,
    result(lambda(x, call(result(name f), result(name x)))),
    result(name step)))
```

The hypotheses are the exact selected tree, resolved lexical identities,
ordinary unannotated parameter interfaces `Value(A_f)` and `Value(A_x)`,
the accepted initial Call construction, and the supplied typed transport
interpretation whenever a packet is transported. The conclusion below is
only an inventory of reachable source routes and retained implementation
data. Full original applicability is deliberately not a hypothesis or a
conclusion.

1. The two headers each introduce one ordinary parameter. Only outer `f`
   owns the root under audit; local `x` is a separate argument root. This
   fixes source identity and interface category, not its nested signature
   positions.
2. `name f` resolves to that outer root and `name x` to the local root. Their
   `result` wrappers return the same values; they introduce no second source
   elimination. The local `call` is therefore the one reachable initial
   `ElimOrigin` producer at `R_f`.
3. The local Lambda retains `f` as a lexical capture, the Bind registers
   `step` sequentially, and the final Name returns that same local Function.
   None is an additional use of `f` as a callee. A later execution of `step`
   can activate the original body Call with an actual provider/argument;
   it does not add another original source Call occurrence.
4. Typed Name/capture/result maps may carry Generated and Inherited profile
   facts. A returned actual value and a separately supplied callee-result
   profile can retain latent entries. Those facts do not acquire a fresh
   source introduction merely by reaching a returned view, even when an
   inherited packet has the same static `beta` label.

This derivation is exhaustive over the displayed selected source tree. Its
extension to *all possible original profile introductions* requires the
missing source applicability rule. It cannot certify that extension by using
the tree's generated-footprint recipe as its own reference semantics.

## 4. Producer and transport inventory

“Reached” means reached by this exact component, not by an arbitrary provider
or ambient source supplied later. Code locators are baseline correspondence
evidence; they are not language authority.

| Route | Reached here? | Evidence and claim boundary |
| --- | --- | --- |
| Ordinary formal declaration / inferred contract introduction | Yes, outer `f`; local `x` has another root | Typed-core §6 assigns the unannotated Value interface. Inferred-view §2 requires a shared contract and complete inventory. This introduction can be parameterized by a multi-position profile; singleton completeness is not proved. |
| Actual `f x` Function elimination | Yes, exactly once | Accepted Call §4.2 generates `p_0` and `ElimOrigin`; P constructor §4 computes the least generated leaf. Shadow `Form::Apply` retains the occurrence but emits pending premises (`shadow.rs:1103`). This is an initial static producer, not full profile formation. |
| Pattern/formal annotation, including outer computation entry syntax | No | No annotation occurs in either selected header. Shadow retention records `PatternTypeAnnotation` and pending typed correspondence (`shadow.rs:139`); parameter annotation association is structural (`:526`). Ordinary production header admission requires a bare identifier (`module.rs:1471`). Absence fixes no annotation grant, not profile cardinality. |
| Expression `as` annotation or explicit result contract | No | Syntax tail owns a Type (`expression/tails/type_annotation.rs:23`); shadow retains its raw occurrence with pending correspondence. No such tail occurs at the Call, its operands, or returned `step`. A future provider/result annotation can supply an inherited packet and remains outside this source introduction count. |
| Expected callback context / normative callback literal B | No known expected context at these declarations | The selected outer/local ordinary function headers supply no callback-slot expected contract. B remains authoritative for actual callback literals. This route supplies no extra position here; the audit proves nothing about unrelated annotated/expected literals. |
| Additional resolved uses or recursive-component contributions at `d_f` | No second local use and no recursive source reference in the selected tree | Addendum fixes `f`, `x`, `step`; shadow resolves local initializer before publishing `step` (`shadow.rs:1265`). Relevant recursive components could contribute in larger programs, but the exact component provides none. Broader local recursion/polymorphism is expressly outside the addendum. |
| Name, lexical capture, binding alias and sequential rebind | Yes | Shadow capture-use incidence records one original `f` (`shadow.rs:1291`). P §3.3 gives identity/path transport. These are transport routes; typed capture attachment and receiver realization remain pending, and static provenance labels need not be globally disjoint. |
| Lambda body/result or final Name forwarding | Yes | Addendum fixes inert closure creation and final return. P §4 retains the one body leaf. Public closure paths do not expose private `f`; returning the closure does not invoke it. Shape substitution alone gives no fresh elimination. |
| Latent result position inherited from an actual provider/result contract | Possible later input; not a new node here | Typed-boundary §6 preserves both actual-result and matching callee-result evidence. `call.effect` does not project to `result.latent.effect`. Full inherited profiles remain allowed. Their source derivations and same-`beta` incidences are not constructed by this component. |
| Primitive/literal/operation/reify/designated eliminate/record/handler introduction | No such selected node | Source-contract §3.2 lists these independent constructors. Later providers/ambient contexts may contain them. They are outside this exact tree; no universal profile formation rule for them is claimed. |
| Generalization and use-time instantiation | Preservation obligation is relevant; exact local polymorphic mechanism is open | Inferred-view §2 preserves source relationship; source-contract §3.4 permits certified whole freshening/graft/hiding with joint evidence. P §§3–6 preserve source leaves under supplied transport. No approved rule lets ordinary generalization invent new original positions or separately quantify captured `A_f`. The full all-view preservation theorem remains open. |
| Role normalization / ordinary-value evidence | Yes in the accepted source constraint, pending in code | Accepted Call §4 and P §5.3 connect seed and `NonHandlerFormal` at the same root. This changes the internal formal/use record, keeps actual provider role separate, and creates no written annotation grant. Preservation of a complete original receiving profile still needs P. |
| Pending Function comparison, solved shape, empty outward effect support | Forbidden as independent producers | Inferred-view §2 forbids Q-created positions/path/receipt/authority. Internal handling or an empty outward row cannot erase a pre-dispatch applicable position. No implementation comparison success is used as formation evidence. |
| Option 2 production-only membership alternative | No selected grammar here | Source-contract §§3.7,10 leave an exhaustive production grammar open. Extra observations are not automatically extra source positions. This audit neither eliminates them nor turns source-only traces into Option 2 membership. |

## 5. Production and shadow entrypoint reachability

At the baseline, public `associate_operator_chains` (`yu-hir/src/lib.rs:114`)
associates chains while retaining CST. Association is not module-level typed
call-view production. Production `ResolvedExpr` (`module.rs:426`) has Lambda,
Integer, Name and Error variants. `lower_simple_chain` (`:1402`) admits an
associated atom with no children. The braced candidate has nested structure,
so its body cannot pass this atom route. `plain_binding_header` can register
the outer one-parameter header; lowering its body does not produce the
selected nested Lambda/Bind/Apply term. This is static code-path evidence,
not a newly executed acceptance test and not a reinterpretation of its
approved source meaning.

`ConstraintBatch::collect` (`yu-solver/src/lib.rs:815`) consumes that production
HIR. Its `emit_lambda` (`:1557`) accepts the parameter Name, integer or resolved
global Name body cases; other body forms return without a Lambda recipe.
`admit_lambda_fact` (`:10539`) builds the structural Function endpoints from
that recipe. Thus neither production path supplies the candidate's missing
original position inventory. `component_generalization_draft` (`:15162`)
reads a frozen definition's live root, while `instantiate_and_route_closed_inner`
(`:14527`) freshens quantified and recursive value coordinates in a supplied
closed scheme. These inspected paths have no reached typed profile formation
input for this candidate. Their existence is not evidence for preservation
of the later evidence-rich call-view relation. The internal generalizer's
entire implementation was not audited.

The default-off shadow path has a different explicit envelope:
`ShadowArtifact::from_parsed` retains the complete chosen parse snapshot;
`project_selected_nested` (`yu-hir/src/shadow.rs:1128`) recognizes the exact
approved candidate and constructs its structural Lambda/Bind/Lambda/Apply/Use
arena. Its annotated-header branch rejects the selected nested slice
(`:580`), its capture correspondence is pending, and the Call has five pending
premises after the formal-use stub is added. `yu-core/src/shadow.rs` only
reexports HIR data. None of these data structures claims `beta` or a typed
profile. The independently implemented structural linkage corroborates
source identity/occurrence accounting; it cannot supply a missing semantics
rule by omitting a field.

## 6. Independence, omissions and failure conditions

No executable semantic checker, differential oracle, seeds, random ranges,
mutation run, build or test was used. The finite coverage domain is the one
exact selected source tree plus the bounded entrypoint paths above. Code and
research notes share the approved source interpretation and may share the
same source-footprint assumptions. Their agreement is correspondence at that
scope, not independent validation of those assumptions.

The conclusion fails as singleton completeness evidence if an original
formal/signature introduction independently supplies another applicable
position. That precise case is unexcluded. It also requires revalidation if
the exact source meaning or stable dependencies change. Provider/ambient
graphs, arbitrary annotated sources, general recursive components, full local
polymorphism, adapters, state/import interfaces, production Option 2 grammar,
initial admission A, runtime receipt/liveness and all-view principality were
not audited or established. An extra inherited latent entry is not by itself
a falsifier of the generated-footprint result.

Recommended next action: construct and independently review the original
formal/signature applicability judgment at `d_f,R_f`, proving or refuting
the stated converse from source introduction premises. This audit supplies
no basis for another transition checker assuming that same converse, and
no basis for production implementation or a user semantic question.

## 7. Commands, resources and frozen dependency packet

Checks performed: bounded `rg`/`sed`/`cat` inspection, `git rev-parse HEAD`,
`git status --short`, scoped `git diff --name-only <baseline> -- <dependencies>`,
dependency `sha256sum`, and
`git diff --no-index --check /dev/null <leased path>` (passed).
Initial inspection dependencies matched the pinned baseline. At final freeze,
concurrent changes appeared in `yu-hir/src/lib.rs` and `shadow.rs`; narrow diff
inspection showed a read-only source-input accessor and test-module wiring,
without a new profile formation judgment. Baseline code locators above were
rechecked with `git show <baseline>:<path>`. The note remains a baseline audit;
these concurrent changes are not claimed reviewed by this producer. No Git
mutation, Oracle command, build/test, child process wave or whole formatting
was performed. Reads used short serial shells; no heavyweight process ran.
Peak RAM, cumulative CPU and total authoring wall time were not instrumented.
The broad solver search was bounded with `head`; it is not an exhaustive
audit of all solver internals. One exploratory search named a nonexistent
`pattern.rs`; the actual `pattern/mod.rs` was subsequently located/read.

Direct baseline dependency SHA-256 values:

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
74604c54f23efc406d5359cd4e2dfcc946065d8b01071874ea8c0945116fce05  notes/progress/2026-10-06-profile-source-normal-form-construction.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
b98eada12b21796a380b5347ba600a8bd66e89b3284c3c2dd1ef255935c1f720  crates/yu-hir/src/lib.rs
ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5  crates/yu-hir/src/module.rs
96e4c982bb9a55e3f2f90e942f34b26a684e48bda3b68e62569fcd944d39550c  crates/yu-hir/src/shadow.rs
58a0bdfdfb0afe0e195e5ce3542932c6b84ea129ce51a683febdb54a3508cb8c  crates/yu-solver/src/lib.rs
d5379317c5ff286a6a5a9c20cdac94efd71b67ada79bff85f9b4caa5cf54b68d  crates/yu-core/src/lib.rs
30e112fda9e208cfbbc07ab8648f5cb2f254f24a8af25674bdde5fd15a04c9d3  crates/yu-core/src/shadow.rs
edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a  crates/yu-syntax/src/expression/tails/type_annotation.rs
f61a4928f9982e9885ba726213f1f6a6cef4feb89ebae38c98f629a9bafc4f03  crates/yu-syntax/src/pattern/mod.rs
```

Commit packet:

- Exact lease/change: `notes/progress/2026-10-06-profile-position-producer-crosswalk.md` only.
- Baseline: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`.
- Changed dependency hashes at final check:
  `crates/yu-hir/src/lib.rs` → `9abefdfa0530edbd671f70d9fb28770a168dd4a226da419683147bab384edae1`;
  `crates/yu-hir/src/shadow.rs` → `4b20ad7164a0ebf17f6ac8b1a29261f181f0b16fd389b6e2b4ce17508c68fac8`.
  Other listed dependencies remained unchanged. Recheck the live delta before
  integration if the primary uses a later snapshot.
- Review status: unreviewed, frozen, non-authoritative research correspondence.
- Checks: narrow inspection/dependency checks and whitespace check; no semantic execution.
- Proposed commit: `research: audit exact formal profile position producer routes`.
- Shared deltas left for primary/curator: link this correspondence evidence if
  useful; retain P open at original applicability converse; make no theorem,
  production or authority promotion. No shared file was edited.
