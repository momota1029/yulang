# Proposal: acquire a declared callback interface at its source use

Status: Draft — representational proposal; no semantic or implementation approval
Date: 2026-11-02
Scope: R226, the known declared ordinary Value-formal path selected by callback delivery B
Approved-by: none for this proposal
Reviewed-by: pending independent review
Supersedes: none

## 1. Concrete result and boundary

Current source data can identify a known callee declaration, its original
annotated Function-valued formal, and an exact source use. Current native
construction also retains that formal's negative Function term and one
correlated per-use reconstruction. Compose those existing owners by their
actual identities, retaining declaration coordinates when annotations are
constructed. Then request the original source Function/profile formation at
that coordinate and deliver its result to B before literal-body generation.

This is a proposed composition, not an existing end-to-end constructor. The
first missing semantic equation is source annotation/declaration formation of
the complete role-indexed Function contract and original callback profile.
A second missing equation factors symbolic use instantiation early enough for
B while preserving the existing scheme/generalization substitution. Raw native
Function terms and source permission paths do not establish either equation.

Authorities remain callback delivery §§2–3, especially normative B in §2.1,
and joint compatibility boundary §8 and its candidate source-owner section.
They select Handler introduction from the known callback boundary, independent
syntax-directed parameter entry, synthesis of the literal's own interface,
and final `F_lit <: F_cb`. They do not select a compiler API or complete
annotation-to-interface/profile interpretation. This proposal changes no source
rule and discharges no original App premise. Parent delta remains **0**.

The mathematical source constructor takes original declaration/annotation and
source-use identities, and uses one abstract substitution. It does not take a
Rust graph or route as a semantic premise. The native path below identifies
existing representations and later correspondence obligations; E2 and the
native commutation part of E3 do not become prerequisites for proving the
abstract source construction correct.

## 2. Start at the declaration, not at a supplied interface

Use the real annotated-formal fixture
`my ident x = x; my apply (f:int -> int) = f 1; my answer = apply ident`
as the acquisition trace. Its source occurs in
`crates/yu-solver/tests/candidate_annotated_function_formals.rs:93`.
It supplies an existing callback value, so it is not evidence for literal
contextual introduction. For the B walkthrough, replace only the final
argument with the source literal `apply (\x -> x)`. That variant is an
unexecuted worked source shape, not an assertion of current acceptance.

The source-owned path is concrete:

1. The callee's `LocalSourceForm::Name` resolves to the exact module definition
   `apply`; `DefinitionUseId` retains the collection artifact and this Name
   occurrence. `DefinitionUse` retains target, receiving owner, use level and
   use-value component. The target is not selected by a solved Function shape.
2. The provider's `LocalSourceNamedGroup.formals[0]` identifies its first Lambda
   and `HirParameterId`. The Lambda's `LocalSourceParameter.annotation` contains
   the actual `SourceAnnotation` for `f:int -> int`, including owner and source
   position; its value constructor is `Function { argument, result }`.
3. Match that exact owner/parameter to `FormalRegistrationInput.recipe_position`.
   Declaration annotation construction publishes
   `formal_domains[recipe_position] = N_f^-`. `admit_lambda_fact` uses that
   same term as the callee Lambda's argument child. This term denotes a native
   constraint descriptor; do not rename it a complete source `F_cb` yet.
4. `Graph.negative_formal_roots[N_f^-] = j`, when retained, locates the captured
   negative Function node. One exact module `FreshRoute` provides its use ID,
   provider, graph, rows and `retained.terms`. Its projection
   `N_f,u^- = route.retained.terms[j]` uses the route's existing common mapping.
   Missing roots or mismatched ownership stop acquisition; they do not license
   selecting another Function node with the same printed shape.

For this one-formal declared Function path, the domain term is a structural
child of the provider Lambda constructed in step 3. Capture recursively visits
Function children and indexes encountered declared negative roots. This
explains the intended retention path. A totality and ownership theorem for
that composition, including canonicalization and refusal cases, remains E2
below; no source program was run to assert it here.

The proposed declaration coordinates are read-only locators into those same
objects: provider root, named group/formal index, parameter ID, annotation
position and structural path. They identify the original formal; they do not
define a new semantic boundary. Preserve omitted effect-port coordinates as
well as written rows. Do not infer permissions or a slot profile by inspecting
the solved effect support.

## 3. Use one symbolic instantiation

Native `candidate_formal_annotation` constructs both polar Function views.
Named source variables share rows by `(AnnotationScope, spelling)`, holes use
their source positions, and omitted effect ports remain fresh symbolic rows.
The source coordinate-to-row association is known during that construction.
Retaining it as a byproduct is the proposed bridge; its storage/API is not
selected here.

For a source-use substitution `rho_u`, require every declared coordinate to
refer to the image of its actual declaration row in the **same** use mapping.
Existing `prepare_candidate_fresh_use` illustrates the relevant discipline:
canonical source representatives share one image; eligible generic local rows
are freshened, non-generic/outer rows are retained; all Function nodes are
rebuilt using that common row vector. Scope, context and evidence remaps travel
with it. A second annotation re-elaboration with an independent fresh map would
not satisfy this proposal.

The existing executable module route is produced from a captured provider
graph. It is therefore a correspondence target, not an input that initial
callback checking may wait to obtain after solving the consumer body. Proposed
early declaration instantiation must factor the declaration-owned symbolic
coordinates from that route and preserve its actual generalization conditions.
E3 requires the commuting equation

```text
early source-use coordinate image = later ordinary route image
```

under one use identity and the same substitution; this is unproved. The proposal
does not call the current completed route early, copy its eventual solved
answer, or independently freshen all annotation variables. The latter would
wrongly freshen non-generic variables and lose correlations with other formals,
results or captured bindings.

For `f:'a -> 'a`, both occurrences of `'a` must use one symbolic `alpha_u`.
Other callee formal/result occurrences of that source binder use the same
image. Literal endpoints are fresh and synthesized independently. Argument and
body uses constrain them through the ordinary solver; no rule sets them equal
to `alpha_u` merely because it is expected. No final type is required to start
ordinary inference. Unknown-callee acquisition remains unresolved here and
cannot become a rejection or mandatory-annotation rule.

## 4. Form the original profile, then deliver B

The original callback declaration occurrence and structural slot locate the
static template. They are not themselves `beta`, and a list of written effect
families is not `Slots(beta)`. The source formation owner must construct the
original template/profile together with the complete role-indexed formal
interface from these declaration inputs (E1/E4). It must account for written,
symbolic and omitted ports, all original dependencies and allowed typed paths.
`FormalPermission` retains useful concrete source permission coordinates, but
its own contract excludes arrival/provider/consumer evidence and it does not
enumerate the complete profile. Runtime activation `b` is not minted here.

Once the source formation/instantiation parts of E1, E3 and E4 are constructed,
the candidate source-checking sequence is:

```text
resolve the callee declaration and exact formal source coordinate
instantiate that coordinate with the one symbolic source-use mapping
form its original (F_cb,u, beta_u, Slots(beta_u))
check the argument literal with that expected boundary
  select Handler receiver role before any body constraint
  determine the literal parameter's Value/Computation entry from its own syntax
  synthesize parameter/body/result and the complete F_lit
  submit one completed-interface F_lit <: F_cb,u query
construct the original whole-argument/App obligations at this same use
```

The boundary/profile is transported from the original template with its typed
dependencies, not reconstructed after solving rows. This sequence is a
candidate source operation expressing selected B; its preservation of the
original source judgment and generated rules is E5. It is not a replacement
implementation of `sourceRules`. Current Rust `Work::Visit(App)` has only
index/level/region; App Finish follows the argument's complete body traversal.
Current `sourceRules` likewise recurses on the argument with the same Context.
Both lack the required explicit acquisition/delivery construction.

An explicitly Function-annotated argument retains its own descriptor. The
relationship with an expected callback descriptor is an unresolved overlap
rule. This proposal does not merge them or select their introduction order.
Computation-retained callback formals and unknown callees remain separate open
cases; they do not prevent describing the selected ordinary known-formal path.

## 5. Worked unchanged App consumers

For original `app s callee argument`, the generated scope is
`exists viewLogic(s). app(...)`, with the original child rules, five atoms and
two checks (`OriginalSourceGeneration.lean:111–123`). The proposed expected
callback `F_cb,u` is the callee's **formal**, not the whole App descriptor.
The latter must still be formed from the original complete call demand and
the independently synthesized argument/result, with joint effect equations.
In particular, do not set `descriptor(s) = F_cb,u`.

| Original premise/consumer | Proposed contribution and remaining equation |
|---|---|
| `descriptorFormation` | Declaration acquisition identifies the correct callee formal. Form the entire original App Function descriptor from the original inert whole argument and result obligations; connect its formal to this source use (E6). Neither native four-child shape nor B supplies descriptor formation. |
| `wholeArgumentCompatibility` | The argument is its inert whole carrier `D_arg`; for a literal it eventually returns the newly formed closure. B's `F_lit <: F_cb,u` contributes the returned-value boundary. Complete carrier formation/admission, including divergence and pending observations, remains E7. |
| `completeCallCertificate` | Apply the same callee/provider to this same admitted whole carrier at its genuine receipt and current world. Acceptance, complete invocation and observations remain E8; no early checking receipt is a runtime certificate. |
| `sourceCallIncidence` | The original source owner is `(s, context, callee.site, argument.site)`. Existing `localCallOwner` reads those operands. E6 must join the acquired declaration/use to that exact owner without replacing its callable subject. |
| `callableImage` | Establish the original complete invocation image under the original shared assignment/event and the same admitted provider/carrier. Return and pending/body observations remain E8. |
| Value check `callee.returnedValue -> s.descriptor` | Prove the ordinary whole Function check for the same returned callee and formed App descriptor (E9). Derive or place B's one final literal/formal query in that original derivation; do not assume the whole check from it. |
| Computation check `s.callableImage -> s.synthesis` | Preserve the original complete result/interface projection (E9), including effect/readout obligations. |

`generated_application_checking` obtains its value check from **supplied
satisfaction**. It does not construct that satisfaction or any acquisition
law. `PortReadout.application` selects the returned callee as the subject; it
does not select the declared callback formal. Those existing theorems remain
useful consumers after E1–E9, with their premises unchanged.

All contributions share the original source scope, assignment, provider,
receipt/world, correlated `nu,K,D`, and joint witness. Value-entry execution
remains `receipt; Force(D_arg) >>= B_receiver`, with both argument-force and
body observations. The callback literal's own Value-entry invocation similarly
keeps its receipt/force/rebind/body sequence. Retained Computation entry binds
its carrier and runs it only at actual body consumers. These are independent
from Handler/Pure introduction. No separate concrete successes are composed,
and no independent port inequalities replace joint Function compatibility.

## 6. Exact remaining equation owners

| ID | Unproved equation | First owner |
|---|---|---|
| E1 | Original declaration/annotation constructs the original complete formal Function interface. | Source declaration/annotation formation. |
| E2 | Native polar construction represents E1's formal; its exact term is retained in the provider graph and projected by the exact use, preserving source identity through canonicalization. | Formal annotation constructor, Lambda constructor, graph capture and source/native correspondence. |
| E3 | Early symbolic declaration instantiation agrees with ordinary generalization/FreshUse under one use substitution, with non-generic sharing. | Source-use instantiation and generalization. |
| E4 | Original declaration/slot constructs `beta, Slots(beta)` and transports them through that same use; raw coordinates/permissions are not a substitute. | Source Function/profile formation. |
| E5 | Expected boundary reaches literal role selection before body constraints; the resulting B computation preserves original source rules/judgments. | Source App checking and Lambda introduction. |
| E6 | Entire App descriptor uses that exact formal/use and original incidence under the same assignment. | Original App descriptor formation. |
| E7 | Whole argument compatibility follows for the original inert carrier with complete admission/observations. | Whole-carrier formation and boundary checking. |
| E8 | Complete Call certificate and callable image describe the same actual invocation, with effects and observations. | Original Call semantics and source interpretation. |
| E9 | Full callee-to-descriptor and image-to-synthesis checks follow, with B's query connected to that same derivation. | Original source checking/readout adequacy. |

These are proof obligations, not assumed `LocalLaws`, new Kernel predicates or
constructor arguments that stand in for the conclusion. No equation is closed
by this document. Representation choices include retaining constructor-known
coordinates and exposing a read-only use projection; the proposal does not
select storage, APIs, phase changes or implementation. A genuine semantic
choice is needed only if original formation cannot determine the original
profile, or broader overlap/unknown-callee rules must change. Return that exact
alternative to the primary before extending this bounded design.
