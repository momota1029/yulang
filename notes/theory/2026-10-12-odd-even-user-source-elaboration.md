# Exact nested odd/even source: primitive formation boundary

Date: 2026-10-12
Status: frozen and independently reviewed research; scoped source inventory and minimized
construction obstruction; original source typing and source-to-core bridge OPEN
Assigned baseline: `d55c4db850e74ba4cc0926402de5d399f610540e`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; proof leaf, no delegation

## 1. Frozen source, claim and exclusions

Keep the user's exact nested source, as recorded in `tasks/current.md`:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

The packet's semicolon notation names the separation between the inner
declaration and the final outer expression. It does not move `even(n - 1)`
outside `odd`, insert another wrapper definition, or add a final source `odd`
expression. Alpha labels below identify distinct binders without changing
the two original spellings `n`.

The required source conclusion is a finite derivation of this actual source
definition in the selected independent source judgment:

```text
rho; T |- S_user @ a_O : R_O ! C_O [d_O]
```

Here `T` is the original binder/event tree, `a_O` is the inert source closure
with its actual capture environment, and `R_O,C_O` retain the complete source
interface and jointly scoped obligations. `rho` must interpret the actual
resolved primitive/declaration environment. It is not a freely chosen
arithmetic library used to make this example typable. No particular final
scheme, Bool result, successful guard, or pure effect is assumed.

The second required conclusion is a constructor-directed image of that
same derivation into a finite native Simple-sub Let/Lam/Var/App construction,
with a scoped correspondence for every retained original source alternative,
provider/world/effect field and both source Calls. The native image must
retain the original source roots, formal binding identities and publication
cuts; its obligations cannot be satisfied by independently chosen marginal
witnesses. For every lawful finite original use/history admitted by the
source derivation, the correspondence must preserve its complete indexed
Call and branch meaning. Finiteness of the construction does not bound
those original future histories.

This is an attempted subsidiary construction, not an asserted universal
elaboration theorem. The parent theorem still quantifies over its original
supported source programs and lawful histories and requires soundness,
required principality, normal inference, complete Call and effect hygiene.
No source domain, binder, alternative or parent obligation is narrowed.

**Claim class of this result:** bounded static characterization and minimized
missing premise. The displayed source typing is the required conclusion,
not an established theorem or a conditional premise assumed to obtain it.
No complete native image, source acceptance/refusal, source counterexample,
intrusion soundness/principality theorem or production authority is claimed.
No compiler edits, tests, builds, probes or Oracle execution are authorized.

Falsifier for the reported obstruction: an in-scope selected source rule and
actual complete resolved declaration/application that supplies the missing
condition constructor below. A scalar builtin signature or a source-interface
slot alone does not meet that falsifier.

## 2. Governing sources and owning judgments

The design index is a locator; the following source clauses govern:

| Source | Exact governing sections and responsibility |
| --- | --- |
| Top-level inference principles | §§1–5 and Authority and integration: native generation/accumulation/propagation and no speculative choice of typings |
| Source Generalize definition | §§2–3: selects the independent source rules and preserves their genuine local premises |
| Source Generalize construction/proof | §2 L1–L5; §3.1 Parameter, Literal/authentic primitive, Lambda, Call, Branch and Recursive introduction; §§3.2–3.3: actual checking choices and original source/event binders |
| Source contracts/common allowances | §§3.1–3.4, 3.7 and 6.1: complete clause inventory, lawful alternatives, worlds and branch allowances |
| Complete source-interface definition | §§2–4: IF-Insert/IF-Use require independently typed complete declarations |
| Complete source-interface construction | §§2, 5–6: actual source/operand/Call formation is an input; finite registered cycles give static placement |
| Call-input construction | §§3.2–3.4: Entry-Value, Data-Lambda, Code-Bind and Code-Call retain original ports and complete invocation |
| Original registry adoption | §§1–2: bounded nonrecursive formal/Name/Int pre-Call scope and unprovided original complete declaration applications |
| Source-owned original registry construction | §2 and §§3.1–3.2: actual Int and additional primitive contracts remain semantic/local formation inputs |
| Adopted invoke pre-Call construction | Claim and assumptions; Exact remaining source and Call premise: actual complete declaration-graph correspondence remains OPEN |
| Parent-copy SCC decision | Apply-result source-fragment ownership; Nested Apply membership; Definition-root Value ownership; Retained boundary |
| Value/type association | Approved extrusion-event qualification; Definition-root origin for nested call-demand extrusion |
| Copied-row ownership | Decision: descriptions/bounds copy without inheriting or retargeting Value-reference incidence |
| Local self-recursive binding | Selected source behavior and Proposed source-to-solver seam: active enclosing root remains monomorphic; publication is sequential |

The decisive source rule is the Literal/authentic primitive row of Source
Generalize construction §3.1, under L1. It requires an actual declaration and
whole independently typed local relation, with its ordered operand telescope,
guards, original effects, provider/future/admission laws and every licensed
alternative. Branch's corresponding row requires its original test/selection
and ordered branches/guards and continuation semantics. These requirements
are not supplied by spelling an operator or naming an interface.

Theorem IF §6 supplies placements from these inputs. In §5 Call first
constructs both child frames and consumes their actual Application origins;
it does not manufacture a child's primitive law. Generalize retains active
clauses that owning rules emitted; it does not derive an unprovided L1/L2
instance. The bounded registry adoption selects a representation, without
identifying unprovided original declarations with it.

## 3. Original scopes and the complete source inventory

Write O for the outer `odd` definition root, E for the nested `even` root,
a for outer `n`, and b for inner `n`. These are source binding identities,
distinct from solver variables, Apply results and copied descriptions.

| Source fragment | Fixed binding/scope and required constructor |
| --- | --- |
| Outer `my odd n = ...` | O active monomorphically during its initializer; outer Lambda introduces a |
| Inner `my even n = ...` | E's own initializer under O; inner Lambda introduces b, shadowing a; E has the selected temporary local self identity |
| Condition `n <= 0` | The Name resolves to b; one comparison occurrence and one literal-0 occurrence; actual overloaded operator resolution/formation required |
| True arm `{ true }` | Original arm Block and its `true` occurrence; its actual Boolean/value declaration and Return must be formed |
| Else arm `odd(n - 1)` | Callee resolves to O; Name inside this subtraction resolves to b; own literal-1 and subtraction occurrence; complete inner Call |
| Final `even(n - 1)` | Callee resolves to published E; subtraction Name resolves to a; a second, distinct literal-1 and subtraction occurrence; complete outer Call |
| Inner publication then outer completion | E's initializer precedes its installation/use; O stays monomorphic until its own completion/publication |

The two literal-1 occurrences can reference the same primitive declaration;
they retain different source occurrences and local applications. Likewise,
the two subtraction occurrences share a spelling without sharing a chosen
overload witness or an invocation event. Each must retain its own actual
method/alternative and the dependencies imposed by the original declarations.

The approved definition ownership directly gives O → E and E → O under
these fixed Name resolutions. Inner initializer Names belong to E. Hence
the original roots share a nontrivial Value-reference SCC across lexical
levels. This is a selected source-law instance, without evidence of current
compiler emission of that graph. Publication does not identify roots with
the Lambda, Block or Call-result rows.

For an actual inner call-demand extrusion, the approved origin is E and the
receiver is O even under this If wrapper. This fixes endpoints only. No event
or parent/copy pair exists merely from this root cycle. Apply's nested
membership rule does not independently define the operator/If fragment
boundary; no full primitive/branch adjacency catalogue is inferred.

Keep the intended native reference cuts: outer initializer/formal at level
1, inner initializer/formal at level 2, E publication at boundary 1 and its
subsequent use at level 1, then O publication at boundary 0. These are the
Let/Lambda schedule derived in the nearby native notes. They are targets of
the missing source correspondence, not observed exact-Yulang scheduling.
Original Source Generalize publication scopes/event telescopes also remain
distinct from scalar levels and from the Value SCC. An added wrapper would
change the native schedule and is excluded.

## 4. First missing primitive constructor and independent remaining debts

Freeze before deriving the condition's independently typed primitive frame.
Given the fixed inner formal context, the first operation-specific missing
judgment in this outer-to-inner construction is:

```text
rho; T_E |- (n <= 0)_actual_occurrence @ a_test
  : R_test ! C_test [d_test]
```

`T_E` retains b's original typing scope and the original invocation/event
binders. Its supplier is the actual resolved `<=` declaration and its genuine
original local constructor, not the checking result of the If expression.
Before IF-Insert/IF-Use can place that constructor, its complete ordered
declaration application must exist. In the notation already used by the
adopted pre-Call audit, the missing application has the form
`Gamma_available |- mu_le : Delta_in(delta_le)`, then the original
`Fam_delta_le[mu_le]`. Here delta_le and Delta_in denote the required actual
declaration and its full telescope; no concrete declaration, new predicate or
introduction signature is being defined by those labels.

The pinned governing source cone supplies no actual resolved comparison
declaration, complete telescope/substitution or original local law for this
occurrence. An overloaded `<=` requires the actual registered alternatives
and their ordinary source/checking selection mechanism. Inferring a desired
Bool branch result and then choosing an Int comparison would assume the
missing derivation. The source has no parameter annotation that licenses
such a choice here.

A later bounded owner audit followed the semantic-import/declaration path
beyond this governing cone. The architecture phase map places semantic
resolution in Resolve/Lower over parsed source plus a semantic imported
interface, while the syntax operator table/compiler record and select only
spelling, fixity, binding power and source provenance. In the inspected
current path, `SemanticImports` has no supplied content and module lowering
does not consume an imported semantic declaration. No authentic selected
`<=` declaration or application was found in these owners. This remains a
bounded missing-evidence result: it does not prove repository-wide or legacy
nonexistence, show that the intended source is untypable, or establish that
an approved language decision is missing. Generalize construction still
requires the real declaration; whether one is supplied by another original
environment must be resolved at that source owner before considering a new
semantic decision.

This is the first **operation-specific** cut with the Name/formal context
held fixed. It is not a claim that every upstream original entry-port or
joint-world registration has been constructed: the bounded invoke note
already leaves their complete original applications OPEN. No arbitrary
left-to-right evaluation order for an unprovided operator is asserted.

Each following debt is independent and remains at its owner:

| Debt / actual owning declaration or rule | What selected generic rules provide | What remains unsupplied for this source |
| --- | --- | --- |
| Comparison declaration for `<=` at the condition | L1 and Literal/authentic primitive describe required whole contracts; IF inserts/uses an actual such contract | Resolved overload catalogue, full dependent declaration application, actual local checking/selection and lawful semantic actions |
| Int primitive declarations at `0`, inner `1`, outer `1` | Adopted formal/Name/Int APIs construct schemas under a complete actual declaration graph; native Scala Lit has Int | Actual original Int/Return/Prefix applications, scopes, provider/world/guard/alternative maps for these three occurrences; the payload tokens supply no membership proof |
| Value/Boolean declaration resolved by `true` and arm Block/Return | Generic Name preserves its actual resolved registration and provider; Result preserves original Return | Actual Boolean/value registration, resolution and complete local contract; original arm block/return formation; no special Name law is inferred from the spelling |
| Subtraction declarations for the two `-` occurrences | General checking §3.2 retains each actual registered method/adapter and its complete evidence | Full overload declarations, operand/result/effect/provider/world relations and lawful applications at b/inner scope and a/outer scope |
| Original If/Branch constructor | General source §3.1 retains test/selection, ordered branch guards and continuation; allowance §6.1 covers test and both arms if Branch is independently supplied | Actual condition interpretation, selection/guards, branch result and complete effect/continuation relation; an allowance inclusion is not this typing/selection law |
| Both Application/complete Call records | Code-Call and IF retain complete callee, inert whole argument, checking origins, actual receiver/entry, result and future interfaces | Authentic arithmetic child proofs and original Application/Gen-Call origins with whole-argument/checking relations; no scalar port is substituted for them |

The generic Parameter rule does close the **rule-selection** issue for the
two unannotated formals: each receives an ordinary flexible Value endpoint
at its own source type scope. Name resolution fixes b versus a and O versus
published E; the selected root rules close the conditional O/E incidence
calculation. None of these generic laws closes a primitive/Branch registration
or its semantic local law. IF closes static placement once those complete
inputs exist. It does not close any absent primitive declaration by itself.

Consequently neither d_test, the complete d_O, nor a faithful finite native
image has been constructed. The obstruction is an absent independently
grounded constructor application, not a proof that its semantic fiber is
empty. It establishes no source type error, refutation or source restriction.

## 5. Native-core, syntax and Oracle boundaries

The imported stock core note explicitly removes condition, arithmetic and
literals. Its closed term ends in a separate `in odd` and has the subsidiary
principal interface `Top -> Bot`. Those source differences prevent using it
as the requested image or carrying that interface to the user's definition.

The actual reference syntax has Lit in addition to Let/Lam/Var/App. Its
Typer.scala:23–33 registers `true:bool`, `false:bool`, `not`, `succ`, `add` and
a polymorphic curried `if`. It supplies neither `<=` nor subtraction nor an
original Yulang world/effect/branch law. Replacing the If by applications of
that builtin would require a genuine scoped lowering/semantics theorem,
including branch suspension/selection and complete invocation. A Function
type for `if` proves none of those facts. Likewise using constant Vars for
`0` and `1` or Church encodings requires actual source registrations and
their correspondence; none is introduced here. There is no impossibility
claim about finite encodings.

If an actual arithmetic argument proof eventually yields type T_inner, the
native inner App would demand `o <: Function(T_inner,R_inner)`. The pure
core's demand `o <: Function(B,R)` instead applies directly to its formal.
No present proof equates T_inner with b's formal endpoint B, and no pure-core
parent/copy pair is relabeled as an emitted exact-source pair.

Separately, syntax-v0's authoritative If page §§1–3 requires `:` before its
first arm body and explicitly does not define branch typing/effects. The
exact `{ true }` arm spelling is therefore not recovery-free If syntax in
that parser. Dynamic operator-chain §2 requires the exact syntax environment
to admit each operator role. These surface limitations are distinct from the
intended mathematical source judgment and cannot refute it.

Implementation inspection only confirms current owners: LocalSourceForm in
`crates/yu-hir/src/module/local_source.rs:107–137` has no If/Branch/Boolean
form; its chain tail match at 520–538 does not admit infix uses. Name formation
at 636–657 reads lexical/module bindings without a special `true` declaration.
The carrier body accessor at 250–253 requires an inline OperatorChain.
`crates/yu-solver/src/candidate_source.rs:254–305` assigns supported root/local
levels without supplying a missing primitive or branch constructor.

The nearby pending-call source note concerns a different Call-only module
and rejects its separate final Name at CandidateInference::solve before
collection. Its admission result is not imported for this source. Its actual
consumer at `shadow_apply.rs:79–113` cannot bypass missing source formation.
No current candidate execution or source-to-core image is implied here.

No frozen Oracle source was used to decide successor primitive semantics.
No Oracle acceptance/type/run was observed. The Scala reference is evidence
of its own stock native constructors, with separate baseline and authority.

## 6. Economy audit, checks and handoff

Earlier exact-source native and SCC/generalization attempts retained the
same arithmetic/test/branch premise. This pass follows its owning source
rule rather than supplying another scalar reconstruction. Complete source
formation and ordinary inference for this example are required A/B work.
Retaining the original resolved declaration, whole substitution, alternative
and source incidence at the primitive/Branch owner can address D when those
facts are actually known. A certificate does not establish an unknown local
law, so adding another reconstruction relation cannot close this cut.
The parent gate remains OPEN without changing its classification or domain.

One next action: the primary should locate the authentic `<=` declaration
supplier and selection authority outside the inspected current pipeline, if
one exists, and obtain its complete application at this fixed occurrence,
including the original Int and test/selection interfaces it uses. A bounded
follow-up can then apply existing placement rules to that exact supplied
declaration. Missing evidence alone does not establish an underspecified
semantic decision; use the existing approval path only if the owning authority
confirms a concrete choice is genuinely unselected and required. This note
chooses none.

One static constructive pass within the assigned 45-minute ceiling. Read-only
`rg`, `cat`, `sed`, Git ref/status/object reads and SHA-256 comparisons; one
leased Markdown write. Commands with speculative nonexistent `spec/` and
`collect/candidate_*` paths produced no evidence and were replaced by actual
owner locators. Truncated combined reads were narrowed at decisive sections.
No builds/tests/probes, Oracle/Scala execution, benchmarks, Git mutations,
other writes, delegation or external/user contact. At most one local shell
process per read tool call; no heavyweight process or measurement samples.
Exact CPU/RAM and reasoning elapsed time were not measured. The primary
retains verification, adjudication, shared records and integration.

Requested role/settings: normal prover/Sol-high route; exact launch metadata
is retained by the primary. Configured `prover` has no model/effort pins and
defaults are `gpt-6.1-sol`/high. Observed runtime model/effort: unknown. No
Astra override, hot reload or effective-setting claim is made.

Dependency hashes and baseline equality checks follow. No dependency edits
were made by this leaf. Broader declarations outside the inspected governing
cone, executable exact-source admission, primitive law validity, full original
entry/joint-world registration, native correspondence, actual occurrence and
pair generation, replay, publication, soundness/principality, complete Call,
effects and production/cutover remain unverified.

Independent review: `compiler_referee` PASS, no blocking, major or minor
findings, for the bounded source/judgment, owner-attribution, syntax-boundary
and non-claim scope. The later independent `spec_auditor` review of the owner
audit initially found an overstatement risk; the bounded-evidence wording above
closed that major finding in delta review. The owner audit did not certify new
dependency hashes or broader/legacy primitive declarations, and it leaves all
parent gates OPEN.

## Dependency snapshot

27 direct repository dependencies byte-match the assigned baseline; two Scala
reference files byte-match their separate reference baseline. Shared task/index
records were read as locators/context, not used to supply primitive authority.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` | `2d6439507f01f38234909f98d86b1d2fbe31d3c7dd60d453cf1c199604020451` |
| `notes/theory/2026-10-10-source-owned-original-registry-construction.md` | `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb` |
| `notes/theory/2026-10-11-adopted-invoke-precall-construction.md` | `897a7bc108349d9ba8eec905f4490e564f54c71d8df11d7b72ad25016452d6ee` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `notes/theory/2026-10-12-cross-level-recursive-scc-core-proof.md` | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| `notes/theory/2026-10-12-cross-level-pending-call-source-construction.md` | `b6c6d7200f23ce5174d349ec43450d76dcc8859c550ae0a80bf9844b30712fe6` |
| `notes/theory/2026-10-12-cross-level-odd-even-inference-derivation.md` | `839e80f5c1426531bb761d9ae6ef9475d8f89104e766a5973c356656f89ae41c` |
| `notes/theory/2026-10-12-cross-level-scc-generalization-proof.md` | `e77f64652b9fbdf7a503542cb0ebdfe1aae6e0300075e8340a2bcd2e1afd01fe` |
| `notes/theory/2026-10-12-fg-call-c-endpoint-construction.md` | `eb5ca0a72d2ec274f3c27ad1f50fb9211ec1ba8d5c45b803843e22b286bb2200` |
| `syntax-reference/en/src/expressions/if-expression.md` | `2b929dcdd31587c1ed5f0b0569cfc41e2f2bc29bf04a5f21be06bf24620718f3` |
| `syntax-reference/en/src/expressions/operator-chain.md` | `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-syntax/src/expression/if_expr.rs` | `77ae21897cf23988c394686cb823b4f3d731b53aa483566a73c67295a7326fba` |
| `.codex/config.toml` | `993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| Scala reference `shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Scala reference `shared/src/main/scala/simplesub/syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-odd-even-user-source-elaboration.md`.
- Baseline: `d55c4db850e74ba4cc0926402de5d399f610540e`;
  Scala reference: `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none; direct source snapshot above.
- Claim/review: frozen unreviewed scoped source inventory and primitive
  construction obstruction; no established exact-source theorem or refusal.
- Checks: static source/rule reads, dependency hashes/baseline comparisons,
  leased-file whitespace/scope inspection; no tests/builds/probes.
- Proposed checkpoint: `research: locate exact odd-even primitive formation boundary`.
- Shared-record deltas left for primary/curator: record the actual comparison
  declaration/application as the next original-source premise; preserve separate
  Int/true/subtraction/Branch/complete-Call debts, distinct n binders and
  publication cuts. Keep original source/core correspondence, intrusion,
  soundness/principality, effects/Call and F5 gates OPEN. Syntax-v0 limitations
  remain a separate surface characterization; no source refutation or narrowing.
