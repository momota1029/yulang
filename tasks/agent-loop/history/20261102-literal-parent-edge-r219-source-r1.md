# R219 source lane — literal producer/consumer map

Status: **NO_SAFE_CODE_SLICE**. Read-only source correspondence audit complete;
no Rust change, abstract source law, or parent premise is closed. This handoff
does not claim a counterexample to adopted L1.

## Frozen target and reused results

The parent remains `YulangClosure.SourceProblem.InferenceSoundness` with its
original quantifiers and witness. L1 fixes each raw literal's complete payload,
`τ(l) = PaperTypes.literalType(p(l))`, `v(l)`, `Value(τ(l))`, original
`(q,r,e₀,ξ,ω)`, and pure `Comp(empty, τ(l))` Return. L1 deliberately does not
define Simple-sub generation, satisfying-assignment readout, or Rust behavior.

R214 rejects the one-sided `atom(code τ(l)) ≤ var(q)` readout: an arbitrary
upper `.top` node satisfies that bound while reading back the wrong descriptor.
R215's candidate adds the reverse bound and reads the equivalence class under
`RegularSub`; it removes that particular countermodel, but does not prove the
equivalence class denotes the original source `Descriptor`, map endpoints, or
provide the pure-effect/source-witness equation. These results remain
candidate/stopping evidence, not parent premises.

## Authenticated implementation path

`yu_hir::shadow::LocalSourceForm` carries `Unit`, `Integer(Box<str>)`,
`Boolean(bool)`, `String(Box<str>)`, and `DecodedString(Box<str>)` as literal
forms. The local source collector in `candidate_source.rs` visits each source
expression and its `Work::Finish` branch obtains its original HIR
`HirOccurrenceId`. For those five forms, it emits four `ConstraintOccurrence`s
at local slots 0–3:

```text
slot 0: positive literal leaf ≤ this expression's Value component
slot 1: this expression's Value component ≤ negative literal leaf
slot 2: EffectBottom ≤ this expression's Effect component
slot 3: this expression's Effect component ≤ EmptyEffect
```

`Unit`, `Boolean`, and string forms choose the corresponding positive/negative
leaf pair; `Integer` and the branch default choose Int. The raw integer/string
payload is not copied into a solver term: the form only selects a type leaf,
while its spelling/value remains in the source HIR. `FloatBits`, `Bytes`,
`Path`, and `Character` have no corresponding literal constructor in this
`LocalSourceForm`/branch. This observation is limited to the inspected local
source candidate path; it is not a language-domain restriction or an L1
reinterpretation.

The exact producer is the `Work::Finish` literal arm plus `InferenceBatch::emit`
in `crates/yu-solver/src/candidate_source.rs` and `crates/yu-solver/src/lib.rs`.
`emit` creates `ConstraintOccurrenceId(occurrence, local_slot)` and derives its
`CauseId` from that ID. In root schedules, `append_source_facts` retains the
occurrence indices as `Action::Fact`; `execute_candidate_action` sends each to
`admit_collected_fact`. That consumer admits the constraint to the solver store,
records provenance, converts the endpoints to a canonical Value or Effect
pair, and calls the corresponding live worklist propagation routine.

The candidate's proxies for parts of the L1 coordinates are:

- `q`: the HIR expression occurrence, plus a different local slot for each
  generated fact;
- candidate Value/Effect coordinates: the `ComponentPositions` value/effect
  components for that expression;
- source owner: the schedule's `SourceRootId` and `source_owners` entry;
- source scope (when the scoped experiment is active): a generated
  `candidate_scope::EffectScopeId` associated with the occurrence;
- runtime solver readout: the session store/typed graph, whose exported bounds
  expose structural leaves and rows.

The inspected path does not define maps equating these implementation
identities with L1's abstract `q`, root `r`, ambient event `e₀`, scope `ξ`, and
shared witness `ω`. In particular, the four fact event IDs are local
constraint/provenance identities, not a proof that the original event is
preserved; `SourceRootId` is ownership metadata, not the abstract root
coordinate; the generated scope ID is not a denotation of `ξ`; and one live
session is not an independent proof that the same arbitrary satisfying
assignment supplies the source judgment and `sameScoped` witness. The effect
facts constrain the implementation expression effect between bottom and
empty-effect leaves; they do not establish the original source Return/effect
readout equation.

The emitted Rust facts are two-sided Value bounds for the represented forms,
which resembles the R215 candidate shape. Their leaves are native solver leaf
constructors, not a proved injective eight-type `code` interpretation of
`PaperTypes.literalType`; no connection from the graph's regular-subtype
equivalence class to the original source `Descriptor` is established here.
Existing candidate graph tests show represented literal leaves can reach
ordered tuple-child rows and that parsed literal local uses replay; those tests
establish candidate behavior only, not the abstract L1 implication.

## Exact missing independent equation and owner

No authorized source-only equation supports a code correction. L1 fixes the
source rule; it does not authorize a new carrier mapping, a restricted source
domain, or a new generator interpretation. The first missing independent
equation is the source/generator/solution bridge, owned by the abstract
`SourceProblem`/Simple-sub semantics and its generation relation:

```text
For every original raw literal l at (q,r,e₀,ξ,ω),
  generate independently of sourceJudgment, LiteralDeclaration, Kernel.atom,
  and the chosen solution the actual Value and Effect clauses for l;
  for every one assignment a satisfying those clauses,
    decode that same assignment at the original q into
      descriptor = Value(τ(l)), intrinsic effect = empty,
    take value = v(l) from the original source constructor, and construct
      Return = Comp(empty,τ(l))
    while preserving r,e₀,ξ,ω and all enclosing contextual obligations.
```

For the R215 two-sided candidate, this equation must additionally prove that
the eight type encodings agree with L1's eight `literalType` cases and that the
same assignment's regular-subtype equivalence class denotes the original
descriptor/effect coordinates. No such generator/denotation/endpoints law is
present in the frozen R214/R215 model. Therefore a helper, observer, test,
Rust-only edit, or assumed readout would move the missing premise rather than
close it. Return **NO_SAFE_CODE_SLICE** to Luna; no Rust correction is
authorized by the existing equation, and the original literal induction edge
remains open.

## Bounded inspection receipt

No Cargo, build, test, Lean, Git, or mutation command was run. Read-only
inspection used `sed`, `nl`, `rg`, and `sha256sum` on the paths below. Relevant
anchors: `candidate_source.rs:1592–1606` (literal generator),
`lib.rs:2185–2201` (occurrence emission),
`candidate_source.rs:2262–2264,2481` (fact action),
`lib.rs:11546–11592` (native admission/typed consumer),
`yu-hir/src/module/local_source.rs:348–370` (local source forms),
`shadow_apply.rs:2620–2640,2865–2890` (native leaf readout), and
`candidate_context_tests.rs:4700–4730` (literal leaves reach tuple child rows).
The local literal replay test was inspected at
`candidate_context_tests.rs:5488ff`; it covers candidate local-use replay, not
L1 source semantics.

SHA-256 at inspection:

```text
crates/yu-solver/src/candidate_source.rs
  bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49
crates/yu-solver/src/lib.rs
  429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be
crates/yu-solver/src/shadow_apply.rs
  99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5
crates/yu-hir/src/module/local_source.rs
  7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1
crates/yu-solver/src/candidate_context_tests.rs
  0aec86b787796e4024e3d0d04fd755c7160d0cd76811ed49395230ea1fb64422
notes/design/2026-11-02-literal-l1-adoption.md
  f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8
notes/theory/2026-11-02-literal-independent-equation-r214.md
  9c19d9422b47408a6ee944d04b04ddb22d58047684144dfc276bfa6e5d01c6e9
notes/theory/2026-11-02-source-solution-readout-r215.md
  c3044d07f4290b019e2a181b032e314501ddc1bc9e37e9d8725cec3898973866
tasks/agent-loop/sprints/literal-parent-edge-r219.md
  b6f87907798e71fae274bf42213346e632b607876b3eea38d3b2a7bc00e5d038
```

Only this leased handoff path was written. No scratch files were created.
