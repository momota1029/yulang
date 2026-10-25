# Paper execution typing substitution — active handoff

Status: active primary-only work; no result has yet been proved for the full
paper judgment. Revision 1 is preserved as a failed attempt; revision 2 is the
active contract.

## Revision 1 result and revision 2 transition

Revision 1 exceeded its six-call cap: nine serial Lean invocations used about
25 checker seconds. The earlier grant is fully charged. The syntax-only source
passed before recursive syntax-map functions were added; the current source
snapshot then failed termination checking. No typing judgments or substitution
theorem were completed. The exact failed bytes are preserved in
`PaperTyping.lean` with SHA-256
`a89201a928d3fbc02cff8ca99c45ae9f75fba813fe4b73b2bc9ba5bcaf09958e`.

Revision 2 is recorded at
`tasks/agent-loop/sprints/paper-typing-subst-r1-rev2.md`. Four further Lean
invocations (about 17 checker seconds) still failed termination. Attached
subtype evidence remained inaccessible to the generic decrease tactic, and
composite list members required projection-size chains. Revision 3 is recorded
at `tasks/agent-loop/sprints/paper-execution-syntax-subst-r3.md`. Explicitly
named membership proofs and product/option projection inequalities now make
the full raw syntax traversal compile. Lean exited 0; it emitted only unused
callback-name warnings because the recursive termination proof consumes the
proofs. Full typing judgments and the substitution theorem are still absent.

The source is now named `PaperExecutionSyntax.lean` to reflect that it contains
raw execution syntax and substitution maps, not typing judgments. Its current
SHA-256 is
`9a978c9c58bed2cdaf560a53924cc0a15d1f2b22072da5adc0b9139a7339871c`. The current
`ValueGraph.guarded : Prop` is
only an arbitrary proposition and does not encode the paper's recursive graph
guard; replace it with the actual guard condition before claiming graph typing
or recursive-value coverage. The full paper rule inventory below remains the
acceptance criterion.

## Original theorem and coverage obligations

Parent: `docs/yulang-operational-type-safety-ja.tex:953–977`, item 2; downstream
`thm:safety` at line 1140. Required theorem substitutes one type environment
consistently through declarations, instances, contexts, plans, operation
payload/response, and result. It is a syntactic typing theorem, not a runtime
safety assumption.

Rule inventory to map one-to-one to Lean constructors:

- §types lines 126–145: declaration tables, identity-sensitive nominal and
  operation signatures, fixed primitive signatures, generated code tables;
  union/intersection evidence (same underlying value), Top/Bottom and
  explicit recursive roll/unroll.
- Lines 146–199: every value/computation raw constructor, delayed computations,
  value/computation lambda entries, wrappers and typed adapters, type
  abstraction/application, metadata views, raw continuations, recursive value
  blocks and generated templates.
- Lines 201–248: every syntactic typing rule for literals/variables, tuples,
  finite native lists, records with presence, variants, nominal constructors,
  delays/lambdas/wraps, returns/binds, force/call/split/field/lookup/switch,
  union/intersection/recursive/top/bottom/polymorphic/view forms, recursive
  blocks, perform, primitive, template and declared failures. `Bad` has no
  typing constructor.
- Lines 255–297: immutable typed value graphs, graph-reference typing,
  administrative forms, request instance/origin/metadata, and explicit
  `Bad` exclusion. The single `Xi` is shared by every premise.
- Lines 337–395: continuation and request typing, ordered bind propagation,
  call entry and adapter plans; response type differs from normal result type.
- Lines 397–464: handler, value/operation arms, attempt/wait, forwarded request,
  capture-avoiding continuation, rigid polymorphic arms and resume. The payload
  and response must use the same operation instance.
- Lines 694–718: both operation mapper adapters, source/target instances and
  all forward/response continuation paths.
- Lines 721–758: record and boundary adapter code, presence and payload
  evidence, generated nominal templates, function/thunk variance and explicit
  adapter composition.
- Lines 760–811: all eleven patterns (Wild, Var, Lit, Tuple, List, Record,
  PolyVariant, Con, Ref, As, Or), defaults, ordered guards and merge binders.
- Lines 813–838: reference protocol and State handler plans, same-typed state,
  response/update/forward and captured continuation environments.
- Lines 839–872: all thirteen source expression forms, statements, roots,
  lexical/root environments, dictionaries and generated code; source generation
  itself remains a separate theorem.
- Lines 874–938: all 62 fixed primitive signatures and result/failure cases;
  an arbitrary signature table is not accepted as a substitute.
- Lines 1012–1028: all six active frame forms, including mapop and wait, with
  intermediate and result types.

Later refined effect/profile judgments remain separate obligations and must be
named if the syntactic execution judgment cannot represent them. Existing
restricted Core/Control modules do not establish coverage of this inventory.

## Method and falsifiers

Use mutually defined syntax and typing derivations, not a generic preservation
premise. Define substitution over all type-bearing fields and derive mutual
induction cases. `DeclSubst.lean` is the operation-instantiation lemma applied
at operation premises. Under `mu`, `forall`, and rigid arms, lift the type
substitution before applying the induction hypothesis and freshen the binder.

Falsifiers include any omitted constructor, arbitrary primitive signature,
changed declaration identity, dropped label/presence/arity/freshness,
intersection proofs for different values, weakened recursion guard, mismatched
payload/response instances, `Bad` typing, or an assumption of the target
substitution result. Report the exact first counterexample/obstruction.

No independent reviewer or implementation worker has been admitted. The full
inference, executor, source/native and A/B parent goals remain open.
