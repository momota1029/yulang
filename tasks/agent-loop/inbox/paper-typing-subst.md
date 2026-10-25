# Paper execution typing substitution — r1 handoff

Status: active work; no result has yet been proved for the full paper judgment.

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
