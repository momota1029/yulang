# R158 Rust original App correspondence map

Disposition: **NO_SAFE_CODE_SLICE** for an end-to-end original App admission
implementation under this packet. STOP after this receipt. This is a bounded
source inspection, not a compiler execution result or a whole-source absence
claim.

## Authenticated inputs and scope

Immutable baseline: `78728e6774e97ca84ae3008888c2d1028ebb744c`, as supplied by
the R158 contract. Only these two baseline blobs were inspected:

| Source | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2` |

The immutable reads used `git show` for exactly those two paths, under the
explicit exception in the assignment. No dirty worktree scheme/receiver,
runtime file/blob, other source, Cargo, test, build, checker, formatter or Lean
invocation was read/run. No source was changed. The only written path is this
receipt. The reviewed R157 observer is accepted only at its contract identity
`shadow_apply.rs` SHA-256
`99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`;
its contents were not re-read or independently reviewed here.

## Exact retained chain

1. `ApplySourceInput` (`candidate_call.rs:39`) retains source owner, App
   expression index, two separate `LocalSourceIndex` operands, source level,
   recipe, both candidate value/effect endpoints, result/application-effect
   coordinates, complete checking identity/cause, optional formal/local route,
   and optional `NativeInterface`. `NativeInterface` (`:137`) retains callee,
   argument, both evaluation effects, result, negative Function demand,
   invocation effect/row and application effect.
2. `observe_inner` (`:493`) resolves the retained owner to its `LocalSource`,
   requires the actual expression to be `LocalSourceForm::Apply`, compares
   **both exact operand indexes** with the retained indexes, requires the
   checking occurrence to be this App occurrence, checks its cause, resolves
   both operands and checks ownership/scopes (`:502`–`:527`). It returns the
   original App and both operand expressions without restricting the argument
   to a literal or the callee to a Name.
3. The same observer requires the native demand to be a negative Function with
   exactly `[argument, argument_effect, invocation_effect, result]`, then
   checks value/effect kinds and polarities and exact invocation-row ordinal
   (`:529`–`:576`). Native callee/argument and their evaluation effects are
   positive; result, invocation effect and application effect are negative.
   These are retained-constructor observations. This observer does not itself
   reconstruct operand typing or compare the native operand Terms with the
   candidate endpoint/recipe coordinates retained in `ApplySourceInput`.
4. The optional formal path preserves parameter identity, source root, Lambda,
   Name resolution and supported source wrapper route (`:578`–`:627`). An
   omitted-formal introduction, when present, is matched against the exact
   registration/Name, original formal position/scope, whole checking identity,
   cause, native demand, `FunctionField::ResultEffect`, invocation effect and
   row (`:644`–`:672`). This conditional path cannot become a universal
   singleton-formal assumption for arbitrary App operands.
5. Scoped bare Local callees additionally use the exact occurrence-indexed
   retained route and local slot/id, with `authentic_use_instance()`
   (`:698`–`:748`; `candidate_scheme.rs:631`). Ascriptions, nonempty blocks and
   annotated local bindings fail this narrower route. This scope restriction
   is not a theorem about all original App derivations.
6. Graph capture retains each complete original `BoundKey(owner, side, item)`,
   relation, kind, side, endpoint nodes and evidence snapshot
   (`candidate_scheme.rs:2345`–`:2387`). In particular, side controls the owner
   selection; an unordered endpoint pair cannot substitute for the key.
7. FreshUse allocates one context-use identity and shared row vector
   (`:4523`–`:4607`). Rows share an image only through the same canonical-row
   table, with fresh allocation conditional on local ownership, level above
   the boundary and non-generic status. Terms, effect operands, scope/input
   maps, relation maps and evidence maps remain together in
   `RetainedFreshUseMaps` (`:637`, `:810`). Support/Allowance reconstruction
   preserves the endpoint variant through remapped effect views
   (`:4660`–`:4686`); Contribution has its own branch. This is not a reason to
   reclassify an operation Support as a Contribution.
8. Fresh-bound restoration rebuilds both endpoints, preserves side/owner
   orientation, transports the original relation with this use identity and
   original complete key, then supplies the imported antecedent and mapped
   relation to physical admission (`:4941`–`:4987`). Module Name routing ties
   the graph root to that use's value component and retains exact provider,
   receiving owner and definition-use identity (`:4989`–`:5055`). The Local
   path analogously restores all captured bounds before linking its copied
   root to the exact occurrence's component (`:5424`–`:5442`). A Name route's
   ordinal-zero constraint occurrence is not an authenticated original App
   ViewLogic binder.
9. `authenticate_demand_transport` has a substantial *conditional* retained
   chain (`:1074`–`:1250`): exact context-use identity, original demand root,
   unique source relation with matching original-call identity, matching
   captured key/snapshot/import, scope/input remap, four mapped ports, fresh
   witness, physical emission/fiber/readback and Replay ancestry. It checks
   exact complete Replay keys and four typed child relations. Argument and
   argument-effect ports reverse orientation; result-effect/result ports
   preserve it (`:934`–`:953`). It accepts the supported zero-step copied-root
   to Replay-upper case explicitly (`:1202`–`:1205`). It does not authenticate
   a general missing intermediate constructor. Its result remains an
   ephemeral observation (`:828`), not propagation authority.

## First missing owner law

The **original App source constructor / Gen-Call-0 producer** must supply the
bridge from an authenticated original App derivation to the selected descriptor
and interface at that same App's ViewLogic binder. The bridge must preserve
both arbitrary operand derivations, every original Local premise, both finite
Checking judgments, the exact App occurrence, descriptor/interface choices and
the conditional singleton-formal origin. It must relate the two original
operand interfaces and checking judgments to the retained native operand
Terms, negative demand and complete admitted BoundKeys. No such constructor
output is supplied by either inspected file.

The precise distinction is visible in `CandidateSourceCall::pending_construction`
(`candidate_call.rs:389`): it returns a request. Its supplier list (`:407`)
unconditionally retains `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier` and
`ReceiverDispatchAndCompleteResultFutureInterfaces` as missing compiler
suppliers; formal and direct-module paths add their own missing suppliers.
`OriginalGenCall0Input` (`:252`) enumerates required coordinates, including
declaration/interface, complete demand, both lexical uses, Call/checking
occurrences, both output positions and elimination origin. Listing these
coordinates and borrowing a negative Function supplies no original typing
derivation. The source observer's occurrence comparison also supplies no law
identifying the checking role/ordinal with the original ViewLogic binder.

The **source/native correspondence owner** must then show that the actual
producer emits those exact keys and that the retained FreshUse/Replay chain
belongs to the selected original constructor. The existing transport observer
can preserve an already authenticated producer's data; it cannot manufacture
the producer's source admission law. Historical receipt identity, equal family,
matching Function shape, or equal rows cannot supply this law.

## Integration decision

There is a lawful bounded *observation* chain for an authentic retained Call
and a supported copied demand. There is no justified end-to-end original App
admission implementation slice in these two sources under the present
authority. Adding a production API, treating supplier enums as proofs, or
generalizing the zero-step transport case would not close the missing law.

The next constructive packet belongs to the original source App/Gen-Call-0
constructor owner: derive descriptor formation/admission with the unchanged
premises above and provide a source-to-retained-key witness. Only after that
witness has an independent review can an implementation consumer be selected.
Rust compilation/runtime behavior, parent soundness, whole effect hygiene and
source/native closure remain OPEN. **STOP; NO_SAFE_CODE_SLICE.**
