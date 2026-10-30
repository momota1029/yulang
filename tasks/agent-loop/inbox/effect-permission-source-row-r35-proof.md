# R35 source annotation proof handoff — CHECKED CANDIDATE; WRITES STOPPED

## Delivered result and parent boundary

Owner `/root/r35_proof`; exact leased writes only:
`notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean` and this handoff.
No scratch paths, generated outputs, builds, tests, Lake commands, environment,
copy, extraction, target, cache, Git mutation, descendants, compiler changes, or
quarantined machine.rs/receiving.rs access. Both files frozen after this receipt.

Original parent: 2026-10-13 intrusion-source-preservation §§1,3,5, preserving
**every supported original source program**, lawful finite histories, original
source scopes, the shared strategy/witness, full Call/effect hygiene, required
principal coverage, progress and termination. Birth-level SCC correction is
2026-10-24 authoritative §§2–6. These parent obligations remain OPEN.
Authoritative annotation policy is 2026-10-10 annotation-effect-hygiene-integration
§§1,1.1,1.2,3,4: the actual original annotation position grants scoped permission;
equal families do not grant authority; unknown symbolic variables stay connected.
No semantic change or A/B closure is claimed.

`YulangClosure.SourceCallbackPermissionR35.source_origin` and
`selection_is_lambda` prove the actual modeled immutable lookup chain:
retained R34 owner -> root -> expression -> Lambda's exact formal -> that
formal.annotation -> constructor-directed path -> exact row. No law asserting
row authenticity is assumed. Root identity retains Definition/Expression/Member
constructors and artifact identity. SourceNodeKey uses existing R31
parse/green/start fields; formal identity retains full root and ordinal.
The snapshot owner is R34's generative retained-allocation name, not an arbitrary
row token. `authenticated_owner_bound` and `foreign_owner_rejected` connect it
to actual issue computation.

`inventory_complete` represents the **entire path-indexed inventory** of annotation
rows: for every path, the issued witness is precisely selectRow of the selected
formal's actual annotation mapped into a witness. It chooses no callback result
consumer. `authenticated_row_preservation` preserves the exact row, concrete
list and symbolic-variable list, plus formal, source position, path and composed
polarity. Complete list equality preserves order and duplicates; the index theorem
states this pointwise. `foreign_formal_same_row_rejected` rejects replacing a
formal while keeping its full row definitionally identical. `foreign_binding_rejected`
and `reject_changed_projection` reject changed root, owner, occurrence, lambda
source/range, formal identity/source/range, annotation owner/position, path or
polarity. `foreign_row_position_rejected` covers the row position itself.
The proof does not use family equality as an authority check.

`selectedPool` constructs R34's finite permissionRow from the issue result; it is
not an independent supplied list. `translate_exact` derives exact source
recomputation and variables=[] from successful candidate translation.
`symbolic_row_rejected` proves every nonempty symbolic-variable vector is
withheld from R33/R32 translation. `concrete_translation_to_r32` applies the
existing checked R34 -> R33 -> R32 theorem to this source-derived row, yielding
exact ordered row equality, coordinate length, same-owner request/consumer/arm
and constructed-table operation round trips and family coverage. It still takes
the actual decoding computation's success, which proves the coordinate
representability facts; no source row is silently coerced into a concrete success.

Represented: all SourceAnnotationValue constructors (Unit/Int/Bool/Str,
Variable/Hole/Tuple/Function), optional effects, arbitrary tuple arity, arbitrary
nested Function argument/result, exact row positions, complete concrete and
symbolic lists, all root variants, Lambda formal body identity and source
occurrence/ranges. Polarity starts contravariant at the formal and flips only
at Function.argument. `callback_result_row` establishes the path [.result] for
`() -> [E] int`; it grants no runtime execution premise. SourceEffectRow currently
stores separate concrete and symbolic vectors; no lost source interleaving is
invented. Its parser rejects >1 symbolic variable; the preservation model proves
all list lengths without removing the existing accepted case.

Source mapping: source_annotation.rs:147–200,439–477,630–697;
local_source.rs:313–324,572–584,1139–1185,1282–1313,2090–2123;
module.rs:1153–1175,1201–1307,1377–1406;
full_parse.rs:72–98. Rust source formation and field correspondence were read,
but a formal Rust-to-Lean parser/lowering simulation is **not** proved.
Other LocalSourceForm constructors are opaque non-Lambda projections and cannot
issue this witness. Parameter spelling/scope/pattern fields are irrelevant to this
lookup theorem and are not a typing proof or restriction of the parent language.
The Lean inventory is a denotational path-indexed view; finite Rust vector
traversal order is not formally simulated. Runtime permission polarity use,
selected callback-result consumption, request/Grant/History wiring, actual
invocation lifetime, native simulation, original A/B and whole-language
soundness/hygiene/principality/progress/termination/production remain OPEN.
First remaining owner: source/runtime integration must select the appropriate
authentic path with its composed polarity, bind it to the actual invocation and
actual Catch, and establish the Rust/Lean correspondence. Quarantined consumers
were neither accessed nor integrated.

## Verification receipt

Pinned Lean 4.35.0 native stdin check under read-only bwrap, no import artifacts:
Python reads the byte-pinned complete R34 standalone module, appends R35 source
with only its first import line removed, then appends every R35 theorem's fully
qualified `#check @...` and `#print axioms ...`. This checks the transitive source
in one process; it does **not** claim the delivered import has been built or that
Lake/default/public root targets were checked. Standard helper would build and
was not used under the packet's no-build constraint.
Final attempt 6: exit 0, empty stderr, no diagnostics or warnings, all **22** R35
theorem types and complete transitive axiom outputs printed below. **16** use
only `propext`; **6** use `propext, Quot.sound`; none uses Classical.choice,
sorryAx, project axioms or bypasses. Both complete source files were searched:
no sorry/admit/axiom/native_decide/skipKernelTC matches. Actual version output
and all source hashes are recorded below. This is kernel acceptance of the
stated candidate model, awaiting independent review and source adjudication.

Failures retained verbatim below: attempt 1 malformed grouped structure field
syntax caused cascading unknown declarations; attempt 2 fixed fields exposed
lookup equality rewriting and missing decidable authentication; attempt 3 fixed
that and exposed root/expression equality orientation; attempt 4 added inventory
and exposed Option-bind reduction ordering; attempt 5 had a doc-comment/omit
placement parse error. Attempt 6 repaired all of these without stronger premises
or source restriction. Failed elaboration diagnostics mentioning generated
`sorry` are retained as failures, not delivered source holes or proof receipts.

Resource evidence: six measured subprocess durations and version duration below;
no timeout and no resident verification process. Whole assignment elapsed was
not clocked at dispatch and is UNKNOWN; no invented elapsed figure. Writes stopped.

## Construction attempt 1
Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`
Exit: 1; subprocess seconds: 7.844341
```text
<stdin>:1608:12: error(lean.inferBinderTypeFailed): Failed to infer type of binder `endByte`
<stdin>:1614:21: error: Function expected at
  Parameter
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `Parameter` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1621:9: error: Function expected at
  Form
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `Form` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1625:22: error: Function expected at
  Expression
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `Expression` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1658:11: error: Function expected at
  Parameter
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `Parameter` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1664:12: error: Function expected at
  SelectedFormal
but this term has type
  ?m.7

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1668:4: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.other` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `IO.FileRight.other`
  [apply] `IO.FS.FileType.other`
  [apply] `Std.Http.Status.other`
  [apply] `Std.Internal.Parsec.Error.other`
  [apply] `Std.Http.Protocol.H1.Error.other`
<stdin>:1683:14: error(lean.inferBinderTypeFailed): Failed to infer type of binder `formalEnd`
<stdin>:1680:14: error(lean.inferBinderTypeFailed): Failed to infer type of binder `lambdaEnd`
<stdin>:1691:12: error: Function expected at
  Binding
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Binding` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1700:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1701:43: error: Function expected at
  Witness
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1707:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1708:12: error: Function expected at
  Witness
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1716:12: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1723:17: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1727:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1728:9: error: Function expected at
  Witness
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1745:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1761:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1766:24: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.lambda` could not be determined
<stdin>:1766:46: error(lean.invalidField): Invalid field notation: Type of
  formal
is not known; cannot resolve field `annotation`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Permission.annotation`
  • `CallbackHygieneCorrespondence.Step.annotation`
<stdin>:1788:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1790:41: error: unsolved goals
history : AllocationHistory
x✝ : Sort u_1
SelectedFormal : x✝
owner : RuntimeOwner history
s : sorry
path : List TypeStep
foreign : sorry ≠ sorry ∨ sorry ≠ sorry
⊢ sorry owner s path = none
<stdin>:1800:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1805:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1810:9: error: Function expected at
  SelectedFormal
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Artifact

Hint: The identifier `SelectedFormal` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1819:24: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1819:24: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1821:18: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1833:6: error: don't know how to synthesize implicit argument `Witness`
  @issue history Artifact Definition Module Parse Green (?m.36 selectedPool pool ri ei path id)
    (?m.37 selectedPool pool ri ei path id) pool { hirOwner := id } ri ei path
context:
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : SourcePool history Artifact Definition Module Parse Green
ri ei : Nat
path : List TypeStep
id : OwnerId history
⊢ ?m.36 selectedPool pool ri ei path id
<stdin>:1833:6: error: don't know how to synthesize implicit argument
  @issue history Artifact Definition Module Parse Green (?m.36 selectedPool pool ri ei path id)
    (?m.37 selectedPool pool ri ei path id) pool { hirOwner := id } ri ei path
context:
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : SourcePool history Artifact Definition Module Parse Green
ri ei : Nat
path : List TypeStep
id : OwnerId history
⊢ Sort ?u.24
<stdin>:1837:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1848:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1857:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1873:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1877:73: error: unsolved goals
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
x✝ : Sort u_1
Witness : x✝
pool : SourcePool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri ei : Nat
path : List TypeStep
w : sorry
request consumer arm : OperationCoordinate (OwnerId history)
row : List (FamilyCoordinate (OwnerId history))
symbolic : sorry ≠ []
⊢ sorry = none
<stdin>:1888:9: error: Function expected at
  Witness
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  history

Hint: The identifier `Witness` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
<stdin>:1903:4: error(lean.unknownIdentifier): Unknown identifier `translate_exact`
<stdin>:1902:2: error: Tactic `generalize` failed: result is not type correct
  ∀ (x : List (SourceEffectId Module Parse Green)),
    let table := coveringTable out.request out.consumer out.arm out.families;
    authenticate pool owner ri ei path w ∧
      ?m.40 = [] ∧
        out.families = x ∧
          out.families.length = row.length ∧
            request.family.snapshotToken = ownerToken owner ∧
              consumer.family.snapshotToken = ownerToken owner ∧
                arm.family.snapshotToken = ownerToken owner ∧
                  decodeOperation table (operationKey table out.request) = some out.request ∧
                    decodeOperation table (operationKey table out.consumer) = some out.consumer ∧
                      decodeOperation table (operationKey table out.arm) = some out.arm ∧
                        ∀ (family : SourceEffectId Module Parse Green), family ∈ ?m.131 → family ∈ table.families

history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
x✝ : Sort u_1
Witness : x✝
pool : SourcePool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri ei : Nat
path : List TypeStep
w : sorry
request consumer arm : OperationCoordinate (OwnerId history)
row : List (FamilyCoordinate (OwnerId history))
out : DecodedCoordinates Module Parse Green
success : translate pool owner ri ei path w request consumer arm row = some out
⊢ let table := coveringTable out.request out.consumer out.arm out.families;
  authenticate pool owner ri ei path w ∧
    ?m.40 = [] ∧
      out.families = sorry ∧
        out.families.length = row.length ∧
          request.family.snapshotToken = ownerToken owner ∧
            consumer.family.snapshotToken = ownerToken owner ∧
              arm.family.snapshotToken = ownerToken owner ∧
                decodeOperation table (operationKey table out.request) = some out.request ∧
                  decodeOperation table (operationKey table out.consumer) = some out.consumer ∧
                    decodeOperation table (operationKey table out.arm) = some out.arm ∧
                      ∀ (family : SourceEffectId Module Parse Green), family ∈ ?m.131 → family ∈ table.families

STDERR:

```

## Construction attempt 2
Exit: 1; subprocess seconds: 3.866868
```text
<stdin>:1747:23: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  [apply] simp only [owners]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1749:20: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1750:24: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [owners, eq_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1750:31: warning: This simp argument is unused:
  owners

Hint: Omit it from the simp argument list.
  [apply] simp [found, eq_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1767:25: warning: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [selected] at authentic

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1797:61: error: Application type mismatch: The argument
  r
has type
  (pool.roots owner.hirOwner)[ri]? = some root
but is expected to have type
  some root = some root
in the application
  And.intro r
<stdin>:1811:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.SourceCallbackPermissionR35.row_payload_exact`:
  [DecidableEq Artifact]
  [DecidableEq Definition]
  [DecidableEq Module]
  [DecidableEq Parse]
  [DecidableEq Green]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq
  Artifact] [DecidableEq Definition] [DecidableEq Module] [DecidableEq Parse] [DecidableEq Green] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1816:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.SourceCallbackPermissionR35.concrete_order_multiplicity`:
  [DecidableEq Artifact]
  [DecidableEq Definition]
  [DecidableEq Module]
  [DecidableEq Parse]
  [DecidableEq Green]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq
  Artifact] [DecidableEq Definition] [DecidableEq Module] [DecidableEq Parse] [DecidableEq Green] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1821:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.SourceCallbackPermissionR35.symbolic_variables_exact`:
  [DecidableEq Artifact]
  [DecidableEq Definition]
  [DecidableEq Module]
  [DecidableEq Parse]
  [DecidableEq Green]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq
  Artifact] [DecidableEq Definition] [DecidableEq Module] [DecidableEq Parse] [DecidableEq Green] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1853:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (authenticate pool owner ri ei path w ∧ w.row.variables = [])

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:1867:8: warning: declaration uses `sorry`
<stdin>:1873:5: warning: Variable name `success` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _success

Note: This linter can be disabled with `set_option linter.unusedVariables false`
<stdin>:1889:73: error: unsolved goals
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : SourcePool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri ei : Nat
path : List TypeStep
w : Witness history Artifact Definition Module Parse Green
request consumer arm : OperationCoordinate (OwnerId history)
row : List (FamilyCoordinate (OwnerId history))
symbolic : w.row.variables ≠ []
bad : ¬(authenticate pool owner ri ei path w ∧ w.row.variables = [])
⊢ sorry () = none
<stdin>:1893:8: warning: This simp argument is unused:
  bad

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

STDERR:

```

## Construction attempt 3
Exit: 1; subprocess seconds: 3.863064
```text
<stdin>:1803:66: error: Application type mismatch: The argument
  rfl
has type
  ?m.351 = ?m.351
but is expected to have type
  root.expressions[ei]? = some expression
in the application
  And.intro rfl

STDERR:

```

## Construction attempt 4
Exit: 1; subprocess seconds: 7.851526
```text
<stdin>:1777:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.SourceCallbackPermissionR35.selection_is_lambda`:
  [DecidableEq Artifact]
  [DecidableEq Definition]
  [DecidableEq Module]
  [DecidableEq Parse]
  [DecidableEq Green]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq
  Artifact] [DecidableEq Definition] [DecidableEq Module] [DecidableEq Parse] [DecidableEq Green] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1872:43: error: Tactic `rfl` failed: The left-hand side
  do
    let selected ← some s
    if selected.formal.id.owner = selected.root ∧ selected.annotation.owner = selected.root then do
        let row ← selectRow selected.annotation.ty path
        pure (fromSelection owner selected path row)
      else none
is not definitionally equal to the right-hand side
  Option.map (fromSelection owner s path) none

case none
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : SourcePool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri ei : Nat
s : SelectedFormal Artifact Definition Module Parse Green
selected : selectFormal pool owner ri ei = some s
formalOwner : s.formal.id.owner = s.root
annotationOwner : s.annotation.owner = s.root
path : List TypeStep
⊢ (do
      let selected ← some s
      if selected.formal.id.owner = selected.root ∧ selected.annotation.owner = selected.root then do
          let row ← selectRow selected.annotation.ty path
          pure (fromSelection owner selected path row)
        else none) =
    Option.map (fromSelection owner s path) none
<stdin>:1872:43: error: Tactic `rfl` failed: The left-hand side
  do
    let selected ← some s
    if selected.formal.id.owner = selected.root ∧ selected.annotation.owner = selected.root then do
        let row ← selectRow selected.annotation.ty path
        pure (fromSelection owner selected path row)
      else none
is not definitionally equal to the right-hand side
  Option.map (fromSelection owner s path) (some val✝)

case some
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : SourcePool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri ei : Nat
s : SelectedFormal Artifact Definition Module Parse Green
selected : selectFormal pool owner ri ei = some s
formalOwner : s.formal.id.owner = s.root
annotationOwner : s.annotation.owner = s.root
path : List TypeStep
val✝ : EffectRow Module Parse Green
⊢ (do
      let selected ← some s
      if selected.formal.id.owner = selected.root ∧ selected.annotation.owner = selected.root then do
          let row ← selectRow selected.annotation.ty path
          pure (fromSelection owner selected path row)
        else none) =
    Option.map (fromSelection owner s path) (some val✝)
<stdin>:1870:23: warning: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [selected, formalOwner, annotationOwner, and_self, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1870:41: warning: This simp argument is unused:
  formalOwner

Hint: Omit it from the simp argument list.
  [apply] simp only [selected, Option.bind_some, annotationOwner, and_self, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1870:54: warning: This simp argument is unused:
  annotationOwner

Hint: Omit it from the simp argument list.
  [apply] simp only [selected, Option.bind_some, formalOwner, and_self, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1871:4: warning: This simp argument is unused:
  and_self

Hint: Omit it from the simp argument list.
  [apply] simp only [selected, Option.bind_some, formalOwner, annotationOwner, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1871:14: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  [apply] simp only [selected, Option.bind_some, formalOwner, annotationOwner, and_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

STDERR:

```

## Full theorem audit attempt 5
R35 theorem count: 22. Module SHA256: 6ad8d5b11d3b4b8bf04e2cd21a02d3d96665cc245a51d4f65121d270705eedf8
Exit: 1; subprocess seconds: 4.217117
```text
<stdin>:1776:83: error: unexpected token 'omit'; expected '#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', 'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', 'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', 'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', 'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', 'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'recall', 'recommended_spelling', 'register_error_explanation', 'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', 'syntax', 'tactic_extension', 'theorem' or 'unif_hint'
<stdin>:1875:6: warning: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
@YulangClosure.SourceCallbackPermissionR35.issueSelected_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issueSelected owner s path) (some.{0} w) ↔
    Eq.{1} s.formal.id.owner s.root ∧
      Eq.{1} s.annotation.owner s.root ∧
        Exists.{1} fun row =>
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
            Eq.{1} w (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row)
'YulangClosure.SourceCallbackPermissionR35.issueSelected_exact' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.source_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Exists.{1} fun s =>
      Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) ∧
        Eq.{1} s.formal.id.owner s.root ∧
          Eq.{1} s.annotation.owner s.root ∧
            Exists.{1} fun row =>
              Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
                Eq.{1} w (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row)
'YulangClosure.SourceCallbackPermissionR35.source_origin' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.selection_is_lambda : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) →
    Exists.{1} fun root =>
      Exists.{1} fun expression =>
        Exists.{1} fun formal =>
          Exists.{1} fun body =>
            Exists.{1} fun annotation =>
              Eq.{1} (getElem?.{0, 0, 0} (pool.roots owner.hirOwner) ri) (some.{0} root) ∧
                Eq.{1} (getElem?.{0, 0, 0} root.expressions ei) (some.{0} expression) ∧
                  Eq.{1} expression.form (YulangClosure.SourceCallbackPermissionR35.Form.lambda formal body) ∧
                    Eq.{1} formal.annotation (some.{0} annotation) ∧
                      Eq.{1} s
                        { root := root.id, lambdaOccurrence := expression.occurrence, lambdaSource := expression.source,
                          lambdaStart := expression.startByte, lambdaEnd := expression.endByte, formal := formal,
                          annotation := annotation }
'YulangClosure.SourceCallbackPermissionR35.selection_is_lambda' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.selected_owner_rejects : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
  Ne.{1} s.formal.id.owner s.root ∨ Ne.{1} s.annotation.owner s.root →
    Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issueSelected owner s path) none.{0}
'YulangClosure.SourceCallbackPermissionR35.selected_owner_rejects' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.row_payload_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row row
'YulangClosure.SourceCallbackPermissionR35.row_payload_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.concrete_order_multiplicity : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green) (index : Nat),
  Eq.{1}
    (getElem?.{0, 0, 0} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row.concrete index)
    (getElem?.{0, 0, 0} row.concrete index)
'YulangClosure.SourceCallbackPermissionR35.concrete_order_multiplicity' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.symbolic_variables_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row.variables row.variables
'YulangClosure.SourceCallbackPermissionR35.symbolic_variables_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green] {α : Type}
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    ∀
      (projection :
        YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green → α),
      Ne.{1} (projection candidate) (projection issued) →
        ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.inventory_complete : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) →
    Eq.{1} s.formal.id.owner s.root →
      Eq.{1} s.annotation.owner s.root →
        ∀ (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.inventory pool owner ri ei path)
            (Option.map.{0, 0} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path)
              (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path))
'YulangClosure.SourceCallbackPermissionR35.inventory_complete' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.authenticated_row_preservation : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Exists.{1} fun s =>
      Exists.{1} fun row =>
        Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) ∧
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
            Eq.{1} w.row row ∧
              Eq.{1} w.row.concrete row.concrete ∧
                Eq.{1} w.row.variables row.variables ∧
                  Eq.{1} w.binding.snapshotOwner owner.hirOwner ∧
                    Eq.{1} w.binding.formal s.formal.id ∧
                      Eq.{1} w.binding.annotationPosition s.annotation.position ∧
                        Eq.{1} w.binding.rowPath path ∧
                          Eq.{1} w.binding.rowContravariant
                            (YulangClosure.SourceCallbackPermissionR35.pathPolarity true path)
'YulangClosure.SourceCallbackPermissionR35.authenticated_row_preservation' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.authenticated_binding_unique : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path issued →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate → Eq.{1} issued candidate
'YulangClosure.SourceCallbackPermissionR35.authenticated_binding_unique' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_formal_same_row_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    ∀ (foreign : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green),
      Ne.{1} foreign issued.binding.formal →
        ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path
            {
              binding :=
                have __src := issued.binding;
                { snapshotOwner := __src.snapshotOwner, root := __src.root, lambdaOccurrence := __src.lambdaOccurrence,
                  lambdaSource := __src.lambdaSource, lambdaStart := __src.lambdaStart, lambdaEnd := __src.lambdaEnd,
                  formal := foreign, formalSource := __src.formalSource, formalStart := __src.formalStart,
                  formalEnd := __src.formalEnd, annotationOwner := __src.annotationOwner,
                  annotationPosition := __src.annotationPosition, rowPath := __src.rowPath,
                  rowContravariant := __src.rowContravariant },
              row := issued.row }
'YulangClosure.SourceCallbackPermissionR35.foreign_formal_same_row_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_binding_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    Ne.{1} candidate.binding issued.binding →
      ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.foreign_binding_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_row_position_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    Ne.{1} candidate.row.position issued.row.position →
      ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.foreign_row_position_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.callback_result_row : ∀ {Module Parse Green : Type}
  (effects : Option.{0} (YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green))
  (argument result : YulangClosure.SourceCallbackPermissionR35.AnnotationType Module Parse Green),
  Eq.{1}
    (YulangClosure.SourceCallbackPermissionR35.selectRow
      (YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk effects
        (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result))
      (List.cons.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep.result List.nil.{0}))
    (YulangClosure.SourceCallbackPermissionR35.selectRow result List.nil.{0})
'YulangClosure.SourceCallbackPermissionR35.callback_result_row' depends on axioms: [propext]
YulangClosure.SourceCallbackPermissionR35.path_polarity_append : ∀ (polarity : Bool)
  (left right : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.pathPolarity polarity (HAppend.hAppend.{0, 0, 0} left right))
    (YulangClosure.SourceCallbackPermissionR35.pathPolarity
      (YulangClosure.SourceCallbackPermissionR35.pathPolarity polarity left) right)
'YulangClosure.SourceCallbackPermissionR35.path_polarity_append' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.authenticated_owner_bound : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Eq.{1} w.binding.snapshotOwner owner.hirOwner
'YulangClosure.SourceCallbackPermissionR35.authenticated_owner_bound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.foreign_owner_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Ne.{1} w.binding.snapshotOwner owner.hirOwner →
    ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w
'YulangClosure.SourceCallbackPermissionR35.foreign_owner_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.selected_pool_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Eq.{1} ((YulangClosure.SourceCallbackPermissionR35.selectedPool pool ri ei path).data owner.hirOwner).permissionRow
      w.row.concrete
'YulangClosure.SourceCallbackPermissionR35.selected_pool_row' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.translate_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  (out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      (some.{0} out) →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w ∧
      Eq.{1} w.row.variables List.nil.{0} ∧
        Eq.{1}
          (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
            (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot
              (YulangClosure.SourceCallbackPermissionR35.selectedPool pool ri ei path) owner)
            request consumer arm row)
          (some.{0} out)
'YulangClosure.SourceCallbackPermissionR35.translate_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.symbolic_row_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))),
  Ne.{1} w.row.variables List.nil.{0} →
    Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      none.{0}
'YulangClosure.SourceCallbackPermissionR35.symbolic_row_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.concrete_translation_to_r32 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  (out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w ∧
      Eq.{1} w.row.variables List.nil.{0} ∧
        Eq.{1} out.families w.row.concrete ∧
          Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
            Eq.{1} request.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
              Eq.{1} consumer.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
                Eq.{1} arm.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
                  Eq.{1}
                      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.request))
                      (some.{0} out.request) ∧
                    Eq.{1}
                        (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.consumer))
                        (some.{0} out.consumer) ∧
                      Eq.{1}
                          (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                            (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.arm))
                          (some.{0} out.arm) ∧
                        ∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} w.row.concrete family → Membership.mem.{0, 0} table.families family
'YulangClosure.SourceCallbackPermissionR35.concrete_translation_to_r32' depends on axioms: [propext, Quot.sound.{u}]

STDERR:

```

## Full theorem audit attempt 6
R35 theorem count: 22. Module SHA256: f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9
Exit: 0; subprocess seconds: 4.029964
```text
@YulangClosure.SourceCallbackPermissionR35.issueSelected_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issueSelected owner s path) (some.{0} w) ↔
    Eq.{1} s.formal.id.owner s.root ∧
      Eq.{1} s.annotation.owner s.root ∧
        Exists.{1} fun row =>
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
            Eq.{1} w (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row)
'YulangClosure.SourceCallbackPermissionR35.issueSelected_exact' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.source_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Exists.{1} fun s =>
      Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) ∧
        Eq.{1} s.formal.id.owner s.root ∧
          Eq.{1} s.annotation.owner s.root ∧
            Exists.{1} fun row =>
              Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
                Eq.{1} w (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row)
'YulangClosure.SourceCallbackPermissionR35.source_origin' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.selection_is_lambda : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) →
    Exists.{1} fun root =>
      Exists.{1} fun expression =>
        Exists.{1} fun formal =>
          Exists.{1} fun body =>
            Exists.{1} fun annotation =>
              Eq.{1} (getElem?.{0, 0, 0} (pool.roots owner.hirOwner) ri) (some.{0} root) ∧
                Eq.{1} (getElem?.{0, 0, 0} root.expressions ei) (some.{0} expression) ∧
                  Eq.{1} expression.form (YulangClosure.SourceCallbackPermissionR35.Form.lambda formal body) ∧
                    Eq.{1} formal.annotation (some.{0} annotation) ∧
                      Eq.{1} s
                        { root := root.id, lambdaOccurrence := expression.occurrence, lambdaSource := expression.source,
                          lambdaStart := expression.startByte, lambdaEnd := expression.endByte, formal := formal,
                          annotation := annotation }
'YulangClosure.SourceCallbackPermissionR35.selection_is_lambda' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.selected_owner_rejects : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
  Ne.{1} s.formal.id.owner s.root ∨ Ne.{1} s.annotation.owner s.root →
    Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issueSelected owner s path) none.{0}
'YulangClosure.SourceCallbackPermissionR35.selected_owner_rejects' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.row_payload_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row row
'YulangClosure.SourceCallbackPermissionR35.row_payload_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.concrete_order_multiplicity : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green) (index : Nat),
  Eq.{1}
    (getElem?.{0, 0, 0} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row.concrete index)
    (getElem?.{0, 0, 0} row.concrete index)
'YulangClosure.SourceCallbackPermissionR35.concrete_order_multiplicity' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.symbolic_variables_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (row : YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path row).row.variables row.variables
'YulangClosure.SourceCallbackPermissionR35.symbolic_variables_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green] {α : Type}
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    ∀
      (projection :
        YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green → α),
      Ne.{1} (projection candidate) (projection issued) →
        ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.inventory_complete : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (s : YulangClosure.SourceCallbackPermissionR35.SelectedFormal Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) →
    Eq.{1} s.formal.id.owner s.root →
      Eq.{1} s.annotation.owner s.root →
        ∀ (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.inventory pool owner ri ei path)
            (Option.map.{0, 0} (YulangClosure.SourceCallbackPermissionR35.fromSelection owner s path)
              (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path))
'YulangClosure.SourceCallbackPermissionR35.inventory_complete' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.authenticated_row_preservation : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Exists.{1} fun s =>
      Exists.{1} fun row =>
        Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectFormal pool owner ri ei) (some.{0} s) ∧
          Eq.{1} (YulangClosure.SourceCallbackPermissionR35.selectRow s.annotation.ty path) (some.{0} row) ∧
            Eq.{1} w.row row ∧
              Eq.{1} w.row.concrete row.concrete ∧
                Eq.{1} w.row.variables row.variables ∧
                  Eq.{1} w.binding.snapshotOwner owner.hirOwner ∧
                    Eq.{1} w.binding.formal s.formal.id ∧
                      Eq.{1} w.binding.annotationPosition s.annotation.position ∧
                        Eq.{1} w.binding.rowPath path ∧
                          Eq.{1} w.binding.rowContravariant
                            (YulangClosure.SourceCallbackPermissionR35.pathPolarity true path)
'YulangClosure.SourceCallbackPermissionR35.authenticated_row_preservation' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.authenticated_binding_unique : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path issued →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate → Eq.{1} issued candidate
'YulangClosure.SourceCallbackPermissionR35.authenticated_binding_unique' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_formal_same_row_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    ∀ (foreign : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green),
      Ne.{1} foreign issued.binding.formal →
        ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path
            {
              binding :=
                have __src := issued.binding;
                { snapshotOwner := __src.snapshotOwner, root := __src.root, lambdaOccurrence := __src.lambdaOccurrence,
                  lambdaSource := __src.lambdaSource, lambdaStart := __src.lambdaStart, lambdaEnd := __src.lambdaEnd,
                  formal := foreign, formalSource := __src.formalSource, formalStart := __src.formalStart,
                  formalEnd := __src.formalEnd, annotationOwner := __src.annotationOwner,
                  annotationPosition := __src.annotationPosition, rowPath := __src.rowPath,
                  rowContravariant := __src.rowContravariant },
              row := issued.row }
'YulangClosure.SourceCallbackPermissionR35.foreign_formal_same_row_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_binding_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    Ne.{1} candidate.binding issued.binding →
      ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.foreign_binding_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.foreign_row_position_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (issued candidate : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.issue pool owner ri ei path) (some.{0} issued) →
    Ne.{1} candidate.row.position issued.row.position →
      ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path candidate
'YulangClosure.SourceCallbackPermissionR35.foreign_row_position_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.callback_result_row : ∀ {Module Parse Green : Type}
  (effects : Option.{0} (YulangClosure.SourceCallbackPermissionR35.EffectRow Module Parse Green))
  (argument result : YulangClosure.SourceCallbackPermissionR35.AnnotationType Module Parse Green),
  Eq.{1}
    (YulangClosure.SourceCallbackPermissionR35.selectRow
      (YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk effects
        (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result))
      (List.cons.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep.result List.nil.{0}))
    (YulangClosure.SourceCallbackPermissionR35.selectRow result List.nil.{0})
'YulangClosure.SourceCallbackPermissionR35.callback_result_row' depends on axioms: [propext]
YulangClosure.SourceCallbackPermissionR35.path_polarity_append : ∀ (polarity : Bool)
  (left right : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.pathPolarity polarity (HAppend.hAppend.{0, 0, 0} left right))
    (YulangClosure.SourceCallbackPermissionR35.pathPolarity
      (YulangClosure.SourceCallbackPermissionR35.pathPolarity polarity left) right)
'YulangClosure.SourceCallbackPermissionR35.path_polarity_append' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.authenticated_owner_bound : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Eq.{1} w.binding.snapshotOwner owner.hirOwner
'YulangClosure.SourceCallbackPermissionR35.authenticated_owner_bound' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.foreign_owner_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  Ne.{1} w.binding.snapshotOwner owner.hirOwner →
    ¬YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w
'YulangClosure.SourceCallbackPermissionR35.foreign_owner_rejected' depends on axioms: [propext, Quot.sound.{u}]
@YulangClosure.SourceCallbackPermissionR35.selected_pool_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w →
    Eq.{1} ((YulangClosure.SourceCallbackPermissionR35.selectedPool pool ri ei path).data owner.hirOwner).permissionRow
      w.row.concrete
'YulangClosure.SourceCallbackPermissionR35.selected_pool_row' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.translate_exact : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  (out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      (some.{0} out) →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w ∧
      Eq.{1} w.row.variables List.nil.{0} ∧
        Eq.{1}
          (YulangClosure.NativeCallbackCoordinatesR33.translateCoordinates
            (YulangClosure.NativeSnapshotOwnerR34.issuedSnapshot
              (YulangClosure.SourceCallbackPermissionR35.selectedPool pool ri ei path) owner)
            request consumer arm row)
          (some.{0} out)
'YulangClosure.SourceCallbackPermissionR35.translate_exact' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.symbolic_row_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))),
  Ne.{1} w.row.variables List.nil.{0} →
    Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      none.{0}
'YulangClosure.SourceCallbackPermissionR35.symbolic_row_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackPermissionR35.concrete_translation_to_r32 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq.{1} Artifact] [inst_1 : DecidableEq.{1} Definition] [inst_2 : DecidableEq.{1} Module]
  [inst_3 : DecidableEq.{1} Parse] [inst_4 : DecidableEq.{1} Green]
  (pool : YulangClosure.SourceCallbackPermissionR35.SourcePool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri ei : Nat)
  (path : List.{0} YulangClosure.SourceCallbackPermissionR35.TypeStep)
  (w : YulangClosure.SourceCallbackPermissionR35.Witness history Artifact Definition Module Parse Green)
  (request consumer arm :
    YulangClosure.NativeCallbackCoordinatesR33.OperationCoordinate
      (YulangClosure.NativeSnapshotOwnerR34.OwnerId history))
  (row :
    List.{0}
      (YulangClosure.NativeCallbackCoordinatesR33.FamilyCoordinate
        (YulangClosure.NativeSnapshotOwnerR34.OwnerId history)))
  (out : YulangClosure.NativeCallbackCoordinatesR33.DecodedCoordinates Module Parse Green),
  Eq.{1} (YulangClosure.SourceCallbackPermissionR35.translate pool owner ri ei path w request consumer arm row)
      (some.{0} out) →
    have table :=
      YulangClosure.NativeCallbackGrantBridgeR32.coveringTable out.request out.consumer out.arm out.families;
    YulangClosure.SourceCallbackPermissionR35.authenticate pool owner ri ei path w ∧
      Eq.{1} w.row.variables List.nil.{0} ∧
        Eq.{1} out.families w.row.concrete ∧
          Eq.{1} (List.length.{0} out.families) (List.length.{0} row) ∧
            Eq.{1} request.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
              Eq.{1} consumer.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
                Eq.{1} arm.family.snapshotToken (YulangClosure.NativeSnapshotOwnerR34.ownerToken owner) ∧
                  Eq.{1}
                      (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                        (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.request))
                      (some.{0} out.request) ∧
                    Eq.{1}
                        (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                          (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.consumer))
                        (some.{0} out.consumer) ∧
                      Eq.{1}
                          (YulangClosure.NativeCallbackGrantBridgeR31.decodeOperation table
                            (YulangClosure.NativeCallbackGrantBridgeR31.operationKey table out.arm))
                          (some.{0} out.arm) ∧
                        ∀ (family : YulangClosure.NativeCallbackGrantBridgeR31.SourceEffectId Module Parse Green),
                          Membership.mem.{0, 0} w.row.concrete family → Membership.mem.{0, 0} table.families family
'YulangClosure.SourceCallbackPermissionR35.concrete_translation_to_r32' depends on axioms: [propext, Quot.sound.{u}]

STDERR:

```

## Version and source pins
Version command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --version`
Exit 0; subprocess seconds 0.037417; stdout `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`; stderr ``
- `notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean` SHA256 `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9`
- `notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean` SHA256 `24ca25828e1a58f9c3246e5f50f2c73ba8ead6d2d003d05c8c2a8a3d2e85795a`
- `crates/yu-hir/src/module/source_annotation.rs` SHA256 `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`
- `crates/yu-hir/src/module/local_source.rs` SHA256 `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`
- `crates/yu-hir/src/module.rs` SHA256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `crates/yu-syntax/src/full_parse.rs` SHA256 `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`
- `tasks/agent-loop/sprints/effect-permission-source-row-20261031-r35.md` SHA256 `b222bb668f9c8f872dfc83a19c48c8ed937a6c5894f6e8ab5b50c5ef468ce570`
- `tasks/agent-loop/sprints/effect-permission-source-row-20261031-r35-inputs-r1.json` SHA256 `a9ef98acf98751e603046fe0c4f64ad107373513d6dd0c33c483a2ff235e1205`
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` SHA256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` SHA256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md` SHA256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`

Source search notes/theory/lean/YulangClosure/NativeSnapshotOwnerR34.lean: []

Source search notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean: []
