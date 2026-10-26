# Constructed record plans: normal preservation and visible-field survival

Date: 2026-10-26
Status: checked research component; independent review pending
Baseline: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, `yulang3`
Implementation: `lean/YulangClosure/RecordBoundaryPreservation.lean`

## Original claim and exact contribution

The original target remains whole-Yulang inference soundness, including optional
records, actual adaptation boundaries, complete Call/effects, and the same
scoped witness for all uses. This component checks the record-local argument in
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex`, the section
“省略可能レコードを解釈する境界意味論” (starting at line 356). The source's SHA-256 is
`28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
That manuscript is an explicit research specification. Formalizing its local
argument does not adopt new production semantics or prove implementation of its
record adapter.

The preceding structural lattice proofs preserve record labels and optional
bits by equal-shape comparison. They do not cover the original width/optional
boundary behavior. This module addresses that distinct case directly: it
constructs a finite plan from source and target signatures and an independent
child resolver; checks required presence; executes target fields in order; and
proves the visible output's required fields, payload types and exact surviving
labels. It also checks the original counterexamples to transitive direct
checking and endpoint-only cast coherence.

The main conclusion is local normal-result preservation, not the manuscript's
full request/resumption contract. No original language constructor is deleted
and no variable is made into an implicit adaptation boundary.

## Representations and construction

All declarations are under `YulangClosure.RecordBoundary`.

`Spec Ty` retains the payload type and optional bit. A finite field list denotes
a signature using first-name lookup; `View Value` denotes the currently visible
record, as a map from labels to optional values. `ViewTyped` independently says:

- a required declared field has a value;
- every present declared value has the independently supplied payload type;
- a label outside the signature is absent from the visible view.

It does not define typing by checking success. A slot with `none` represents
absence, not an unknown payload type. The finite output list retains target
order and its absence slots; `visible` turns it into the corresponding map.
For the manuscript's finite-map signatures, target names are unique. The code's
first-match convention also makes its list representation explicit instead of
equating arbitrary duplicate physical entries.

`compileField source known resolve target` makes precisely these decisions:

1. If the source declares no such field, only an optional target compiles; its
   plan explicitly returns absence.
2. For a common field, a required target needs a required source or a true
   `known label` presence bit. A common optional target needs no presence bit.
3. Every permitted common field calls the same child resolver on the two
   payload types. Failure of that resolver fails compilation of the field,
   even when the declarations are optional.

`compile` visits the complete target list in order and constructs its complete
plan. `compileField_sound` and `compile_sound` prove its original input/output
declaration correspondence and all of these premises. `common_field_resolved`
extracts the actual child-resolution equation for any declared common field.
It therefore rules out skipping static optional-payload checking merely because
one particular input value is absent.

`PresenceValid known input` means each asserted presence bit has an actual value
in this very input view. `required_input_present` derives required lookup success
from the compiled field conditions, input typing and that independent evidence;
the caller does not supply the required lookup conclusion. Taking every presence
bit false gives the static optional-to-required rejection used by the current
native dispatcher. Allowing a verified bit models the manuscript's separate
input-specific presence evidence, not a new native acceptance rule.

## Execution and checked statements

`FieldRun child input entry trace result` describes one normal field execution.
An absent plan emits no value. A converted field reads only `input label`:
absence stays absent; a present input goes through the retained child cast.
There is no backing-object lookup and no default field generation. `Run` combines
these executions by target order, concatenating each child's actual finite
event list before the rest. An event type and child relation are parameters;
this module supplies no event admission, effect owner, or resumption semantics.

`ChildSound typed resolve child` is the independent payload premise: every
normal child execution selected by that resolver preserves the specified input
and output payload types. It neither states record preservation nor assumes a
record run. Diverging or suspending children need not have normal executions.

The principal declarations and quantifiers are:

| Declaration | Inputs retained | Constructed conclusion |
| --- | --- | --- |
| `required_input_present` | Valid field plan, independent input typing, authentic presence bits, required target | A value is actually visible at that field before child execution. |
| `run_preserves` | Valid compiled plan, input typing/presence, child normal preservation, an actual normal run | Ordered output slots satisfy every target field, including optional bits. |
| `compiled_run_preserves` | Actual `compile = some plan`, the same input/presence/child premises and normal run | `ViewTyped typed (signature targets) (visible output)`. No output typing premise is supplied. |
| `run_survivors` | Valid plan, input typing and an actual run | A label is present in output exactly when present in the input and declared by the target. |
| `composed_survivors` | Two actual sequential runs through an intermediate view, valid plans, initial typing/presence and child preservation | Output presence is the intersection of original presence, intermediate labels and final labels. |

The survivor result does not need child type preservation; label creation is
already excluded by the actual field-run constructors. The composed result uses
first-run preservation to establish the intermediate view's typing, then applies
the one-step survivor equality twice. It does not assert or assume that the direct
source-to-final comparison succeeds.

`execute` is a concrete pure-payload specialization. `execute_runs` constructs
its normal run with the empty event trace. The general preservation result is
not limited to this specialization.

## Mechanically checked original discriminators

`Witness.direct_comparison_nontransitive` calculates all three compiler results
for the manuscript's exact shapes:

```text
A = {foo?: string}, B = {}, C = {foo?: int}
A -> B: succeeds, B -> C: succeeds, A -> C: fails.
```

The child resolver accepts equal primitive payload types only. No opaque oracle,
project axiom, assumed rejection or unchecked native evaluation establishes these
equations. Both optional payloads are still compared in the direct case.

`Witness.accepted_paths_have_different_views` calculates a second discriminator:
from `{foo: int}` and the visible value `{foo = 1}`, direct adaptation to
`{foo?: int}` keeps `1`, while the accepted path through `{}` ends with `foo`
absent. All three involved plan-compilation equations and both execution results
occur in the theorem. Thus these are two genuinely accepted paths, not comparison
of a successful path with a rejected one.

These examples check the semantics of this constructed record component. They
are not claims that the native compiler already implements surface cast chains.

## Actual native correspondence and remaining owners

The actual record dispatcher in `crates/yu-solver/src/lib.rs`, starting near
line 14593 at the frozen baseline, builds a first-source-field table, visits
target fields in declaration order, permits a missing optional target, records
a missing-required diagnostic, returns `RecordAdaptationUnavailable` for
optional-to-required without concrete evidence, and issues every permitted
common payload comparison. It retains each child index and ordered pair in
`RecordDispatch`. The existing test
`f5b_record_comparison_is_local_and_retains_late_child_bounds` covers the same
nontransitivity, first-source-name convention, optional/required distinction
and retained late payload constraint. This work read that owner/test; it did
not rerun them or change production behavior.

The checker above is a finite declarative transcription of those accepted shape
conditions, with the manuscript's separate authentic-presence extension exposed
as a parameter. A native `Ok` may accompany diagnostics; it is not equivalent to
`compile = some plan`. Native child admission also retains a comparison for later
solution, while `resolve = some cast` means an actual selected child cast. Those
differences remain explicit native-to-evidence obligations.

The following original premises are still owned outside this component:

- Actual source checking/elaboration must attach the correct record plan to the
  original boundary and retain boundary identity, payload evidence, owner/scope
  metadata and source evaluation order. The local module does not manufacture
  those identities or identify two boundaries.
- The original child calculus must supply normal type preservation and its
  stronger all-request-prefix/typed-resumption contract. Concatenating traces
  does not prove that stronger contract.
- Defaults, head/tail spread, open rows, nominal projection/cast resolution and
  hidden source dependencies require their original rules. They are absent
  from this record-adaptation component, not removed from the language.
- The native solver's successful retained constraints must construct the
  selected child evidence and source derivation with the original joint witness.
  Neither a finite structural lattice model nor this local record theorem
  establishes that whole-source reconstruction.

Consequently `SourceProblem.InferenceSoundness` remains OPEN. The reduced
obligation is the record plan's own normal shape/payload preservation and exact
non-resurrection law; the remaining work is its genuine source/native and
effectful-child application, rather than a fresh assumption of the record
conclusion.

## Verification and review handoff

Pinned Lean 4.35.0; isolated project/cache at
`/workspace/scratch/f98087c7ac1a/inference-record-boundary`. Checks use one thread,
1 GiB and a 120-second bound each. Initial failures and repairs are retained in
`check-01.log` through `check-04.log`; `check-05.log` passes without warnings.
The subsequent module build passes two jobs. The complete originating-module
audit covers 77 distinct theorem constants, including all fourteen public
theorems and generated/private declarations: 62 use no axioms, 11 use only
`propext`, and four use `propext` plus `Quot.sound`. There is no `Classical.choice`
dependency in this component. Build log SHA-256:
`47e45f2edc5f25dfb410eac3424f093676e2b7bc9ca5907251684d924282a520`;
full audit log SHA-256:
`9b875fa0d6aadf27f488d80ea6332be31999388ff2f2a57e5094fd4f901559d6`.
Frozen Lean source SHA-256:
`1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056`.

No project axiom, proof hole or kernel bypass is used. Fresh nonauthor review
must inspect this exact source, its independent predicates and the above
application boundary before integration.
