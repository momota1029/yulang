# Companion receive application: source-to-observer identity

Status: source-constructor derivation and static correspondence criterion, revision1; runtime acceptance UNOBSERVED; independent review NOT_RUN.
Assignment `RECEIVE-APPLIED-SOURCE-CORRESPONDENCE-20261018`.
Author `/root/npair_local_route_authentication_proof`; descendants0.
Sprint `npair-applied-fixture-replay-observation-20261018` rev1 SHA-256
`3223aec16eb3026a874676492c334199433b3333f539375e8ad3064107e4b23d`.
Baseline supplied by Luna `aa808f96543474d85fe70fba92161f94cf4cfd9a`; start commit supplied `c3e42d07d`; no Git operation.
Requested Sol/prover/high; observed model/effort UNKNOWN/UNKNOWN.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN, closure **0 -> 0**.

## 1. Exact companion and identity discipline

Let B be the immutable original fixture bytes, SHA-256
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.
The permitted companion C is B followed only by a trailing explicit declaration
`my received = receive f0` and separating/trailing whitespace. Its include path,
disk path and `ModuleIdentity::source_root(FileId::new(FileKey::new(...)))`
path must all name `tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu`
in realm `yulang-research`. Exact C/harness bytes belong to the implementation
freeze, not to an invented pre-existing artifact. At proof intake C did not yet
exist. This derivation applies only once the final append-only byte comparison
and identity/path checks are independently established.

`FileKey` equality includes realm and full path; changing this path changes the
module identity. More strongly, `HirOccurrenceId` and `DefinitionRootId` contain
an immutable HIR artifact brand, while `SourceNodeKey` contains a parse brand,
the exact green allocation and its start. `ParsedFile::owns_source_key` checks
the parse brand, not merely text or range. Reparse/re-lower produces fresh
brands even if earlier text is byte-identical. Therefore no old occurrence,
root or source key is transported to C. Every f0, receive, received, ctrl and
choose identity below is newly derived from C's single parse/HIR pair.

## 2. Constructive derivation from actual producers

Assume successful parsing without structural recovery and successful
`shadow::lower_module_with_local_source` on C with its stated identity. These
are run prerequisites, not facts proved by this static packet.

`source_identity::try_source_keys` traverses the actual ParsedFile node tree
and records SyntaxNode -> exact SourceNodeKey. `HirSourceIdentity::new` retains
that parse root. `module::lower_module_with_counters` plans roots and constructs
the namespace; `module/local_source` construction consults that namespace for
module names. The companion's added body contains one ordinary whitespace
application with identifier callee `receive` and identifier argument `f0`, no
local binders or competing declarations of these names. On successful formation
its identifier constructor has no lexical shadow and uses the unique namespace
entry, producing `Name { resolution: ModuleDef(receive.id()) }` and
`Name { resolution: ModuleDef(f0.id()) }`.

In the application constructor, an admitted MlArgument/CallTail/ColonApplicationTail
allocates separate source-owned callee/argument slots, calls `set` with
`LocalSourceForm::Apply { callee, argument, source_form: tail.kind() }`, and
schedules the actual argument subtree and callee subtree. For `receive f0`
there is one application tail and neither identifier introduces another Apply;
thus this body's LocalSource has exactly one Apply. Its exact source key is
that **application tail node**, not necessarily the full declaration, whole
expression or callee node. No source-range equality substitutes for this fact.

`Builder::set` obtains `self.key(node)` from the parse-owned node map, allocates
an artifact-branded occurrence, records `(occurrence, key)` in HirSourceIdentity,
and stores that same key in LocalSourceExpr.source. It therefore proves, by
construction, for each of the Apply and its two operand expressions x:

```
hir.occurrence_source_key(x.occurrence) = Some(x.source)
parsed.owns_source_key(x.source)
```

Their LocalSourceIndex values carry the same source owner; `LocalSource::expression`
checks ownership before indexing. The received LocalSource owner is exactly
`SourceRootId::Definition(received.definition_root())`, and root lookup rejects
foreign HIR brands. The f0 and receive definition roots and their source keys
must be fetched from C's own HirBinding records. The exact dynamic keys/ordinals
remain unknown until the reviewed harness runs.

The same discipline applies to `ctrl::choose`: the family/member declaration,
name and signature keys are their respective actual parsed nodes. The f0
Operation expression's source key is its own use node. Its resolved declaration
must be the exact retained choose declaration Arc from this HIR. Textual member
spelling, declaration/use key equality or key equality with f0's definition are
not substitutes. The existing harness checks parse ownership, occurrence/source
key equality and `Arc::ptr_eq(resolved, choose)`; no historical operation or
mathematical contribution identity follows.

## 3. Constraint registration and actual final observer

In `candidate_source` Apply collection, the source expression index and owner,
actual callee/argument indices, endpoint/effect components, recipe index,
checking occurrence and cause are retained in ApplySourceInput. The candidate
recipe refers back to that source input. Existing `admit_candidate_fact` checks
the recipe and endpoint correspondence, forms the actual negative Function
ports and retains NativeInterface before admitting/propagating the constraint.
This is a constructor/control-flow argument conditional on reaching and
successfully executing these source actions. It does not prove acceptance of
receive's annotation, successful graph routing or Replay activation.

The actual final call site `CandidateInference::source_call` invokes
`candidate_call::observe_scoped` with the solved GraphState when scoped mode is
enabled; otherwise it invokes observe. The observer authenticates the owning
source Apply, operands, checking occurrence/cause and native Function ports.
The scoped helper additionally authenticates eligible Local routes; received's
callee here is the source ModuleDef receive and does not become a Local callee
merely because receive's body has local g.

To establish this particular call rather than a count, the reviewed harness
must observe the same HIR artifact, require no solver conflicts, and find exactly
one source call whose owner is received_owner. For that call require:

- source/operand pointer identity with the previously inventoried three
  LocalSourceExpr records, exact occurrences and source keys, and parse ownership;
- exact owner/root and source/callee/argument scope equality;
- checking occurrence equals that Apply occurrence, with its corresponding cause;
- callee resolution equals ModuleDef(receive.id()) and argument resolution equals
  ModuleDef(f0.id()), both from the companion HIR.

Exactly-one-Apply plus pointer correspondence alone proves the call corresponds
to whatever the body is; explicit target resolution proves the promised
receive/f0 operands and detects a companion edit or resolution error. The proof
lane sent this requirement to Luna because the baseline harness did not assert
these two targets explicitly.

## 4. What this closes and what the run must supply

The actual source constructors justify the exact mapping from this admitted
companion application to its source-owned Apply and operand records, then to
the registered call observer if solving reaches it. This removes the previous
fixture's purely syntactic absence of `received` once the companion delta is
verified. It does not prove that inference accepts C or produces a demand row.

The one authorized command must supply actual parse/HIR/binding/operand/source
key values, candidate outcome, exact stopping point, and complete stdout/stderr/
exit. A demand-bearing Replay row is evidence only for its retained identities
and ordered endpoints. It must be associated with this observed original_call
before attributing that row to received. Empty, missing or truncated stderr
cannot establish universal absence or consumer completeness. Aggregate flow
counts do not establish this linkage.

No companion source key, native member, call demand or Replay identity is the
original fixed semantic c. Universal R/W/Z/domain actions, active-consumer
reflection, NPAIR, F1/FK1, Call, N-Transport, soundness, principality, termination
and production remain OPEN at their prior quantifiers/domain. Original theorem
conditions genuinely closed: zero.

## Pins, checks and resources

Every12 sprint input pins matched before reliance. They are recorded in the
contract table; baseline harness SHA is
`d76cbae29f5f095ffdb5068a49556149fe4a0fcc0f5d0702ff17ad71aed35f28`.
Additional direct constructor inputs independently hashed before this write:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/shadow.rs` | `460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |

Static source reads and SHA inventory only; no compiler/build/test/runtime/Git
commands or descendants. Companion and final harness freeze is an explicit
implementation-owned premise, with fresh independent review required. Budget120s,
full120s conservatively charged; observed model/effort UNKNOWN, CPU/RAM unmeasured.
Only this note and its exact assignment inbox are written; scratch0.

## Final bounded source snapshot (22:59:27 UTC)

Before the120s stop, the companion became available. Independent byte comparison
confirmed original B is an exact prefix and the complete suffix is precisely
`\nmy received = receive f0\n`. Companion SHA-256:
`7d7ad10d00773ecef583c53a1d546737dbf92daf75a9637f45c03798eb893fad`.
Observed harness SHA-256:
`eb7e5aae0f29d9277ba191dc965918a6110eca8f054417aa44bbb0cec1f414e6`.
Its include/disk/ModuleIdentity paths all name the companion. Source inspection
finds ModuleDef(receive.id())/ModuleDef(f0.id()) checks both on the inventoried
Apply operands and on the final observed call operands. Thus these byte/path/
assertion premises are now statically supplied for this snapshot. The harness
was still implementation-owned; independent review must freeze/revalidate the
exact bytes before execution. Parse/lower/solve/Replay remain unobserved here.
