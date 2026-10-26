# Independent review: structural constraint soundness

Date: 2026-10-26. Reviewer: `/root/execution_frontier`, non-author of both
constraint modules. Review packet: bounded read-only compiler-referee/Lean
review; sole write is this receipt. The reviewer's graph module is not an
input to the reviewed proof.

## Decision

**ACCEPT for the explicitly stated finite structural constraint algebra and
backward solution-reflection scope.** No BLOCKING, major or minor findings.
This is not acceptance of original whole-source inference soundness, native
trace correspondence, recursive solution existence or complete Call/effect
interpretation. The files and producer handoff explicitly retain those gates.

## Frozen inputs

| Input | Independently checked SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `tasks/agent-loop/inbox/20261026-inference-constraint-soundness.md` | `5fd04767542ebb58697665b91058d1c9e7f66511621061ef9b58210e153db16d` |
| Imported `YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

Both modules and Contracts are byte-identical to the producer's isolated
project in `/workspace/scratch/f98087c7ac1a/inference-constraints/`.

## Mathematical and source review

Read both complete modules, including every authored proof and all Step
constructors. Checked the governing source-preservation note §4 and Oct24
birth-level correction §3/BL4. Independently inspected the actual candidate
parent/copy implementation, rather than treating the legacy level-lowering
routine as its implementation:

- `crates/yu-solver/src/candidate_extrusion.rs:90–195`: high-level row copy,
  memo registration, direct link insertion and selected-bound work.
- The same file `:225–335`: variant, record, tuple and four-port function
  traversal; `:635–775`: physical lower/upper bound lane orientation.
- `crates/yu-solver/src/term.rs:150–222`: kind/polarity carriers, retained
  record presence and label, variant tag/payload ordering and function ports.
- `crates/yu-solver/src/lib.rs:14485–14655` and `:14800–14865`: actual
  structural comparisons, full variant/record matching, and four function
  child constraints.

### Directed extrusion and sharing

`Copy.link` has the correct directions: positive parent≤child and negative
child≤parent. Native insertion at `opposite(p)` installs precisely these
orientations in the original owner's upper/lower lane. `extrusion_directed`
derives its conclusion by induction from **the emitted links**, rather than
assuming approximation or step soundness.

Both argument ports of Function flip polarity; both result ports preserve it.
This matches actual candidate traversal and native comparison direction.
The effect ports remain kind-indexed and separate. The negative polarity
case correctly reverses the entire desired function comparison while using
positive argument and negative result approximations.

All recursive children use the same valuation and the same copy-name function.
Names are keyed by kind, polarity and parent; repeated visits retain aliases.
No per-field or per-use existential valuation is independently selected.
Arbitrary name collisions can strengthen constraints, but do not invalidate
this backward implication. The theorem does not promise a fresh allocation
or preservation of all preexisting solutions.

Record labels and optional bits, tuple order, variant tags and payload spines
are preserved through the executable traversal. `Sub` and Step only decompose
same-shape record/variant spines. They do not purport to cover native width,
first-visible-name selection, optional absence/adaptation, or tag-domain
matching. The source and handoff make that limitation explicit. In particular,
there is no false inference that an absent optional runtime field permits
ignoring an arbitrary declared payload constraint.

### Demand reflection, retained obligations and histories

Positive demand reflection composes old≤positive-copy with the solved
copy≤upper demand. Negative reflection composes lower≤negative-copy with
negative-copy≤old. Both use one valuation and reconstruct the original
comparison after the modeled Step has removed it.

Checked each concrete Step case. Structural decomposition retains every
required child and the complete rest of the store. Union on the lower side
emits both alternatives; intersection on the upper side emits both demands.
The inserted-row and intrusion cases retain the previous obligations, so
their backward implication needs no unjustified forward/model-existence law.
`replay_solution_iff` is stronger: it derives the new comparison from the two
actually retained opposite bounds and proves equality of solution sets.

`Step.intrude` requires a retained occurrence, qualification through the existing
immutable-birth `Contracts.Qualifies`, and selection only from that occurrence's
actual copies. All earlier occurrence objects remain retained. Its backward
soundness does not use qualification because any additional equalities restrict
models. That is mathematically appropriate for this direction and is not a
proof of qualification completeness, fair activation, event-ID uniqueness or
source-scoped coverage. Subset selection is a modeled finite emission step;
no claim that every required pair has eventually been emitted is made.

`History.sound` composes the derived concrete implications with one fixed
valuation. `History.empty_sound` uses actual absence of final obligations and
does not identify native success with emptiness.

### Quotient and parent-claim boundaries

`Store.quotient_pullback` renames **every** clause under one kind-preserving
map and uses exactly the valuation pulled back through that map. It preserves
shared coordinates and does not select new witnesses for clauses separately.
`History.quotient_sound` applies this pullback before history reflection.
Injectivity is correctly unnecessary for the implication. No claim that the
native union-find implementation retains every physical clause is established.

`Sub` is an independently defined structural derivability relation, not source
typing defined as successful solving. Nevertheless, interpreting it as the
original contextual source/Call/effect relation is an open bridge. Finite Term
substitution can retain variables and supplies no ground/rational model or
recursive-type solution existence. Effect atoms preserve identity but do not
prove correlated admission, owner/world evidence or source scope. Actual
selected-bound recursion, memo/worklist traces, source generation, publication
and generalization remain explicitly unrepresented. The claimed result does
not hide these premises inside a closed original theorem.

The next original-source application still requires terminal model extraction,
actual generated-clause/solver-history correspondence, and reconstruction of
the original judgment with its same scoped joint witness. This review does not
promote any of those parent gates.

## Audit and evidence inspection

No checker was rerun: no concrete discrepancy justified spending the review
budget on another execution. Inspected the successful `check-04.log`, the entire
originating-module audit script and complete receipt structure of `audit-05.log`.
Read the actual printed types for all authored application roots, including
extrusion, both demand-reflection theorems, replay, Step/History soundness and
quotient pullback.

Independently verified:

- Exactly **186 unique ordered begin/end pairs**, with module counts 90 Syntax
  and 96 Soundness. All **26 authored theorem declarations** occur in the audit.
- Exact axiom inventory: **145 none; 26 only `propext`; 15 `propext, Quot.sound`**.
  No custom axiom, `sorryAx` or `Classical.choice` occurs.
- The audit inventories actual originating-module theorem constants, includes
  generated/private helpers, rejects project axiom declarations and checks
  required roots rather than merely reporting matching names.
- No hole or bypass keyword occurs in either reviewed module.
- Scratch copies of both reviewed modules and Contracts match repository bytes.

| Evidence | Independently checked SHA256 |
| --- | --- |
| `ConstraintAudit.lean` | `333a76c407813e90bec0aaca6f9ba482d985894a47cb035c0e99a37979f9affe` |
| `audit-05.log` | `de1e3bac51c0afae311d44864fdb0f5e6687bcc06bf964bf530243e5f041fcdd` |
| `check-04.log` | `8cd643ccf8bc74c5809851b78f25c16faebc6e2b274bd0606689bfaf5cf359d0` |

Uninspected scope: full compiler behavior, all source constructors and effect
admission, actual successful solver model extraction, recursive solutions,
full native trace simulation, production/integration behavior. No Rust tests,
Lean checks or Git operations were run in this review. No proof source, cache,
configuration or previous frozen artifact was modified.

**Writes stopped after this review receipt.**
