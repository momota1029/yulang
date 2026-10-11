# Oracle nested effect annotations: predicate and scheme falsification boundary

Date: 2026-10-11
Status: frozen, unreviewed research checkpoint; original universal hygiene gate OPEN
Claim class: bounded source characterization, one conditional renaming fact, and an unresolved source premise; no source-qualified hygiene counterexample
Primary baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`
Oracle revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only
Budget: 30 minutes, static source inspection only; zero compiler/Oracle executions, builds, tests, probes, or child delegation

## Objective and governing premise

Attack only nested Function annotation predicate flow through generalization and
per-use subtraction-ID mapping. This complements the constructive proof lane.
The parent quantifiers are [negative formal source proof](../theory/2026-10-11-negative-formal-effect-source-proof.md)
§1; its missing coupled constructor/consumer law is §§5–6. They still quantify
over every formed composed-negative concrete formal occurrence, applicable
current/future lower, correlated symbolic refinement and actual fresh
use/extrusion/qualifying intrusion. No singleton result closes that claim.

[Annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 fixes composed polarity, same-attachment local subtraction, retained
symbolic connections/checks and independent same-family retention. The
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 govern inference and necessary abnormal safety.
[Contextual admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§6 does not enable general negative concrete formals. No semantics or production
authorization changes follow here; the withdrawn callback scheme is unused.

Revision identity is primary-supplied. Inspected bytes are hashed below; this
worker performed no Git operation and did not independently prove checkout
identity or source-to-binary correspondence.

## 1. Nested vectors do not reach the immediate binder predicate

All Oracle locators below begin under `crates/` in the pinned checkout.

**Bounded source fact.** Given successful `AnnConstraintLowerer` construction
of `AnnType::Function`, its returned `output_subtracts` is exactly the vector
from this Function's own `lower_ret_effect_bounds`. It does not concatenate
`param.output_subtracts` or `ret.output_subtracts`.

Derivation from `infer/src/annotation/constraints.rs:363–390`:

1. Recursively lower `param` and `ret` to paired Value bounds (369,371).
2. Lower this node's argument and result Effect bounds (370,372).
3. Form the positive Function with `param.neg`, `arg_eff.neg`,
   `ret_eff.pos`, and `NonSubtract(ret.pos, ret_eff.subtracts)` (373–379).
4. Form the negative Function with `param.pos`, `arg_eff.pos`,
   `ret_eff.neg`, and `ret.neg` (380–385).
5. Return only `ret_eff.subtracts` (389). The two child vectors are not read.

This contrasts with the actual Tuple constructor (335–348), which collects
each item's `output_subtracts`. The difference is a source fact, not a proposed
repair or an assertion that every nested permission belongs in the enclosing
predicate. Hoisting every nested predicate could alter composed variance,
scope and call timing and is not licensed by this evidence.

`connect_value_detailed:124–137` emits both annotation constraints and returns
that exact vector. `connect_parameter_computation_detailed:251–282` selects the
parameter boundary for the entire annotation tree. `lambda.rs:1278–1283` uses
the connection to build the binder's call predicate. The ordinary Function
case in `lambda_annotation_predicate_constraints:1581–1591` returns
`connection.subtracts`; Function annotations have no immediate output predicate
(`lambda_parameter_output_predicate_constraints:1571–1578`).
`mark_lambda_param_call_predicate:919–936` returns immediately for an empty
predicate and otherwise stores its weights in the actual local records.

### Smallest structural discriminator inspected

Candidate source, **not parsed, lowered or executed in this packet**:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
```

The exact constructed annotation tree under investigation is

```text
Function(Unit, arg_eff=None, ret_eff=None,
  Function(Unit, arg_eff=None, ret_eff=[resolved tick], Unit))
```

Assume the syntax/resolution supplies that tree, the formal starts Negative,
construction succeeds, and no subtraction-ID overflow occurs. Both result
descents preserve Negative. At the inner result row the ordinary closed-row
branch `constraints.rs:451–470,602–620,657–690` produces:

```text
q = function_boundary_effect_stack_inner([tick])
i = fresh_subtract_id()
inner positive ret_eff = Stack(q, PUSH_i({tick}))
inner negative ret_eff = Stack(q, FILTER({tick}))
inner positive ret Value = NonSubtract(Unit+, POP_i with FILTER({tick}))
inner output_subtracts = [POP_i with FILTER({tick})]
outer output_subtracts = []                 // outer ret_eff is omitted
cb local call_predicate_subtracts = []      // inner vector is not forwarded
```

The declaration resolution and source acceptance premises are unverified for
this exact text. The structural discriminator needs two Function nodes, a
concrete inner result row and a use of the returned callable. Deleting the
outer Function returns to the already known singleton; deleting the inner row
removes the predicate; deleting the second call removes the delayed consumer.
No global shortest-source or executed mutation claim is made.

The application constructor `tail.rs:535–563,615–627` queries
`local_callee_call_projection` before generating the ordinary Function demand.
It obtains weights only from a recoverable local binding (`690–705`).
`local_callee_def:844–849` accepts only `Expr::Var`. The first application is
constructed as `Expr::App` at 626; consequently the second application's callee
cannot recover cb's local predicate through this lookup. The direct annotation
predicate route therefore contributes no inner `POP_i` to the enclosing
latent frame for this tree. The defined-output wrapper consumes frame
predicates at `lambda.rs:1232–1237`.

**This refutes the stronger candidate premise that recursively formed nested
output vectors are all forwarded through the binder-call predicate route.**
That premise is not the selected language meaning. It does not refute universal
hygiene: the inner PUSH/POP/check still exist in the paired type tree.
`propagate.rs:257–269` keeps Function return Effect and Value as separate child
constraints, while Stack and NonSubtract normalization (`11–36`) can transport
their actual contexts. Complete replay/coalescing may retain or discharge
obligations through those paths. No final scheme or actual concrete provider
contribution is established for this candidate.

## 2. What per-use mapping does establish, and its exact limit

**Conditional source fact.** For an already formed Scheme, let `Q` be its
`stack_quantifiers`. Assume a single instantiation call, valid TypeArena nodes,
normal constructor completion, and sufficient nonwrapping fresh-ID space.
Every referenced ID in `Q` is mapped consistently within this use; distinct
IDs in `Q` map to distinct fresh target IDs, and separate instantiation calls
on the same monotonically allocating target use different target IDs.

The actual construction is `instantiate.rs:70–101,516–529`: each ordinary API
call creates one `SchemeInstantiator` with a new subtraction map. Scheme parts
prepopulate all quantified IDs through `fresh_subtract` (`620–636`). That
method checks the map before allocating (`741–747`), using
`InferArena::fresh_subtract_id` (`arena.rs:46–50`) and the counter allocator
`poly/src/types.rs:123–126`. Positive/negative Functions recursively clone all
four children (`798–808,861–871`); Stack and NonSubtract wrappers use the same
map (`835–840,891–894`). `clone_stack_weight:983–999` clones global filters,
floors, POP counts and PUSH payloads, including type arguments via
`clone_subtractability:946–979`. Recursive bounds use the same instantiator
(`1002–1028`). Thus equal source IDs in these surviving structures cannot
accidentally get different target IDs in this branch.

The root predicate also receives `u32::MAX` POP counts for each remapped
quantified ID (`770–785`); this is an actual additional operation, not proof
that the resulting contextual predicate has the desired source behavior.

**Coverage limit.** Ordinary `clone_subtract:763–768` preserves a source ID
absent from the map. Per-use independence therefore follows only for `Q`,
not for every ID ever allocated during annotation construction. The separate
`freshen_unmapped` mode has a broader mapping policy, but the ordinary scheme
APIs examined here use `false`. This fact does not demonstrate a leak: the
generalizer explicitly removes remaining unquantified entries before export.

## 3. Decisive unresolved source premise: discharge before erasure

Generalization is a semantic transformation before the renaming fact applies.
`generalize/mod.rs:805–834` prunes declared candidate entries and cleans weights.
`core/prune.rs:39–77` computes death using covariant occurrence tests, live
PUSH occurrences, declared-All exemptions and non-generic facts.
`core/stack_ids.rs:72–99,176–180` considers only nonempty PUSH stacks at
covariant occurrences; Function arguments reverse and results preserve sign.
`generalize/mod.rs:188–233` quantifies only those selected IDs (plus declared
All), then removes every other ID from all root/recursive/role weights.
The ancestor finalizer repeats that removal (`837–864`; `prune.rs:165–188`).

The removal is explicit, not a guess: `prune.rs:504–524,575–584` recursively
calls `StackWeight::without_ids`, including nested Function ports. That helper
preserves its global filter (`poly/src/types.rs:444–455`). Nevertheless raw
filter survival alone is not a publication proof:
`compact/finalize.rs:586–600,837–839` replaces the global filter with All when
reconstituting a weighted variable. Concrete negative effect prefixes are
handled separately by `compact/collect/type_nodes.rs:543–582`, which projects
filter and PUSH families into a Row prefix, and by the row finalizer.

Before publication, actual retained filter registrations do check present and
future lowers on the current machine (`bounds.rs:3213–3255,3285–3301`), and
recursive `Pos::Var` encounters install another registration (`3303–3360`).
These registrations are not proved to transfer merely because Scheme wrappers
are cloned. Neither source comment saying an ID is dead nor a liveness test
proves that every allowed future nested invocation has discharged its check,
attachment-local residual and Value-carried latent obligation.

**Precise OPEN premise:** for the nested tree above, derive from actual solved
bounds and the owning compaction/generalization path that every pruned nested
`i` is already semantically discharged or represented by a sufficient exported
Row/constraint, and that every retained nested `i` reaches the delayed call's
Effect/output consumer under the same attachment and symbolic-lower check.
Include correlated symbolic tails and independent same-family contributions.
This is the source-owned erasure/activation bridge that cannot be supplied by
the conditional per-use renaming fact. The inspected source alone did not
decide it. Stop here rather than assert a failed concrete result or construct
another transition-assuming checker.

## Evidence, coverage and resources

Method: targeted static constructor/consumer reads (`rg -n`, `nl -ba` with
bounded `sed` ranges) and `sha256sum`; note creation through `apply_patch`.
Early broad searches produced truncated captures and one absent guessed path
(`crates/types/src`); targeted actual owners were reread. This is not an
exhaustive source search. No executable Oracle, model oracle or independent
reference transition system was used. The Oracle source is the implementation
under attack and grounds the operational claims; policy and parent theorem
fix the desired scope independently. They do not establish solver reachability.
Shared assumptions are normal Rust collection/arena behavior, valid inputs,
successful selected constructors and the explicitly bounded ID allocator.

Zero builds, tests, Oracle runs, mutation runs, benchmark samples or parallel
process waves. Seeds/ranges: none. Static utilities were short single processes;
aggregate CPU/RSS and reasoning wall time were not measured. The 30-minute cap
was not expanded. Omitted: admission/resolution of the candidate source,
actual provider/body lower contribution, full solved graph/ordered queue,
all compaction/simplification paths, generic symbolic tail proof, imports,
extrusion/intrusion, handler selection, runtime elimination, integer exhaustion,
complete Call, soundness/principality and Yulang3/F5 cutover. No omission narrows
the original parent obligation.

Recommended next action: assign the exact nested erasure/activation bridge to
its Oracle compaction/generalization owners, using this candidate's full
source-generated bounds and delayed call as the discriminating case.

## Frozen dependency hashes

SHA-256; Oracle paths are relative to `/tmp/yulang2-oracle-read/`. No dependency
was edited by this worker. Baseline equality remains for the primary to check.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/theory/2026-10-11-negative-formal-effect-source-proof.md` | `262c2569935c30a369846f50fede295d7f024677dca203b5d11e56ed6484f856` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/arena.rs` | `e407480ee4984e24ce214543bfe23ed83e34883129487878df034090688bd9db` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `crates/infer/src/annotation/tests.rs` (static corroboration of nested Function syntax only) | `c94d9e62a762d4fc2cece87cc6acf8b92aa88057b885057460326ef2eedd1b7c` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-oracle-effect-nested-scheme-falsification.md`.
- Baseline SHA: `b37bfab842dd3f0a39d15c358399a068ff8e3194`; Oracle revision primary-supplied as above.
- Changed dependency hashes: none authored; inspected snapshot hashes above; revision equality unverified by this no-Git worker.
- Review status: frozen, unreviewed, research-only. No independent review of this worker's output is claimed; universal hygiene and implementation gates remain OPEN.
- Checks already run: targeted static source/rule/authority reads, dependency SHA-256 inventory and leased-note scope/whitespace inspection; no executable verification.
- Proposed one-line commit message: `research: locate nested Oracle effect predicate and scheme erasure premise`.
- Shared-record deltas intentionally left for primary/curator: record nested call-predicate noncoverage as a bounded construction fact, record per-use mapping's quantified-ID premise, and assign the explicit generalization erasure/delayed activation bridge. Retain original hygiene/Call/soundness/principality/admission/F5 gates OPEN. No shared records changed.
