# Frozen Oracle declaration-slot and binder provenance

Date: 2026-10-08
Status: frozen research-only bounded historical characterization; compiler-referee reviewed, no findings
Yulang3 baseline: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Semantic and production authority: none

## Objective, method and result

Seek a historical source producer distinct from the already traced ordinary
App, formal/frame, selection, SCC, explanation, projection and pattern routes.
The method is a bounded constructor → identity → consumer source trace, with
an analytical discriminator of an identity shortcut. No Oracle execution or
stipulated-transition checker is used.

The distinct candidate is the **role/implementation declaration contract**.
It captures declaration-order substitution slots, source annotation binder
identities, implementation/requirement `DefId`s, source ranges, and explicit,
default or missing method correspondence. A declared-view consumer substitutes
those slots into the retained signature; a separate same-session bridge maps
logical binder identities to solver variables without making the solver
variable the logical identity.

This is a concrete declaration-provenance analogue. It does **not** construct
the missing ordinary Call `beta`, `Slots(beta)`, typed `p0`, owner/receiver
incidence, complete contribution or shared original `xi=(nu,K,D)`.
`ORIGINAL_ASSOC` and its dependent gates remain open. No novel route satisfying
that full requirement was found in these windows.

## Baseline, exact premise and claim class

Governing sources are [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5, especially §§1.1–2 and §5 item 1, and [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1–3 and 10. Source/public/internal layers remain distinct. Formation must
come from source resolution and typed elaboration, preserve original binders
and the joint assignment, and remain independent of pending `Q` success.
Source-contracts §2.1 takes an independently typed owner/view kernel as input;
C-realization does not produce that input. Approved Option 2 still permits
conservative production observations lacking source-constructor witnesses.

The supplied current-task frontier also retains directional protection of the
upper source exposure, the accepted unannotated-formal refinement and scoped
annotation permission. This pass changes none of those meanings. It does not
identify a declared role requirement with the fixed ordinary
`call(result(name f),result(name x))` source cut.

H1: the cited bytes are the files whose hashes appear below. Direct metadata
reads resolve current and Oracle HEAD to the assigned pins. No committed-blob
comparison or whole-worktree cleanliness check was performed; HEAD identity
alone does not certify source bytes equal those commits.

H2: role/implementation resolution and annotation construction succeed and
the inspected registration branch reaches `RoleImplConformanceContract::capture`.
Its module-supplied names, requirement signatures and annotation/solver map
are supplied inputs; this pass does not prove their source typing or coverage.

H3 for the local discriminator: one unambiguous role input named `a` occupies
declaration index 0; there are no associated assignments; a supplied requirement
signature has exactly one `a` occurrence and one builtin `int` leaf.

Established observations: the recorded metadata/hashes and the cited concrete
assignments/control branches. Conditional bounded characterization under
H2/H3: the contract retains declaration/binder identity separately from its
same-session solver pointer, while its reference projection omits an
occurrence's structural position. Interpreting these records as current
original slots or contributions would be an unsupported candidate assumption.
No semantic theorem, admitted-source counterexample, adequacy result,
absence theorem or independent review is claimed.

## Constructor, identity and downstream consumer

All locators below refer to files under `/tmp/yulang2-oracle-rebuild`.

1. `crates/infer/src/lowering/body/impl_decl.rs:103–135` resolves the impl
   head/description and obtains role input/associated names. At `:144–171`,
   an explicit associated assignment retains its lowered `AnnType` and CST
   source range; an omitted assignment obtains a logical
   `AssociatedInferenceBinderId` plus its `AnnTypeVarId`. This is declaration
   provenance, not a call occurrence or receipt.
2. `impl_decl.rs:209–257` obtains the impl's `SourceSpan`, captures each
   role method's requirement `DefId`, name, signature, default-body flag,
   optional source span and declaration order, and captures implementation
   method `DefId`s/source spans/order separately. At `:901–922`, requirement
   signature building adds role input/associated names and the first-input
   `self` alias before building the stored signature and adding receiver shape.
   Missing signature/companion or failed building yields `None` here; no
   source association is manufactured from successful shape comparison.
3. After `lower_role_impl_args` and optional associated-variable lowering,
   `impl_decl.rs:261–285` passes those records and the annotation/solver map
   to `RoleImplConformanceContract::capture`. Thus capture is not established
   to precede all solving or constraint submission. The source inputs already
   underwent lowering; no inference-scheduling claim follows.
4. `crates/infer/src/role_impl_conformance.rs:58–78,93–147` retains the impl
   identity, source, declared types and method records. Annotation binders
   collected from inputs, explicit assignments and prerequisites are sorted
   and deduplicated by `AnnTypeVarId`, then assigned logical universal IDs.
   This is not a reconstruction of the current original lexical binder tree.
   `:1268–1331` constructs role input slots by declaration index. Explicit
   associated slots retain their declaration index and deduplicated universal
   references; inferred associated slots retain their logical inferred binder.
   Input/associated name collisions are recorded.
5. `role_impl_conformance.rs:1404–1461` orders requirements and implementations,
   matches names, and retains all matching explicit implementations, a default
   route, or a missing route. It keeps the requirement `DefId` and source span.
   `:1464–1549` collects signature variable names and maps them through the
   declaration substitution, retaining explicit associated-slot indices and
   ambiguous names. The reference vector has no occurrence path. The full
   signature is retained separately (`:1434–1450`).
6. `role_impl_conformance.rs:602–669` defines a separate binder bridge:
   `(logical universal/inferred ID, TypeVar)` pairs are looked up using the
   retained `AnnTypeVarId`. Missing entries produce an explicit unavailable
   result. An inferred entry is retained even if it shares an annotation
   identity/solver pointer with a universal entry. The source comments limit
   the pointers to the inference session; this pass does not prove their
   preservation through serialization, generalization or fresh use.
7. `crates/infer/src/role_impl_conformance/view.rs:472–582` consumes the
   contract to produce declared input/associated/substitution/method views.
   `:2032–2046` converts logical references, and `:1912–2010` walks the full
   signature and substitutes variable names using the recorded slots.
   Missing, duplicate and ambiguous names have explicit outcomes. General
   Function/effectful/effect-row views are unavailable in these clauses;
   `role_impl_conformance.rs:376–422` separately considers the receiver-result
   first-order route when selecting explicit shadow targets. Inferred
   associated assignments suppress all targets there; default/missing methods
   produce no explicit target. `impl_decl.rs:286–289` calls that consumer.
   This is a declaration-view/shadow-target consumer, not an original Call
   owner/view-kernel introduction.

The retained chain is therefore:

```text
resolved impl/role declaration + annotation binders + source method records
  -> impl-owned declaration substitution and method correspondence
  -> logical binder / same-session solver bridge
  -> declared signature substitution and selected explicit shadow targets
```

Only constructor and consumer windows above are covered. The full module-map
producer, annotation builder, shadow comparator and later lifecycle are not
audited by this chain.

## Smallest local position discriminator

Under H3, consider these two supplied signatures:

```text
S_left  = Tuple(Var(a), Builtin(Int))
S_right = Tuple(Builtin(Int), Var(a))
```

The collector visits tuple leaves in order, but builtin leaves emit no name
and the sole variable emits `a` (`role_impl_conformance.rs:1503–1515`). Hence
both name lists are `[a]`. Slot lookup and extension at `:1473–1479` yield
the same `[ContractTypeRef::DeclaredInput(0)]` for both signatures. Yet the
variable is at tuple position 0 in the first and 1 in the second.

This two-leaf, one-variable discriminator is minimal within fixed-arity
tuples for moving one variable between positions while preserving a single
reference. It refutes the proposed shortcut “the reference vector alone
determines its typed occurrence position.” It does not show that the full
contract loses the position: the original signatures differ and remain
retained, and the declared-view tuple walk preserves their order. Reconstructing
a current typed source path from that retained type shape still requires the
independent source typing/ownership rule; source occurrence identity cannot
be inferred from the reference list or type shape by analogy.

The analytical mutation is deleting the signature/occurrence context and
using only `ContractTypeRef` as `p0`. No mutation or experiment was executed;
this is a representation discriminator, not a Yulang source counterexample.

## Independence, failure conditions and stopping boundary

Historical code grounds these payloads independently of current toy transition
models. Its annotation builder, declaration capture and view consumer share
one implementation's resolution and type-representation assumptions. They
are not independent semantic oracles, and no source-rule truth is inferred
from Oracle success. Source ranges and logical IDs provide attribution without
the missing independently typed original contribution judgment.

Failure conditions include different source bytes; failed resolution/building;
unavailable requirement signatures; missing binder-map entries; ambiguous or
duplicate substitution names; unsupported declared views; inferred associated
assignments; default/missing provisions; and terminal lowering/resource failure.
The discriminator additionally fails if `a` is not the sole unambiguous
declared input reference. These branches prevent an unconditional existence,
uniqueness or preservation assertion.

The prior [ordinary-Call novelty stop](2026-10-08-frozen-oracle-original-call-association-mechanism.md),
[annotation-declaration trace](2026-10-06-frozen-oracle-remaining-licensing-producer-archaeology.md)
and [Function-path trace](2026-10-07-frozen-oracle-function-derivation-paths.md)
exclude rebranding their App/formal/stack/explanation/projection mechanisms.
Scoped searches of the October 6–8 Frozen Oracle note family found no
`RoleRequirementSubstitution`/`ContractTypeRef` trace; that is a bounded novelty
check, not complete literature or repository coverage.

Recommended next action: return this declaration identity pattern to the
primary as a possible implementation correspondence check, then derive the
current ordinary Call slot/contribution introduction from independently typed
source premises. Do not dispatch another reference-ID or type-shape probe as
if it supplied that introduction.

## Commands, resources and frozen dependencies

Commands: bounded `cat`, `sed -n`, `nl -ba`, `rg -n`, `rg --files`, and Python
read-only SHA-256/metadata/file-existence reads. One nonexistent historical
crate path and one nonexistent occurrence file locator failed; neither is
absence evidence. Broad initial output truncated; decisive source windows,
authority sections and novelty matches were subsequently read in bounded
captures. No search claims full enumeration of the initial truncated output.

No tests, builds, Oracle execution, checker, random seeds/ranges, runtime
samples, Git command, Git mutation, formatter, children or scratch outputs.
Heavyweight process count: zero; at most four lightweight shell reads were
batched. No numeric resource budget was supplied; the worker used a narrow
serial source trace with a target of at most 15 minutes. CPU time, peak RSS
and total wall time were not instrumented; individual tool calls completed
in sub-second reported tool time. Unverified scope includes committed-blob
equality, complete source/module coverage, actual source realizability of the
discriminator, generalization/use/serialization transport, complete receiver
typing, original licensing/admission, current semantics and production
conformance. The artifact freezes on submission; producer review is not
independent review.

| Direct dependency | SHA-256 at freeze |
| --- | --- |
| `tasks/current.md` | `f77e761619e649e5dc09f085f81d898031f68911c3ea6ddd55734a372511cab9` |
| Inferred-call-views design | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Source-contracts design | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Prior ordinary-Call novelty stop | `2697c8e2db5d67be0cfdc1bfdb5b4cdea9f5ae9ee456afc55b6402a2979419ba` |
| Prior annotation-declaration trace | `03adcceed74bb8a08290e748989fd0af1e8eb417a19a7a7ba6303c29191d70d7` |
| Prior Function-path trace | `08e6995c1b09a29288cb9c5da5e52a7b6231c244baf34f42ea11c587711e1039` |
| Oracle `crates/infer/src/lowering/body/impl_decl.rs` | `7353af913f609b32502e8a0c18515aee95ef7419dc478432a9444b13e80d7b05` |
| Oracle `crates/infer/src/role_impl_conformance.rs` | `92b328ad27289dcb10d2d228d6ee4aa53f8ebbdc8bb7a19243e6d47b59321041` |
| Oracle `crates/infer/src/role_impl_conformance/view.rs` | `94130ef703f4775f10a46d9706f165a9b588195bff280242d1da66ec49aec835` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-frozen-oracle-static-slot-producer-archaeology.md`.
- Baseline SHA: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none introduced by this worker; the freeze
  inventory identifies the inspected bytes. No pinned-blob equality is claimed.
- Review status: frozen, unreviewed, research-only bounded history and
  conditional representation discriminator; no gate closure or authority.
- Checks already run: scoped novelty/source searches, direct payload and
  constructor/consumer reads, HEAD metadata and SHA-256 inventory, output-path
  absence before creation; final dependency hash and trailing-whitespace checks.
  No tests/builds/Oracle execution. Primary owns review and lease/diff validation.
- Proposed one-line checkpoint message:
  `research: trace Oracle declaration slots and binder provenance`.
- Shared-record delta intentionally left for primary/curator: optionally add
  this declaration-provenance analogue and reference-vector position
  discriminator; keep ordinary Call `ORIGINAL_ASSOC` and all dependent gates
  open. No task/index/authority/theory/question-board path was written.

## Independent review

The compiler-referee reviewed the complete note and all cited constructor,
bridge and consumer windows. No blocking, major or minor findings. The
reviewer confirmed the two-tuple discriminator under H3, the retained full
signature qualification, and the absence of any bridge to ordinary Call
`beta`, typed `p0`, receiver incidence, complete contribution or joint `xi`.
Uninspected: committed-blob equality, upstream module/annotation producers,
later shadow comparison/lifecycle, source realizability,
serialization/generalization transport and production conformance. No edits,
Git, builds, tests or Oracle execution occurred during review.
