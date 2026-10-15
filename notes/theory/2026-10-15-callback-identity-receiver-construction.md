# Callback identity and compose: receiver-owned introduction and discharge

Date: 2026-10-15
Status: independently reviewed constructive source-constructor characterization and bounded
conditional preservation proof; proposed native correspondence, no implementation
or whole-language source/runtime closure.
Review: compiler_referee found no findings in source ownership and the conditional finite argument; native supplier, latent values and runtime premises remain OPEN.
Native baseline: `3df337fb0`; direct read dependencies frozen by hashes below.
Oracle source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, at
`/tmp/yulang-hygiene-audit-my68a_85/oracle` (O below).
Lease: this new note only. Existing reviewed proofs are unchanged.

## 1. Fixed decisions, statement and exclusions

The user's new direct decision is:

> 「id (h i) に包んでも、元の例と同じく callback の return は外側まで抜ける」という意図ですね．idは高等関数なんで意味がついては困ります

Thus the original Callback Hygiene example and its ordinary identity wrapper
must both forward the callback's return through g's local sub to the outer sub.
The earlier note's §6 attribution question is resolved for that behavior.
The [compose decision](../design/2026-10-15-compose-scoped-effect-release.md)
still requires release of the attributed e scope throughout f's output,
including f=id, while preserving effect membership and independent protections.
Neither decision authorizes a name-specific inference or execution rule.

The original parent remains: every supported accepted source computation must
preserve real effects, original binders, complete Call, providers, attachments,
joint witnesses, residual lineage, soundness and required principality. No
finite restriction below replaces its source domain or closes that parent.

Finite subclaim: for the original g/h/loop-i/callback-i/b/outer binders under one
shared `xi=(nu,K,D)`, give a source construction preserving the same h boundary
through ordinary id and synchronous nonescaping capture, expiring its protection
at the correct receiver output; preserve g's distinct direct-return control,
two fresh g uses and independently supplied protections. For straightline
`compose f g x = f (g x)`, show the e release reaches the actual whole f result.
No independently licensed second shield is assumed or introduced.

A source-wide **necessary invariant**, not a proved implementation theorem, is:
each protection introduction has its authentic source receiving owner and typed
path; each discharge names the same instance at its source-licensed output;
ordinary typed forwarding cannot choose either endpoint by effect-row equality.

Authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–3; [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md) §1.1;
[SCC charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§13–15,21,24;
current direct decision above. Reuse: [typed-boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md) §6;
[protection-only filtering](../progress/2026-10-05-handler-protection-filter-derivation.md);
[scoped kernel](2026-10-15-compose-scoped-release-construction.md) composition/renaming;
[ownership/capture](2026-10-15-effect-scope-ownership-capture.md) §§1–3,7.
Their original hypotheses remain. Excluded from this finite proof:
arbitrary latent escaping values, recursion/reentrant runtime activations,
source-wide frame selection, native guard execution, complete replay and
principal-scheme derivation. Oracle code characterizes source construction;
its runtime observations are not premises of this derivation.

## 2. Actual Oracle constructors supply a smaller introduction rule

At `O/crates/infer/src/lowering/expr/tail.rs:741–798`,
`unannotated_local_callee_return_effect` checks the actual resolved local callee:
it must be `Def::Arg`, unannotated, and have a selected Defined function frame.
It then allocates once per **(selected frame, original formal DefId)**:

```text
k = frame.unannotated_call_subtracts[formalDefId], allocated on first use
declared_subtract_fact(call_effect, k, Empty)
frame.subtracts contains matching Pop(k)
the original call demand RE upper and call-result lower carry Push(k,Empty)
```

These are actual construction actions, not interpretation of `Empty` as a pure
effect row. Their protection interpretation uses the existing hygiene results.
All calls with that same key reuse k; different source witnesses remain distinct
even when they share this key. No nominal identity is inferred from solved rows.
Annotated calls do not receive this omitted-formal introduction. The selected
concrete annotation's local permission still needs its original typed boundary;
it is not a closed cap and cannot remove an additional write contribution.

`make_app_with_origins:535–625` obtains this return view before emitting the
actual negative Function demand, then admits its lower to the result effect.
An ordinary known id is not an unannotated argument callee; its application
adds no such frame key or matching Pop. `apply_arguments:91–130` lowers its
argument in the current frame context first. Therefore inserting id around
h i does not move h's introduction to id's definition or create a release of
h's key. This fact follows from the producers, independently of observed output.

**Discharge owner is selected, not guessed from the formal Lambda.**
`unannotated_call_frame_index:801–828` selects:

1. With current Defined frame: normally the current last Defined frame.
2. If an active nested definition skeleton separates the introduced formal
   from that current frame, its explicit range test selects the introduced frame.
3. In an anonymous context with active sub syntax: the introduced frame.
4. Otherwise no qualifying frame; the call view stays bare at this constructor.

These cases describe this frozen source implementation; they are not an adopted
new language restriction. Defined parameter formation (`lambda.rs:659–770`)
retains each formal's introduced frame and complete active parameter skeleton.
Wrapping parameters in reverse (`:852–870`) pops their actual frame records.
`tail.rs::lambda_predicate_subtracts:1058–1073` collects that frame's pops;
`lambda_output_predicate_vars:1093–1110` wraps **both the entire body effect and
the body value**, not a separately reconstructed e summand.

## 3. Applying that constructor to the two selected sources

For original g with its single h parameter, call the selected frame G. The
for-body lambda captures the original h DefId. Oracle for lowering constructs
an Anonymous lambda (`block_local.rs:445–484`); unlabeled sub pushes only its
sub-syntax scope while lowering its body (`chain.rs:300–318`). Thus h's call
inside that body selects its introduced G frame by case 3 above. It introduces
k(G,h), whose matching pop belongs to g's exported output, outside the local
sub computation. A known id wrapper changes none of these selector inputs.

For a named synchronous helper capturing h, an active nested definition skeleton
with `introduced < before_frames` and current frame inside its parameter range
selects G by case 2. Its own output does not collect G's Pop. This supplies the
source owner for that captured-use case; it is not a theorem for every alias or
every anonymous context. Typed transport carries the same h profile to the
actual helper receipt; it allocates no second callback boundary or grant.
This is not a successful native-helper instance: qualifier transport/admission
through actual Effect copy links remains a separate implementation premise.

For compose's single named definition with f,g,x parameters, formation pushes
three Defined frames before lowering its body. Calls of f and g in that body
select the final x frame X by case 1: their introduced frames are within the
same skeleton, so the inner-skeleton crossing test does not select them.
They receive distinct keys k(X,f), k(X,g). X's exported body is the actual
f(g x) result. Consequently Pop(k(X,g)) wraps that complete effect variable,
including any g contribution transported through f's RE. If f=id, value-entry
forcing and return forward that same argument effect through the ordinary
four-port chain; no id-specific rule is needed. Applying the e release there
therefore affects occurrences inside f's output, as the compose decision asks.

This is a bounded placement correspondence for straightline compose's exported
result. It does not derive its principal type or equate release timing in all
larger source contexts. In particular, it does not justify the current native
heuristic that releases an argument-occurrence scope at every Apply slot 2.
The source construction can instead discharge at the authentic owner's output.
It requires one owner-bound key for h, not a new shield added beside an
unjustified earlier release. A different explicitly attributed source release
still acts on its own witness; no blanket veto of approved e release follows.

## 4. Finite owner-preservation proof, with operational hypotheses visible

Construct a finite source region forest, one region for each selected owner
frame, retaining original formal identity separately. For each used pair (F,a)
allocate one nominal key k owned by F. Introductions and output descriptors
refer to that same key. Preserve source/Call/provider/attachment witnesses w
and `xi` separately from this key; key sharing never merges their fibers.

The proof concerns any finite synchronous route generated by these actions:

- authentic omitted-call output introduction on its own typed demand;
- ordinary value entry/return or matching typed view transport;
- capture/FreshUse with explicit ownership frontiers and one shared injective map;
- discharge of precisely an owner's source-established keys at its output.

Require actual matching route/receipt and successful complete activation, as
in the existing transport and scheduling results. For the pure-argument
callback-body request q0 in the exact example, apply the existing scoped
ProtectBody(k,u) interpretation with u absent on its generating body route.
For arbitrary entry effects/other latent positions that interpretation is a
separate source bridge; the finite claim does not silently extend it.

**Induction before owner output.** Introduction adds k to q0's protection
state U. Ordinary forwarding preserves that witness by typed image composition;
known id's own source body uses its value parameter without an unannotated
Function call and so has no matching key/pop. A nested helper's own output
may discharge its own keys; distinct owner keys leave k unchanged. The same
argument iterates over any finite nesting with the stated selector/route facts.
No identity transparency is assumed as an unexplained second protection rule.

**Capture and two uses.** If helper capture frontier Q is properly below G,
k's owner G is external to Q. The existing ownership theorem fixes k under
that capture; copying a helper cannot freshly rename only its h guard. A fresh
g use instead clones G and maps k plus every introduction/output descriptor
jointly. For two fresh uses, the fresh local images are disjoint, so one g's
discharge cannot erase the other's key. This is the same map theorem already
proved; its new input here is the source-selected frame/formal owner, rather
than the h-call occurrence region. Correct Q remains a constructor premise.

**Output and frame condition.** Let S_F be precisely F's declared keys. The
existing kernel evaluates its discharge as `U -> U minus S_F`; no effect
member, origin, grant, dependency or residual lineage is changed. Each
independent t outside S_F survives. In compose, the e operation on k(X,g)
alone preserves k(X,f) and every independent t; any separate owner discharge
of k(X,f) is its own operation, not authority to delete t via e release.
Late contributions receive the same output operation when they activate;
mere retention of that descriptor does not prove the native activation premise.

**Exact controls.** While g and its local H_g are active, q0 retains the h
witness, including with id. There is no local concrete grant, so the existing
eligibility rule forwards it. At the outer handler, g expiry disables the
incidence; matching return's discarding arm leaves println/tail2 unexecuted,
as in the reviewed finite source trace. In the normal-callback control, g's
own direct q1 has no h-call source incidence and receives no h introduction;
it remains locally catchable. This conclusion uses event/typed-path identity,
not just equality of the two return families or payload types.

The induction is a proof of this owner-indexed construction with its named
source/operational hypotheses. It is not a proof that the current candidate
implements those actions, that static use IDs are dynamic activation IDs, or
that all future source constructors satisfy the hypotheses.

## 5. Concrete native bridge and first missing owners

| Actual native owner | Supplied fact / missing implementation premise |
| --- | --- |
| HIR `LocalSource::form:353–418`, local initializer formation `:431–467` | Formation knows the whole named parameter group before turning it into Lambdas. Retain the explicit group/terminal body and Defined/Anonymous source frame distinction here; do not reconstruct a group from equal source keys or names. |
| `candidate_source.rs:719–724,993–1017`; `candidate_call.rs::ReceiverBoundaryAttachment` | Original parameter, Lambda body and call-scope attachment are supplied and validated against the authentic demand. This is observational. Original formal Lambda body differs from selected terminal X for compose; attachment does not supply that selected owner. |
| Demand admission and `candidate_context_seed`; Function-port dispatch | Allocate/retain k(selected owner, formal) at the authentic source call; introduce only on its actual upper-use Effect occurrence, keeping provider lower provenance separate. Occurrence-scoped `EffectScopeId` is not already this key. |
| Lambda emission `lib.rs::admit_lambda_fact`, slot 4 | The actual body-effect -> Function RE edge is available. Supply its complete selected-owner inventory and same-instance targets before using it as the discharge. No per-name special case or arbitrary new grant is involved. |
| `candidate_context.rs` Apply slot 2; capture/FreshUse | Current unconditional Release(argument scope) caused the identity collision. A source-supported replacement must target attributed owner keys at their licensed output and share the existing map with every nested/captured reference. Adding a second guard while leaving a semantically unjustified release is not this construction. |
| Value outputs and future latent uses | Oracle wraps value as well as effect. Native Value transforms must remain identity; a corresponding deferred typed qualifier/profile must carry future descriptors. Immediate RE release alone does not prove latent closure. |
| Catch, actual calls and backend | Native scopes/attachment are not guard execution or receiver activity. Exact request eligibility, matched consumption, shallow suffix behavior, source for/sub/stdlib lowering and VM execution still need their actual owners. |

The next concrete constructor is explicit source group/selected-frame output,
followed by one shared owner-key inventory and mapped output descriptor. This
changes the earlier missing premise using its actual source supplier. No new
semantic vote is needed for the selected identity/compose cases. Full source
owner selection, late activation, reentry and latent-value/runtime bridges
remain A/B obligations; classifying them or copying Oracle carriers does not
close them. No legacy representation is adopted here.

## 6. Freeze, checks and commit packet

One constructive attempt; no tests, builds, executable probes, Oracle execution,
network, Git operations or delegation. Checks: bounded source reads, dependency
SHA-256 pins, artifact whitespace/fences/links. Allocated <=30 minutes; one
lightweight read lane, CPU/peak RAM unmeasured. Requested Sol/high; effective
runtime model/effort unknown. Fresh independent compiler-referee review passed
without findings in the declared conditional scope. Only this lease changed.

SHA-256 direct source snapshot (native paths relative to repository, O as above):

```text
359566bccaa150cbe001c060475cce3d0a3e35a37a9e45d118c0f485df2e88cf  crates/yu-solver/src/candidate_call.rs
90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab  crates/yu-solver/src/candidate_source.rs
72bdca0b4e81d587966e695bfaacef31fcc9c91e5fe67e94c9538b066fb79a86  crates/yu-solver/src/candidate_context.rs
c2d043f455434625db2338f5b98161c9d83b9e3769ae98b37af7d997fddc5ade  crates/yu-solver/src/candidate_scheme.rs
bfd2d79347d80481c5b15cc93be62006fabbcd21762a8635a1897efac3e7b51c  crates/yu-hir/src/module/local_source.rs
909042e10ce22308db75d70f62139b3858347cc74e1a8ae3d1224fcc65a9350c  crates/yu-solver/src/lib.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8  O/crates/infer/src/lowering/expr/tail.rs
2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9  O/crates/infer/src/lowering/expr/lambda.rs
e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6  O/crates/infer/src/lowering/expr/chain.rs
300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81  O/crates/infer/src/lowering/local.rs
661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898  O/crates/infer/src/lowering/expr/block_local.rs
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679  notes/design/2026-10-15-compose-scoped-effect-release.md
4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
44d69d6506f14c1658d7670ef68c46348d1315ce98ff1d2677f68993c5e00ea6  notes/theory/2026-10-15-effect-scope-ownership-capture.md
773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e  notes/theory/2026-10-15-compose-scoped-release-construction.md
```

Exact path: `notes/theory/2026-10-15-callback-identity-receiver-construction.md`.
Baseline: `3df337fb0`; semantic/dependency changes were not consumed during this
snapshot. Review status: independently reviewed conditional construction, parent OPEN.
Proposed checkpoint: `research: derive receiver-owned identity and compose release`.
Shared-record deltas left for primary/curator: replace the resolved identity
question by this finite source-owner construction; keep native group/owner
supplier, latent/runtime correspondence and global gates OPEN. One next action:
retain the explicit
named group and selected terminal-frame owner at its existing HIR constructor.
