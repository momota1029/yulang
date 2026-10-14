# Annotation members through copied Allowance tails

Status: reviewed bounded source/native derivation and exact operational
obstruction. A fresh M2 `compiler_referee` found no findings on frozen SHA-256
`dc618bc321d252974ffdec8116423fb191393f8d1cce71de3e6d047263e9e164`.
Research only; no theorem-status promotion or implementation authority.
Exclusive output lease: this file. Leaf; writes stopped at handoff.

## 1. Frozen objective, parent and claim

Primary-supplied checkpoint: `0a8e90aec`, on
`research/simple-sub-intrusion`; native source baseline:
`d8a6209c1dc181858948c4d811259aa20683d64e`. No Git command independently
established these identities. The native hashes below match the supplied
reviewed lineage/application/audit inputs.

The unchanged parent quantifies over every originally admitted shallow Catch
H and one original scoped assignment sigma. Preserve its scrutinee, original
operation/value-arm binders, provider, raw resumptions, complete Call and
dependent interfaces. Remove exactly eligible scrutinee contributions actually
consumed by H. Preserve protected/independent same-family survivors, unmatched
requests, outside-arm computations and raw-resumption/future contributions.
Residual constructor lineages stay distinct. No marginal projection chooses
another witness or sigma. The selected local introduction remains the
original upper Function demand's Eout only; Ein, nested positions inside B,
and existing provider/recursive lower outputs gain no protection from that
step. Independently inherited protection remains. H1/H2/U remain OPEN, H3/P
disabled, and production/F5 separate.

This packet freezes a narrower claim before deriving it. For each finite
successful native history reached from actual source Support construction,
each live original view w, each valid member ordinal k, each retained open
cut v_i with tail g, and one actual positive extrusion e at target l, derive:

1. the exact member emitted by Support and its identity under this operation's
   maps;
2. the actual BoundKeys, relation fibers, source sets and tasks that check
   that member against original/copied cuts or forward it to original/copied
   gamma rows;
3. sufficient, explicitly bounded timing cases for those consequences, and
   the precise remaining premise for the pending/remapped source case.

Hypotheses for each positive activation result below: valid branded handles,
consistent initial native graph, successful non-discarded named operations,
ordinary typed admission at the named receiving row, and successful completion
of work actually emitted. Plain activation results assume their actual fiber
contexts are IDENTITY; this is not a test for source protection. Exact memo
reuse also needs the established current-generation/completion premise. None
of these hypotheses assumes that copied current pairs are replayed. No
source restriction is selected by delimiting these cases.

Claim class: bounded constructor correspondence and conditional activation
derivation. This is neither a universal source theorem nor a source-qualified
counterexample, impossibility theorem, effect-hygiene/soundness/principality
proof or closure of H2/U. No executed source witness or probe is supplied.

Governing sources: top-level inference principles §§1–5/1.1; residual-lineage
selection, Selected policy and Preserved contract; attachment/admission §4;
directional inferred-protection §§1–2; design-authority, Authority order and
Natural compiler behavior; compiler-engineering, Natural compiler behavior
and proof-obligation economy. The top-level policy governs older general
rollback clauses. Immediate evidence: native lineage §§2–6, reviewed pending
application §§1–5 and paired falsifier, and copied-symbolic owner audit.
The pending-remapped source audit was initially an unreviewed lead; the
primary subsequently reported independent no-findings review of its bounded
source claims. Relevant owners are checked directly here; that review does
not supply a missing source history.

## 2. Authentic member and exact operation-local view identity

Code locators below are under `crates/yu-solver/src/` unless stated otherwise.
Write S(w), A(v), M(w,k), t(w) for Support, Allowance, AnnotationMember and
the view's optional tail. Let F_e(y,p) be this actual extrusion's entry
`Key(canonical(y),p,l)`, and R_e(w,h) its separate `(old_view,mapped_tail)`
view map. B(y,+,z)/B(y,-,z) are the literal native BoundKeys, with Effect
endpoint wrappers understood. This is notation for existing records, not a
new reconstruction layer. Numeric runtime RelationIds were not observed;
below each symbolic relation names its exact constructor/key and ancestry.

Authentic source entry is operation resolution in
`yu-hir/src/module/local_source.rs:694–709`, planned as Action::Operation at
`candidate_source.rs:560–574`. `candidate_operation` constructs the positive
signature at level+1 and admits its Value link (`candidate_effect.rs:786–804`).
At the outer operation Function only, signature construction injects the
resolved family into ResultEffect (`1494–1507`). Without an explicit result
effect row, this constructs a closed w with that singleton family and inserts
S(w) on a fresh port (`1527–1535`). Explicit positive concrete rows can instead
construct an open w using their actual shared signature-variable environment
(`1582–1595,1608–1645`). This does not claim that every such signature is
accepted on every source path; negative concrete variance is rejected at 1576.

Ordinary comparison involving an EffectRow first stores/replays the endpoint;
it does not eagerly split a stored S(w) (`candidate_extrusion.rs:843–867`).
When S(w) reaches the non-row operand consumer,
`candidate_check_effect_operand` emits, in member order,

```text
M(w,0) <= upper, ..., M(w,count-1) <= upper,
canonical(t(w)) <= upper                  [only if t(w) exists].
```

The owner is `candidate_effect.rs:960–982`. The member keeps w literally;
the tail is a separate sibling task, not an alternative member witness.
`canonical_effect` does not canonicalize view IDs (`lib.rs:11490–11504`).
Membership uses `views[w].allowed[k]`; forwarding an unmatched member through
A(v) queues the **same lower endpoint** M(w,k) to canonical(t(v)), without
changing w to v (`candidate_effect.rs:985–1019`). Family equality therefore
neither merges members nor supplies attachment/eligibility evidence.

Positive selected-bound extrusion has the exact equations:

```text
Phi_e(M(w,k),+) = M(w,k)                       if t(w)=None
Phi_e(M(w,k),+) = M(R_e(w,Some(F_e(t(w),+))),k) if t(w) exists
Phi_e(S(w),+)   = S(w) or S(the same mapped w) by the same cases.
```

These follow directly from Visit/EffectView at
`candidate_extrusion.rs:182–209,260–293`. If an open tail is reused because
its level is at/below l, EffectView still asks R_e for a copied view. Thus
unchanged tail ordinal does **not** imply unchanged member view ID. Closed
views take the unchanged branch for extrusion. Fresh-use reconstruction is a
different operation: it remaps even closed A/S/M operands through its own
per-use map (`candidate_scheme.rs:1065–1091`); the closed-view identity claim
above must not be extended across fresh use.

`candidate_remapped_effect_view` reuses exactly equal `(w,tail)` requests and
otherwise appends a copied view (`candidate_effect.rs:871–913`). One extrusion
has one view map (`candidate_extrusion.rs:37`), shared by EffectView and
IncomingAllowance. Therefore a copied S(w), its subsequently emitted M(w',k),
and a directly mapped M(w,k) have the same w' **when their keys agree**.
Different old w/v IDs never merge even with identical tails/heads. Opposite
polarities may choose different row-map entries/tails. If w=v and a matching
map key produces the same copied view, its own k is among that view's heads:
the native member is matched there, not an unmatched-tail discriminator.
An unmatched source member and cut generally have different view ancestors.

## 3. Bound and relation construction; storage versus activation

Let C(y,v)=B(y,-,A(v)), L(y,m)=B(y,+,m), and
K(y,y')=B(y,-,y') for a positively copied row. For every actual fiber r of a
bound B, record its RelationKey `(pair,context,sources)` and post-check context
pc(r), rather than counting origins. The owning relation interner is
`candidate_context.rs:2403–2424`; equal keys share a RelationId. Each bound's
fiber chain is `bound_relations(B)` (`2590–2621`).

| Actual event | Bound/fiber and task consequence |
| --- | --- |
| Ordinary `m <= y` | `candidate_apply_effect` inserts L(y,m), then enumerates y's opposite uppers and begins replay (`candidate_extrusion.rs:843–867,766–806`). The bound fiber is derived from the active processing relation, with pc(parent) and that parent's sources (`candidate_context.rs:3034–3075`). |
| Ordinary `y <= A(v)` | Inserts C(y,v), attaches its actual processing fiber and registers `(canonical(t(v)),y,v)` when open (`candidate_effect.rs:553–560`); then replays y's current lowers. Registration alone does not emit a member. |
| Positive Visit(g), level(g)>l | Allocates g', retains the actual parent/copy occurrence, and installs K(g,g'). Snapshots its selected lowers and scans current incoming incidence (`candidate_extrusion.rs:89–179`). Links have their extrusion-processing fiber; insertion is bare. |
| Scanned `(g,y,v)` | Schedules Visit(y,+,l), then IncomingAllowance; installs C(y',v') where y'=F_e(y,+), v'=R_e(v,Some(g')). Transports every original C(y,v) fiber (`295–309`; `candidate_effect.rs:563–574`). |
| Selected lower m already on y | Work::Bound installs L(y',Phi_e(m,+)), and transports each original L(y,m) fiber (`310–325`). It does not invoke opposite replay. |

Bare bound insertion attaches an owner-emission fiber before physical storage,
registers incidence, marks dirty and emits evidence, then returns
(`candidate_extrusion.rs:398–400,435–456,563–570`). Transport adds, for each
original r, the child relation

```text
r' = intern(bound_pair(new B), pc(r), sources(r))
Dependency::Transport(child=r', parent=r,
  witness={from:old B,to:new B,reason:Extrusion{operation,polarity,target}}).
```

It snapshots evidence and attaches r' (`candidate_context.rs:3403–3416`).
IncomingAllowance also has its owner-emission fiber; identical fibers may
intern. Neither transport nor evidence emission invokes replay. Distinct v_i'
remain distinct endpoints/fiber inputs even if relation nodes elsewhere share.

For actual replay of L(y,m) with C(y,v), each new Cartesian fiber pair
(r_lower,r_upper) creates the child with pair `m <= A(v)`, context
`Replay(context(r_lower),context(r_upper))` (IDENTITY only when both are
IDENTITY), and union of source sets. Its Dependency::Replay retains both
RelationIds and both BoundKeys (`candidate_context.rs:3131–3208`). Covered
quadrants are suppressed by retained replay heads/dependency identity, not by
nominal family equality. This is an activation owner, conditional on actual
completion or valid exact memo reuse; two stored opposite bounds alone do not
call it.

Support expansion and unmatched forwarding call enqueue_task. Child relation
admission reconstructs the child pair's own context and inherits the active
processing relation's sources, with a Derived parent dependency
(`candidate_effect.rs:403–407`; `candidate_context.rs:2403–2409,2754–2775`).
For an open Allowance upper or row upper the child-local context is IDENTITY;
a closed Allowance can instead introduce its own PrefixLeft filter
(`2683–2694`). This does **not** copy an arbitrary parent ContextExpr, nor
does it erase source-set/Derived ancestry. Thus plain native membership is
not a proof of arbitrary source-context discharge or protection conservation.

## 4. Exact-member continuation and IncomingAllowance's positive-tail route

First bounded continuation: suppose C(x,v_i) registered before Visit(g)'s
incidence scan. IncomingAllowance installs C(x',v_i') even when x genuinely
remaps. A subsequent ordinary M(w,k) lower on x' replays every retained
original/copy cut actually on x'. If x'=x, both C(x,v_i) and C(x,v_i') are
there and check the **same M(w,k)**. An unmatched member queues that exact
M(w,k) respectively to g and g'. A future Support S(w) lower has the same
conclusion after the replay child expands S(w); it is not Phi_e(S(w)) unless
an actual mapping operation produced that different endpoint. Actual IDENTITY
fibers and successful emitted-work completion give this native continuation
without substituting a Contribution.

For a lower admitted to original x when x' differs, ordinary replay can meet
both its original cut and K(x,x'). The latter delivers the original member
unchanged to x'; if copied cuts are registered there, ordinary admission
replays them. The link does not retroactively rename w. Nor does it identify
its nested Replay/source history with that of the missing direct mapped pair.

Second bounded continuation addresses the positive-tail exception explicitly.
Suppose some original open cut u has tail x and source z. Positive Visit(x)
scans `(x,z,u)` and installs

```text
C(z',u') where z'=F_e(z,+), u'=R_e(u,Some(x')).
```

This is a negative Allowance cut whose unmatched-tail task has destination
the **positive** copy x'. It invalidates a global polarity-only exclusion of
incoming members on x'. Its activation must nevertheless be traced.

If z is reused, z'=z, and both original C(z,u) and copied C(z,u') remain.
A later ordinary S(w) lower on z replays both. Each S(w)-to-cut child emits
the same M(w,k), and if the family is outside heads(u), it is outside
heads(u') because copying preserves heads. The original cut sends M(w,k)
to original x; the copied cut sends the identical M(w,k) to x'. This proves
an original-route counterpart for this authentic incoming mechanism. If the
downstream original C(x,v_i) has completed, or is emitted and eventually
completes, its checking of that original-x member supplies unmatched
M(w,k)-to-g. Later ordinary g admission replays K(g,g') and forwards the same
member to g'. Consequently this reused-upstream/plain/emitted-drain case
cannot authenticate the earlier discriminator's exclusion of every original
counterpart. It supplies a consequence by completed drain, not necessarily
before every intervening rewritten Value dispatch.

If z also genuinely remaps, bare installation of C(z',u') does not replay its
already copied lowers. A future ordinary member on z' would activate it, but
the origin and original counterpart of that future member require their own
source owner. Following incoming cuts recursively without authenticating that
owner would restate the missing premise. No general induction over arbitrary
cyclic source/copy incidence is claimed here.

Third bounded timing factorization concerns an unmatched original member that
has actually reached original g:

| Position relative to g's selected-lower snapshot | Exact consequence |
| --- | --- |
| M(w,k) physical on g before the snapshot, w closed | Selected-bound copying installs the identical M(w,k) on g'. This is an authentic case for the implicit outer operation-family Support. Bare initialization still does not activate every pre-existing upper of g'. |
| M(w,k) physical on g before the snapshot, w open | Selected-bound copying installs M(w_e,k) where w_e=R_e(w,Some(F_e(t(w),+))). It preserves member ordinal/family but may change view ID even if the tail row is reused. Comparing it to the original-route member requires the exact map ancestry, not endpoint/family substitution. |
| Ordinary M(w,k)-to-g admission occurs after snapshot | It inserts L(g,M(w,k)), replays existing K(g,g'), and queues M(w,k)-to-g' unchanged. This route retains original w; it need not equal the mapped w_e above. |
| M(w,k) was physical before K(g,g') was installed | Bare installation of the link alone does not replay that old lower. Use the selected-copy route above, or another actual activation; do not invoke a future ordinary admission that did not occur. |

For each finite set of cuts these arguments apply separately to every v_i.
Same heads, shared source or gamma equality do not collapse retained lineage.
If an actual parent/copy pair qualifies for intrusion, both sides transfer and
the merged Cartesian replay runs (`candidate_intrusion.rs:487–515,553–608`).
Fresh-bound restoration also explicitly drives replay
(`candidate_extrusion.rs:662–763`). These alternatives remain required when
reached, without assuming they occur in every history or equating unqualified
pairs to repair a missing diagram.

## 5. Completion boundary and precise unsupported premise

Replay with no separate provenance transfers children to the enclosing typed
queue; Queued leaves completion with that owner
(`candidate_context.rs:3281–3344`). enqueue_task appends to the back
(`lib.rs:12884–12914`). Function child dispatch can put its children at the
front (`12701–12724`). The drain transports and executes context before Effect
dispatch, settles qualified intrusion when the queue empties, completes
diagnostics, acknowledges replay children, then returns
(`12283–12368,12380–12404,12630–12692`). This covers emitted descendants on
successful return. It cannot create comparisons never emitted.

Structural Value dispatch runs extrusion synchronously, then appends the
rewritten Value comparison (`lib.rs:12469–12512`). There is no drain inside
the extrusion Work loop. Therefore the following **conditional native queue
order** is permitted by these owners:

```text
before extrusion returns:  [pending original x<=A(v), remaining siblings]
after rewritten enqueue:  [pending original x<=A(v), siblings, rewritten Value]
original cut later emits: [siblings, rewritten Value, member/cut or tail task]
```

The rewritten Value can dispatch before that newly emitted effect task and
its gamma-link descendants. This shows no universal per-dispatch internal
effect-completion barrier at these owners. It does not authenticate the full
source interface/levels making that queue, a semantically dependent use that
observes an incomplete consequence, or incorrect final acceptance. Source
actions advance after their operation returns
(`candidate_source.rs:827–874`); a completed source action/drain cannot be used
to preserve an ordinary pending child into the next action.

The exact remaining owner premise is now separated into two parts:

1. **Incoming source disposition:** in an authentic source history where the
   original downstream x-to-cut registration misses the gamma scan and x
   genuinely remaps, identify the actual Support/view ancestor and receiving
   owner that admits each later M(w,k) directly to x'. For every reached
   IncomingAllowance path, retain its original source/cut/tail and map key;
   establish its original counterpart or exhibit why all reached original,
   selected-copy, gamma-link, upper-admission, qualified-equality and
   fresh-restoration routes fail to supply the required consequence. The
   reused-upstream case above has a counterpart; remapped upstream/current
   stored pairs are unresolved.
2. **Exact checking/discharge before dependent completion:** establish that
   those actual routes execute or validly discharge each required transported
   member/cut consequence, with its ordered contexts, source sets and map
   ancestry, before any dependent result is reused as complete. In an open
   source view, original-link M(w,k) and selected-copy M(w_e,k) cannot simply
   be exchanged. A physical lower on g' also does not certify checking of an
   already stored g' upper. Typed-drain return proves only emitted completion;
   rewritten Value dispatch supplies no stronger pre-use barrier.

No inspected constructor establishes these two parts universally, and no
authentic history excluding all rescue routes is derived. This is the stop:
the result neither proves that some source ordering loses a required effect
nor proves that every source ordering avoids that loss.

The existing proof-economy audit classified necessary activation as A/B and
reconstruction of activation from stored evidence alone as D. This packet
changes the investigated owner from fabricated atoms to authentic Support,
member mapping and incoming cuts; it establishes the bounded cases above.
It does not turn the unchanged universal premise into progress merely by
reclassification. Before another equivalent proof variant, the primary should
obtain one exact source disposition at these construction/completion owners.
No additional semantic relation, source restriction or production mechanism
is proposed.

## 6. Checks, dependencies and resource report

Static method: focused constructor/consumer, bound/fiber, map and queue reads.
Commands used: bounded cat, sed, rg, nl, wc and sha256sum; leased-path creation
with apply_patch; note-only whitespace/newline and dependency recheck below.
Some initial combined reads exceeded capture limits; decisive cited ranges
were read in focused chunks. No exhaustive source reachability census is
claimed. No Cargo, build, test, executable probe, benchmark, seed/range,
mutation, Git command, delegation, interactive question or compiler/test/
shared-record edit ran. No independent executable oracle exists; native code
is the operational subject, and source/semantic adequacy is explicitly open.

One static leaf, twenty-minute wall cap, no heavyweight process. Exact CPU,
peak RAM and elapsed time were not measured. Requested ordinary routing:
prover, gpt-6.1-sol/high; observed effective runtime model/effort metadata:
unknown. The role registration and unpinned model/effort fields were read;
they do not establish hot reload or effective runtime routing. No Astra.
Only this lease was written. Shared task changes are primary-owned locators,
not theorem premises. No changed native dependency hash was observed.

Unverified: complete accepted-source schedule/levels/incidence and all-source
Catch admission/eligibility/coverage; nonidentity live-context equivalence and
termination; all-current copied-pair activation; all-history memo completion,
dependent publication, suspension/abnormal paths; full capture/freshening and
complete Call/hygiene/soundness/principality correspondence.

One next action: authenticate one source-owned IncomingAllowance route with a
genuinely remapped upstream source, from S(w)'s construction through its exact
M(w,k) receiver and first dependent rewritten-Value completion, recording all
original/copy/gamma alternatives and exact map/fiber identities. A named
missing producer or completion premise is a sufficient bounded outcome; do
not substitute another native Contribution trace.

SHA-256 frozen dependencies follow; bare filenames are not used.

```text
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e  crates/yu-solver/src/candidate_intrusion.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b  crates/yu-solver/src/candidate_source.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
1781952afd258038345ba2dbe5a3c425bc193a04c7d77c72b2eb52a636466822  notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md
00e9691a3ecb92029f15fc6bb0a0c79f906287d2c6517e672e33ab7c7f1c6cd5  notes/theory/2026-10-15-pending-symbolic-cut-continuation-application.md
bd377f5a891d94f40bb026408fbf1ca824695b6fd6a08aa3a08f667d3aa177ae  notes/progress/2026-10-15-pending-symbolic-cut-continuation-falsifier.md
1e6d42dc59ca4e82c62fa78fd4bcb6188f72b35aac964095883fcf03bb5beaf6  notes/progress/2026-10-15-copied-symbolic-cut-continuation-owner-audit.md
1ef831a58bfa8bbca8e4d3e71184cae229c0fee36f671826cb4c5ff9b8e68727  notes/progress/2026-10-15-pending-remapped-source-reachability.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5  rules/orchestration-budget.md
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810  /home/momota1029/.codex/skills/yulang-proofs/SKILL.md
```

## Commit packet

- Exact leased path: `notes/theory/2026-10-15-annotation-member-copied-tail-lineage.md`.
- Baseline SHA: primary checkpoint `0a8e90aec`; native source
  `d8a6209c1dc181858948c4d811259aa20683d64e`.
- Changed dependency hashes: none observed for native/authority/prior paired
  notes; source-reachability note's frozen hash is listed, with its subsequent
  bounded review conveyed by the primary. No Git-baseline equality claimed.
- Claim/review status: reviewed bounded derivation/obstruction; fresh M2
  `compiler_referee` found no findings on the exact frozen SHA-256 above.
  Primary adjudication is recorded in shared task records. No parent closure.
- Checks already run: cited owner/map/fiber/queue static trace, SHA-256 freeze
  and note whitespace/newline checks; no executable verification.
- Proposed one-line message: `research: derive authentic annotation-member copied-tail lineage`.
- Shared-record deltas for primary/curator: record exact closed/open member
  transport distinction, same-key S/M/cut sharing, the reused-upstream incoming
  cut counterpart, and the remaining remapped-upstream/context/pre-completion
  premise. Preserve original H1/H2/U OPEN, H3/P disabled and production/F5
  boundaries. No shared task/index/theory-status/authority file was edited.

Writes stop at handoff.
