# Runtime raw continuation: constructor-to-template correspondence

Date: 2026-10-16
Status: independently reviewed constructor characterization and implemented-path raw-Resume bridge; original full-domain Resume parent OPEN
Owner: primary-assigned prover leaf; no delegation or certification
Lease: this file only
Baseline: `d40452204ff4e5b8547287a46f6f27af29781e16`

Independent review: `ordinary_carrier_semantic` accepted the original conditional
constructor derivation at `88df21f55a40be18ab24f78eff0f7af12c42d65301f02994ae992a0588eb5b77`.
`runtime_semantic_review` accepted the final actual-source §§9–12 bridge at
`51784be9c242f185b66081a327cfc8503d12de0c287d5c5befbbc1ff99726ff3`,
including arena ownership, map/active-bit equivalence, reuse and recapture.
The source-typing/transport and general-visibility/full-source premises remain
explicit. The historical pending-cache-capture residual is addressed by the
later independently CLEAN delimiter corollary in §6.1 below; the primary
accepts that current-public-runtime pending-write branch as discharged.
M3 code, contract and resource deltas are clean;
the primary's final raw-Resume package check passed 82 tests.

## 1. Frozen objective, authority and dependency boundary

The original objective is reusable, shallow raw continuation execution with
the original source scopes, binders, complete suffix, current shared cells,
typed views and event lineage. It includes owners whose return delimiter lies
outside the capture bound, owners still active below a resumer, forwarded
handlers, crossed computation views, nested completion and repeated capture.
There is no one-use restriction, receiver revival, recursive demand of a
returned latent value, or omission of inconvenient source suffixes.

Governing source:

- `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§13–17;
  §§18,20–21,24 preserve result forwarding, joint request witnesses, source
  parameter roles and the distinction between receiver role and entry demand.
- `notes/design/2026-10-02-source-call-scheduling-choice.md` §§1–2, including
  the October 15 reaffirmation: obtain callee, delay the whole argument,
  then perform its declared entry demand inside the invocation.
- `notes/design/2026-10-02-typed-source-owner-realization.md` §§2–4,6:
  saved context constructors, containing owner, owned/borrowed completion,
  historical evidence exclusion and outside shallow selection.
- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` §5:
  complete shallow image and fresh source-prescribed forwarding wrappers.

The latter two are reviewed decorated-source packages, not a newly adopted
compiler architecture or full arbitrary-source realization theorem. This
note derives requirements of their selected owner/control behavior; it does
not turn their remaining premises into facts.

Frozen non-HEAD input SHA-256:

| Dependency | SHA-256 |
|---|---|
| `tools/inference-playground/src/runtime/machine.rs` | `d1d0380bf6b2e70996777829c6e4b8643921d7656fa4cb093b962e26bb5e6a92` |
| `tools/inference-playground/src/runtime/receiving.rs` | `4c8d23733ec6b8aac3a73875051f79fce6914fcc0e4d56fc90c239bad86bc22b` |
| `tools/inference-playground/src/runtime/program.rs` | `984efecac3257976b87c24c851f2f3d1e5a5a762bfcaaa92b572ac75000591ea` |
| `notes/theory/2026-10-15-runtime-receiving-view-construction.md` | `f06651865fbb666daab3349fbf4a946daa59d5877ba8b87798bba5463655feb8` |

The primary notified this lane that the last note's optimized `local_grant`
converse is under repair: the executing view's receipt need not be the
candidate owner's authentic receipt for that same view. Neither that converse
nor current query completeness is a premise below. Visibility is the original
joint existential receipt/typed-flow/Observe relation at the candidate. A
later receiving repair invalidates only conclusions actually using its query,
not this pinned frame-constructor analysis.

## 2. Statement and hypotheses, before derivation

Fix one source descriptor graph Ω, one original assignment ν, one finite
reachable source execution prefix and a request event q in that prefix. Fix
the selected shallow handler occurrence h and its actual capture bound B.
Keep all request-local binders, payload/response types, answer type, typed
views, profiles and dependent K,D under their original joint witness. Nothing
below chooses their marginal witnesses independently. Let S be the ordered
pending frames strictly between the response hole and B, in next-return-first
order. Let a be any response admitted by that original request typing, and C
any related current configuration reached by legal intervening source work.

The required conclusion is: capture constructs exactly the finite context

```text
T ::= Hole | Bind(T,F) | Owner(i,u,T)
    | ForwardHandler(H,ownerSlot,T) | View(v,p,T)
```

whose execution on a in C simulates the original raw suffix, with fresh local
control, shared current cells, correctly scoped resolved executable owners,
fresh forwarding handlers and computation executions, unchanged historical
evidence, and one root return to the current resumer. Inner completions feed
their parent suffix. Capture includes no code beyond B and no wrapper for h.
The conclusion quantifies over every finite legal reuse/recapture history;
an infinite execution is observed at all its finite prefixes.

This pass distinguishes three claims:

1. **Actual bounded constructor characterization:** for every finite request
   propagation prefix of the pinned machine, its saved vector is exactly the
   next-return-first sequence of popped frames, with its original fields and
   no frames below the reached candidate. This includes all current `Frame`
   variants. It does not establish a template consumer that does not exist.
2. **Conditional extraction and entry/completion derivation:** if constructors
   retain the missing source-owned descriptors/slots and consumers implement
   the local rules in §§4–6, the displayed conclusion follows for those
   frames by structural induction. These are explicit implementation bridge
   premises, not assumed observations about the pinned machine.
3. **Original actual source-to-runtime theorem:** OPEN. The pinned machine
   rejects bound continuation arms and has no raw-resume executable or entry,
   so it cannot presently satisfy claim 2's premises or the full objective.

Shared hypotheses for claim 2 are source typing/operation compatibility of
the actual response and arm, source-faithful ordinary instruction transitions,
valid original annotation/view elaboration, fresh identity allocation or
explicit safe failure, and related stores. They do not assume visibility from
saved reachability, replay old activity, or assume the current Grant query is
complete. Generic operations, symbolic families, arbitrary higher-order view
transport and source forms absent from `Instruction` still require their own
actual constructors and consumers. This is an omission of this local proof's
coverage, not a restriction of the original parent source domain.

## 3. Actual producer/consumer correspondence

All line locators here refer to the machine hash in §1.

| Pending frame | Actual construction | Actual completion represented by F or scope |
|---|---|---|
| `Callee` | `evaluate` Apply, 421–430 | `return_value`, 535–667: delay entire argument; select callable entry; allocate invocation; bind retained carrier or force once before body |
| `ValueEntry` | closure Value invocation, 569–574 | 679–696: bind returned value without executing it again, then evaluate body in original closure environment |
| `OperationPayload` | operation Value entry, 648–653 | 529–532: construct the declared operation carrier from the returned payload |
| `OperationResultConsumer` | operation Call, 643–646, below that Call's receiver delimiter | 533: execute the declared returned carrier after that invocation completes, in the containing caller's owner scope |
| `Local` | `begin_local`, 1080–1096 | 698–723: write the retained cell, extend the original binder/environment if needed, continue the original block cursor |
| `Condition` | If, 435–443; next test, 748–757 | 724–765: inspect Boolean, choose original arm/else, possibly install `DiscardToUnit` |
| `DiscardToUnit` | successful no-else branch, 738–742 | 534: discard branch result and construct source Unit |
| `GlobalRead` | empty module Name demand, 384–398 | 776–788: publish in original cell, release its pending marker, perform original name consumption |
| `Root` | `begin_root`, 1003–1033 | 767–774: publish original definition cell, release marker, continue original module root cursor |
| `ReceiverReturn` | closure Call, 561–566; operation Call, 635–646 | 669–677: end that invocation and return its value to the next pending frame |
| `CatchReturn` | Catch, 456–473, with exact installer owner | 490–528: leave that handler, bind value pattern, run its value arm outside it; otherwise pass value onward |
| `RootCompReturn` | explicit formal execution, 1054–1062 | 485–488: end that exact computation execution and perform its declared result-view completion |

`RuntimeProgram::from_hir` retains original source `SourceSite`, original
parameter/local/catch binder IDs, source child labels and original arm code.
It builds finite shared code and preserves recursive references as binders.
`Frame` environments are arena indices, not copied lexical value maps.
`Environment::binder` points to cells; `bind`/`extend` at 1147–1158 append links.
Thus saving these fields retains source lexical resolution and cell identity.
It neither captures mutable cell contents nor schedules expression execution.

`execute(Request)` at 1115–1129 allocates q once, records its observations
from the current executing views, and initializes an empty suffix.
`propagate_request` examines an installed Catch before removing it (835–931).
When it commits forwarding, it pops exactly one frame, converts that frame
at 947–970 and appends it at 971. A crossed receiver ends its current active
occurrence; a crossed view ends its execution; an unmatched Catch retains its
descriptor/environment and original installation. Ordinary fields are moved
unchanged. No transition in that loop modifies q, its payload, event or prior
observations. Induction on the number of such transitions proves claim 1.

On successful selection the pinned consumer pops h, calls `abandon_suffix`
and runs the discard-only arm. It requires a wildcard continuation at 884.
On unhandled termination it saves the vector and observations at 932–944.
Neither path constructs a callable continuation. Stored fields therefore
establish capture order only; they establish no activation, replay or source
simulation for a later raw call.

## 4. Extraction by the actual frame nesting

The construction owners must retain the following facts when they know them:

- Each ordinary Call entry records a source invocation descriptor i, fresh
  occurrence u, the previous executable-owner slot and its matching return.
  For closures these are known from the selected `ExecutableValue::Closure`,
  its original value source and Apply site. For operation Calls they are known
  from the declaration, selected entry and Apply site. Re-entering i identifies
  the saved span; it does not execute the already completed argument/entry.
- Every executing span has an explicit executable-owner binding. A capture
  can therefore retain its containing i,u even if `ReceiverReturn(u)` lies
  below B. ModuleRun is the distinguished ambient owner, not invocation zero;
  it requires no invented callback entry or fresh receiver.
- Each pending scope records its source parent/completion relationship. Each
  forwarded handler retains a slot referring to that executable owner. Each
  crossed view retains its original typed packet and its separate computation
  execution/completion information.

These facts already exist at entry; retaining them avoids reconstructing a
callee from labels, historical IDs, surrounding handler spelling or a later
successful evidence query. The pinned `ReceiverBoundary` keeps only u, and
`ExecutableValue`/active receiver IDs do not provide this full retained span
record. `SavedFrame::Ordinary(RootCompReturn)` also has no re-entry consumer.

Given those retained facts, fold the next-return-first vector from `T=Hole`:

```text
ordinary F                  : T := Bind(T,F)
crossed ReceiverReturn(i,u) : T := Owner(i,u,T)
forwarded Catch(H,slot)     : T := ForwardHandler(H,slot,T)
crossed RootCompReturn(v,p): T := View(v,p,T)
```

After the last frame strictly inside B, enclose T in its still-containing
invocation `Owner(i,u,T)` when that invocation's matching return was not
crossed. This records attribution only, with completion to the capture root;
it does not append that invocation's remaining outside code. For ModuleRun,
bind the ambient distinguished slot without inventing an invocation. The
selected handler contributes no `ForwardHandler` node. Stack below B remains
the current outer continuation and is not folded into T.

Proof of exact nesting is induction on popped frames. The induction invariant
is that T denotes the original removed inner context from its response hole
to the current search position. An ordinary pending return consumes the
inner result and then runs its retained suffix, hence `Bind(T,F)`. A receiver
return closes the invocation containing exactly that inner context, hence
`Owner(i,u,T)`. Catch forwarding encloses that body's context in the ordinary
shallow image, hence `ForwardHandler`; a view return similarly delimits the
computation context, hence `View`. Each new node encloses the entire previous
T, so the induction preserves all nesting and response order. The final
containing owner follows from its actual constructor scope at B. Inspecting
that owner does not inspect or add code below B. These cases exhaust the
actual frame enum in §3.

For example, frames for the remaining g suffix, g return, remaining f suffix,
and f return produce

```text
Owner(f,uf, Bind(Owner(g,ug,Kg), Ff)).
```

If f's return is outside B, the final containing-owner step produces the
same displayed attribution while Ff contains only the suffix inside B.
Stopping at `Owner(g,ug,Kg)` loses Ff. Appending f's whole body or outside
return continuation adds code not captured by source. Both mutations fail
the induction invariant. The pinned flat vector's ordering suffices for this
shape derivation; it does not supply the missing descriptors or final scope.

## 5. One entry/completion simulation, conditional on retained constructors

Interpret a template with a fresh local pending-frame stack and control
environment ρ, a current executable-owner register o, a current computation
view context V and the current store σ. Keep the resumer continuation R only
in one separate root `ResumeReturn(R)`. Allocate no σ snapshot.

**Hole.** Supply the admitted response a as the return to its immediate
pending frame. This replaces the result of the original request, not its
payload or answer type. No argument expression is reexecuted here.

**Bind(T,F).** Push the completion that executes the exact original F under
its retained lexical links; enter T. On return x,σ′, pop that completion and
run F(x,σ′). Any request from T retains F; any request from F retains its
remaining source suffix. F does not complete the root until its parent does.
The table in §3 gives F's complete meaning, including Callee entry forcing,
operation result consumption, conditional cursors and pending cell writes.

**Owner(i,u,T).** Save o. If exact u is active in C, bind o=u and record
`Borrowed(u)` without adding or removing an activation. Otherwise allocate
fresh u′ with source descriptor i, bind o=u′, add its active occurrence and
record `Owned(u′)`. Enter T with this local completion. On child return,
Borrowed leaves u active; Owned ends exactly u′; both restore the saved o and
pass the child result to the parent. A new actual Call made by F still uses
its ordinary fresh invocation/entry. Saved-span re-entry does not replay that
Call's old boundary entry or force an argument already consumed before q.

In particular, Active(u,C) is membership of the exact live occurrence, not
`active_receivers.last()==u`. A still-running original owner can be below the
new resumer. The register o supplies its executable attribution while that
resumer remains active. The pinned `current_execution_owner` at 815–820,
handler validation at 825–830, receipt creation at 1045–1047 and receiving
query's last-receiver guard are valid only for their current ordinary nesting
and are not a correct implementation of this general resumed case. Their
future correspondence must use explicit o plus exact activity. Merely pushing
the borrowed ID again makes its original completion ambiguous and is not the
borrow rule.

**ForwardHandler(H,slot,T).** Resolve slot in the current lexical control
environment, allocate a fresh handler occurrence under that owner, push its
ordinary shallow completion and enter T. On return, remove that exact handler
before running its actual value arm with the retained typed environment.
Only the value arm's result continues the parent. Requests retain the parent
through ordinary bind. A forwarded request rebuilds this source-prescribed
wrapper; selecting this fresh handler excludes it from its newly selected
raw suffix. The historical installation ID is lineage, never the new ID.
Reusing old `CatchReturn.installation` verbatim fails freshness and ownership.

**View(v,p,T).** Enter a fresh computation execution with original typed
view v and packet/provenance p, nested inside the resumer's ambient V; push
its exact completion and enter T. On normal completion or search unwind,
end only this execution. The existing source-designated result projection
still runs: for the pinned RootComp consumer that ends execution and returns
a ground result view (485–488). A fresh execution occurrence is distinct from
the historical receipt and from boundary entry. If the chosen representation
uses a separate token, it must allocate a new one; copying an old token may
not reactivate it. Event observation allocates fresh observations for new q
from the entire current V. Owner entry never replaces V, even when borrowed.

For each constructor, these steps are the corresponding decorated-source
entry and completion with administrative records made explicit. The child
induction hypothesis supplies the same result/request and current σ′. Its
local pending frame supplies exactly the parent continuation described above.
Thus structural induction proves one entry/completion simulation for any
finite T under the stated implementation premises. Only the separate root
frame can return to R. For the example in §4 this closes g, runs Ff, closes f,
then reaches R; a request in Ff is observed before R.

No case modifies a retained boundary receiver, old receipt owner, original
view, request event/origin, joint ν or symbolic K,D. New Name consumption
uses the existing source receipt rule under o, adding a fresh receipt rather
than renaming an old one. Dead original receivers stay dead even when a fresh
execution shares i. This establishes the control/evidence separation needed
for hygiene, conditional on the original actual visibility/transport bridge;
it does not establish that bridge by saving a template.

## 6. Reuse, recapture and current cells

Each invocation of T gets its own ρ and pending completions. Completed child
nodes are absent from a later remaining context; capture starts at the newly
yielded response hole and retains only unfinished F/owner/view/handler
completions. It saves the currently resolved owner occurrence and source
descriptor, then later resolves activity again. A saved Borrowed/Owned mode
from a previous use is never replayed as a pop instruction. This is the same
constructor induction on the current execution's pending frames, so finite
reuse histories follow by induction on source steps and resume calls. It
does not follow from cloning historical `ReceiverReturn` frames.

All retained environments, Local cells, global cells and typed values remain
the original references. Local completion writes the same cell using the
current result; a later read sees its current contents. Appending fresh cells
for genuinely executed later source bind operations remains ordinary source
behavior. Copying a saved cell's old contents into a new arena is not this
semantics. Closure/environment cycles remain finite arena references.

Historical pre-initializer-boundary residual (current applicability in §6.1):
there is an additional OPEN runtime obligation for `GlobalRead`/`Root` pending
materialization markers. The receiving note §9.5 proves uniqueness of W(c)
only for a machine with no Resume that duplicates a pending write owner.
Reusable raw control can retain and re-enter that write continuation, while
other source work reads the same live global cell. The former proof therefore
does not establish marker ownership, recursive-initialization rejection or
cache publication for this extension. Blindly restoring a marker snapshot,
blindly clearing every marker, or treating retained control as abandoned all
lack the required current-store correspondence. The owning constructors are
Name/`begin_root`, the captured Root/GlobalRead F, `abandon_suffix`, and their
completion consumers.

The minimal operational requirement is more precise than a generic cache
obligation. Let W_j(c) be one current pending execution of the retained write
continuation for c. The reusable template is a recipe; it must not itself be
confused with every W_j it can instantiate. Creation, suspension, re-entry,
completion and abandonment must retain enough ownership to distinguish all
unfinished W_j that the source protocol counts as pending. Completing or
abandoning W_j changes only that occurrence's pending claim. If a different
blocking W_k(c) remains and c is empty, a later Name must not start a second
initializer merely because W_j ended. Conversely a template that has no
blocking execution may not leave a stale marker solely because it could be
called again. Which suspended claims block a new Name must come from the
existing source initialization owner; it is not selected by this note.

Here is the minimal operational discriminator for the current unconditional
Boolean removal. Assume two unfinished instantiated writes W_1(c),W_2(c),
with c empty. W_1 is outside a reached selected capture bound and W_2 is
inside its suffix. Such multiplicity must be considered once a reusable T
containing `GlobalRead(c)` can be invoked while an earlier use remains
unfinished. Abandon the suffix containing W_2. The pinned `abandon_suffix`
removes c from the set, although W_1 has not completed or been abandoned.
A subsequent empty-cell Name can then successfully insert c and start a new
initializer under `GlobalRead`; the old guard would have rejected that start
with W_1 still pending. A one-owner state and this two-owner state have the
same old Boolean representation before abandonment but require different
post-abandonment bookkeeping. No rule that unconditionally erases their
shared Boolean can preserve both owner states.

This is a conditional operational countertrace against importing the old
uniqueness proof, not an authenticated current Yulang source counterexample:
the current machine has no Resume, and this pass does not prove a particular
source can construct the nested two-use scheduling. It supplies the exact
falsifier for the source-owner lane: authenticate that scheduling or establish
the source-derived invariant that prevents it, without restricting raw use.
Even a serialized execution needs distinct knowledge of a retained recipe
versus its live pending work. A scalar count could handle some multiplicities;
ownership attribution is still required so that only the right completion or
abandonment decrements it. This derivation prescribes no data structure.

Publication remains the original F operation on the current shared cell:
the pinned `GlobalRead`/`Root` completions write their actual result. Do not
silently skip a later resumed write, restore an earlier cached value, or assume
every use produces an equal value. A proof that publication is idempotent or
that a previously populated cell suppresses a pending F would need the actual
source memoization law and store/response hypotheses; none is supplied here.
The minimal implementation handoff is therefore per-occurrence pending-work
ownership plus original-source publication/recursive-demand correspondence,
including the stated two-owner discriminator. The primary retains the choice
of protocol after that source-owner check. The control theorem's store-related
premise includes that missing evidence when such a frame is present. These
frames remain in the original parent domain.

### 6.1 Current-runtime delimiter corollary

The later [outward-order theorem §2 and corollary §8](2026-10-16-initialization-outward-order-current-runtime.md)
provide actual all-path constructional unreachability for selected reusable
templates containing Root, GlobalRead or ExpressionReturn. This applies to all
current public from_hir/start traces, including raw Resume, nested demands and
budget pauses, rather than relying on a new source purity restriction.

No such template can reproduce the pending W_j(c) assumed by the historical
two-owner discriminator. Entry reconstructs no demand frame indirectly;
selected discard likewise cannot clear one. Normal initializer completion
below a handler and future new Name demands are distinct operations. Captured
cache references and current shared cells remain supported. Defensive guards
stay in place; no new cache protocol or A/B law is selected.

The corollary's fresh application review by `runtime_semantic_review` is CLEAN
at parent-note SHA-256 `5ea071b59f135348379ece891071d54c8c8e5c61b1da7c303cef3e364d150f41`
and corollary producer `5b0a98d3...ac91b4`. The primary closes exactly this
current-public-runtime pending-publication capture/duplication obligation.
General source-to-runtime materialization, initialization entry timing/full
traces, unimplemented contexts and future global consumers remain OPEN. Earlier
cache residuals in this baseline's handoff tables are historical within that
scope; no whole-source or full-domain Resume theorem is thereby declared proved.

## 7. Decisive obstruction and smallest next evidence

The missing premise is localized: **actual invocation constructors do not
retain i/parent executable-owner scopes, and no actual raw-continuation
entry/completion consumer realizes the derived fold and local rules.**
It is an A correctness/B intended-behavior obligation with a D component:
the owner/descriptor fact is known by Call entry and discarded before capture.
Retain that fact there rather than adding an inverse reconstruction theorem.
This pass is one constructor-directed attempt, not a third restatement of an
unchanged premise; it supplies exact owners and a falsifiable implementation
handoff. It does not promote the parent gate.

Smallest provisional evidence is a reversible source-owned template slice:
retain invocation descriptors and lexical executable-owner bindings; convert
actual capture frames with the fold; implement root/inner completion and
owned/borrowed/View/forwarding entry; expose a typed raw continuation through
the existing Call path, whose Value entry delays and forces the whole supplied
response expression exactly once before feeding Hole. Do not infer demand
from a response value's executable tag. Keep all dependent production gates
OPEN until the actual constructor/consumer proof and independent review.

Primary-owned focused verification should discriminate: a containing owner
whose delimiter is outside B; a borrowed owner below a resumer; dead-owner
fresh occurrence without boundary revival; g completion followed by f's
effectful suffix; effectful response expression forced once without recursive
latent forcing; forwarded handler value-arm completion; ambient plus crossed
view observation; second use after a shared-cell change; recapture after an
inner child completed; and a captured GlobalRead/Root marker lifecycle. These
are proposed checks, not executed tests or evidence of implementation.

No further semantic decision is inferred necessary for the selected owner,
entry or shallow rules. Missing source constructors for other original source
forms and the cache protocol remain explicit implementation/proof owners.

## 8. Handoff, resources and commit packet

Method: one bounded static construction/consumer pass and structural induction.
Commands: bounded `cat`, `rg`, `nl`/`sed`, read-only `git status --short` and
`git rev-parse HEAD`, SHA-256 dependency checks; no builds/tests/probes/network
or Git mutations. Runtime frame enum and all its construction/completion/
capture sites were inspected. No compiler or test file was written. Primary
retains verification and independent review ownership. No subprocess-heavy
calculation or measurement samples; no delegation. Requested normal Sol/high;
effective runtime model/effort metadata unavailable, therefore unknown.

Final dependency audit observed unrelated HEAD movement to
`f75299ea4b81dcae4a2807abf33a8ea25d36bf58`. The machine became
`bac47d83a5f928bb30cb73df830048f9f57d9041fbc2cac2bc965dde10a7cdc8`:
reverting only the newly added `Hash` derive on `ExecutionOwner` in memory
reproduced the exact §1 machine hash. Thus its analyzed constructor/consumer
text and line locators are unchanged. The receiving file became
`dcd40e9ff0eae587339825d5e434d627269b6f56e2aa61990230fd5dd7af0fe1`;
its new query implementation was not reviewed or used to strengthen this
proof. Program and receiving-note hashes remained as in §1. No trailing
whitespace was found by a direct line scan; `git diff --no-index --check`
against `/dev/null` emitted no whitespace diagnostics (exit 1 reflects the
new-file difference). These checks execute no runtime model.

Review status: producer derivation only; no independent review or theorem
certification. Source typing, full visibility, arbitrary view transport,
unrepresented source forms and marker lifecycle are not proved here. Next
action: primary assigns the smallest provisional constructor/consumer slice
in §7 and independent review of this frozen derivation; then prove its actual
emitted records and transitions against §§4–6, rather than repeating the
abstract induction with the same absent runtime premise.

Commit packet:

- Exact leased path: `notes/theory/2026-10-16-runtime-resume-template-correspondence.md`.
- Baseline SHA: `d40452204ff4e5b8547287a46f6f27af29781e16`; non-HEAD input
  hashes in §1; do not substitute a later receiving repair silently.
- Claim class: unreviewed bounded constructor characterization and conditional
  extraction/entry/completion derivation; actual raw-resume bridge OPEN.
- Checks already run: static source-owner tracing and initial dependency hashes;
  final file/dependency hashes and whitespace check reported by the leaf handoff.
- Proposed checkpoint: `research: derive runtime raw continuation template requirements`.
- Shared-record deltas left for primary/curator: record exact missing retained
  owner descriptors/explicit executable owner and absent resume consumer;
  retain raw Resume, complete Call, full hygiene, soundness/principality and
  production gates OPEN; add separate GlobalRead/Root marker bridge; do not
  import the receiving-query converse currently under repair.

## 9. Actual-source bridge preparation, not implementation evidence

New packet baseline: `46bb232a4cfbdab20fd28026f0893da41d875bc3`.
The primary reports that independent `compiler_referee` review accepted the
original artifact hash
`88df21f55a40be18ab24f78eff0f7af12c42d65301f02994ae992a0588eb5b77`
without findings. That review covers §§1–8 at that hash, not this added section
or any later runtime implementation. The primary has consumed the conditional
result into an authorized provisional runtime slice. The original Resume
parent remains OPEN. The receiving proof's later review is separately
primary-owned; this section does not import an uninspected repaired query.

The matrix below freezes the source obligations before reading the new
implementation. Constructor/consumer names identify responsibilities, not
assertions that the expected code exists. All rows await a complete frozen
runtime hash set and actual-source inspection. Expected dependency paths are
`tools/inference-playground/src/runtime/{machine,receiving,program,mod}.rs`,
an optional continuation module, and `tests/runtime_resume.rs` under the same
tool. Tests may be read for their claimed coverage but are not theorem
premises and will not be run by this proof leaf.

| Obligation | Source construction fact to retain | Actual consumer evidence required | Discriminator / omitted-premise check |
|---|---|---|---|
| Invocation descriptor | Original Call selects actual callee source descriptor i, fresh occurrence u, entry role and prior executable owner | Saved owner refers to that exact descriptor; re-entry resumes its suffix without replaying original entry | Closure and operation Calls both covered; no reconstruction from callee name, body shape or type equality |
| Containing owner | Span at selected bound retains i,u even when matching receiver return lies outside the bound | Final owner wrapper attributes only the inside context and completes at the raw root | No outside body/suffix code appended; containing owner's old return not executed by borrowed completion |
| Exact frame fold | Actual unwind retains next-return-first pending code, source cursor, lexical environment and relevant completion records | Fold implements the four cases in §4 and final containing scope; every frame enum variant is accounted for | No implicit reverse of ordinary suffix order; selected handler absent |
| Explicit executable owner | Every source transition has lexical owner o separate from active occurrence membership | Handler installation/validation, fresh receipts, nested Call return and capture all read/restore o | Borrowed u remains below a live resumer in the active list; `.last()` cannot substitute for o |
| Borrowed entry/completion | Saved u is tested by exact current activity, with a local completion mode | Active case introduces no duplicate activation and never ends u; restores previous o and continues parent | Original invocation can complete later through its own return; no stale completion mode reused |
| Fresh entry/completion | Dead saved u retains source i but no authority to reactivate u | Allocate fresh u′, keep original evidence unchanged, end exactly u′ at its matching completion | Same descriptor never implies same activation or renewed old boundary |
| Response Call entry | Applying k receives the entire response expression as an inert delay | Ordinary Value entry forces once inside its fresh invocation, then supplies result to Hole | Effectful argument prefix is not run before entry; executable/latent returned result is not recursively forced |
| Inner versus root return | Each owner/bind/view/handler completion retains its local parent | Inner completion passes value/current state to its parent; one distinct root returns to current resumer | g finishes, then f's effectful suffix runs, then root; no inner direct return to resumer |
| Forwarding handler | Actual forwarding retains original descriptor/environment and resolved owner slot | Fresh handler ID; full shallow return/value-arm computation outside that handler; parent retained through arm requests | No old installation reactivated; selected shallow handler never automatically restored |
| View re-entry | Crossed computation delimiter retains original view and receipt/typed packet independently of executable owner | Enter fresh execution scope in ambient current view context; exact completion/unwind; later event gets fresh Observe | Re-entry must not fabricate `Receive(new owner,old view)` or call boundary entry; owner resolution must not rewrite old receipt |
| Fresh source receipt | Actual executed Name/boundary entry retains source slot and current lexical owner | Only that source action adds its receipt; visibility joins authentic current evidence under original witness | A saved View packet is not a newly executed Name; observation's receipt is not the only possible authentic receipt for the same view |
| Current shared cells | Template retains original arena/env/cell references | Each F reads/writes current cells; only newly executed source binds allocate new cells | No cell or store snapshots; subsequent use observes intervening source writes |
| Recapture | Current unfinished local pending frames retain current resolved owners and completion parents | New template starts at the new Hole, omits completed work, resolves activity afresh on its next use | Saved Borrowed/Owned actions are not replayed as stale pops; forwarding/View nesting preserved |
| Bound continuation exposure | Successful source arm selection retains the actual raw template with original response/answer contract | Binder receives reusable callable that uses ordinary Call and preserved typed value flow | Payload, raw suffix, response binder and event-dependent evidence stay jointly associated; no marginal witness choices |
| Cache-bearing control | Root/GlobalRead identity and pending-work claims arise at actual initialization owners | Pending-work/publication/abandonment protocol must satisfy §6, or provisional execution explicitly reports unavailable | Provisional unavailability is a tool boundary only; no source theorem/domain narrowing and no parent closure |
| Failure/resource behavior | Identity allocation and input checks identify explicit failure before unsafe state publication | Failure is unavailable/private suspension with no completed false result or stale active-control exposure | No recovery/rollback theorem is inferred from storage alone; exact failure paths must be inspected |

For the View row the negative obligation is deliberate: restoring an old
executing computation scope is not a source read by a newly entered owner.
It can reuse the original packet/provenance for fresh event observation while
preserving authentic earlier receipts. A genuinely executed later Name may
add a fresh receipt under its actual lexical owner. Confusing these two
operations would supply authority not present in the selected source rules.

For cache-bearing templates the primary reports that the source-owner question
remains pending. An explicitly unavailable provisional path can provide bounded
runtime evidence for other control paths; it does not discharge the original
cache-bearing source case or transform that case into a forbidden program.
No inference about publication equality, memoization idempotence or allowed
continuation multiplicity is made here.

This preparation changes only the leased note. No new implementation has
been inspected or claimed conformant. Next evidence: primary supplies final
runtime hashes after implementer freeze, then the leaf traces each matrix row
through actual producers, transports, completions, unwind and re-entry paths
and records exactly which conditional premises became established source
facts and which remain OPEN.

## 10. Frozen first implementation: actual control correspondence

### 10.1 Inputs, claim and retained exclusions

This section uses the primary's first implementation freeze, read at HEAD
`419c801bd96447efadbc6a1994c9a2f20b2e9d0a`. The assignment baseline remains
`46bb232a4cfbdab20fd28026f0893da41d875bc3`; the following uncommitted file
hashes, not the moving branch name, select the implementation.

| Dependency under `tools/inference-playground/` | SHA-256 |
|---|---|
| `src/runtime/machine.rs` | `032894cac2c23d18532c9c0fe1b915008a874a221ab1354a160e6ff599a0267d` |
| `src/runtime/program.rs` | `b0d189ed051b0f38fb0a87a6379f9455105d9e5d88673fc8a84143a11349745b` |
| `src/runtime/receiving.rs` | `4aacabb8d7712157478ba632bf16668e99c35633553e3362d4e23f3839b5758a` |
| `src/runtime/continuation.rs` | `a18cb78e5a907b93868b2b51175e8fe7acef47834b82c07a8278a8d7a74ae281` |
| `src/runtime/mod.rs` | `4b6a0aab50459e673e7e54724db08adc1f9fc75b45e98b6831e8ee47af0b8aae` |
| `tests/runtime_resume.rs` | `f892173c928165ce65a57e31ee110613eb3226c1f22b0c18787b6fce235c9099` |
| `tests/runtime_receiving.rs` | `0a40a089c4a53f131a75221c97270713c9d42b664d847288334fce85a1dd8790` |

Claim class: **actual implemented-path source/operational derivation, submitted
for independent review**. It applies the already-reviewed conditional result
to real constructors and consumers; it is not a second supplied transition
model. The original §2 quantifiers and joint witness are unchanged. On the
currently implemented local source paths, with actual primitive payload and
response types, actual local positive visibility, original statically typed
arm/response and ordinary instruction interpretation, the machine's successful
capture, call, entry, return, forwarding and recapture steps realize that raw
source context. This includes arbitrary finite reuse histories on those paths,
containing owners outside the bound, borrowed owners below a resumer and fresh
owners for expired spans. Administrative entry steps may stutter with respect
to source computation; the response and original pending suffix are unchanged.

This is not a theorem that every original source execution is available in
the provisional tool. Cache-bearing capture explicitly stops with
`ContinuationMaterialization`; nonprimitive response/payload consumers, full
negative/inherited visibility, general symbolic-family transport and absent
source forms remain open in their original domains. Unknown evidence stops
execution rather than proving invisibility. Shared source typing/ordinary
semantics premises remain explicit: the primitive check is not a type checker
for arbitrary arm bodies or a proof of candidate inference. The original
full-domain Resume, complete Call, hygiene, soundness/principality and
production parents remain OPEN. No new source restriction follows.

### 10.2 Source constructors discharge the descriptor and extraction premises

`Machine` now holds `current_owner`, `invocations` and `controls` (38–40).
`InvocationDescriptor` stores the original Call and provider `SourceSite`
(61–64). `new_invocation` (886–901) allocates the monotone fresh occurrence,
appends that descriptor at its occurrence index, pushes the active occurrence,
saves the lexical previous owner and assigns the new executable owner. The
initial occurrence/descriptor arenas are empty (298–301). These statements
establish the index/descriptor invariant inductively; its debug assertion is
corroborating code, not its proof.

All three real Call entries use this same constructor: raw callable (621–632),
ordinary closure (634–686), operation (695–743). They use the actual selected
value's source as provider and the original `Callee.site` as Call. Each installs
`ReceiverReturn {activation,previous}` before source entry execution. Ordinary
closure entry retains its source body/environment; operation entry retains its
declaration. Re-entering a span needs only its original Call/provider descriptor
for logical attribution, since its actual remaining code, lexical links and
entry cursor already reside in the pending F fields. It does not regenerate a
body or select an entry role from descriptor equality.

At a reached Catch the explicit owner is validated while the handler remains
on the stack (1133–1157). Selection checks exact declaration identity, the actual
positive local Grant and primitive payload compatibility before capture
(1171–1203). A bound continuation triggers primitive declared-response
validation and `capture_template(&request,self.current_owner)` at 1205–1215.
The selected handler is still on the live stack; it is absent from
`request.suffix`. This call therefore obtains the actual containing owner,
including when its own receiver delimiter is below the selected bound.

The real `capture_template` (942–1000) starts with Hole, scans the actual
next-return-first suffix, and appends exactly the §4 node for every frame.
Ordinary frames are cloned without changing their source/cell/env fields;
RootCompReturn becomes View, receiver and ambient scopes become Owner, and
forwarded Catch becomes ForwardHandler. Every inner index names the previous
root, so it is smaller than the new node index: the resulting finite graph
has one descending context spine, without a new recursive host closure. It
then appends the containing Owner and stores the original declaration/event.
It adds no code from below the selected bound.

The only ordinary-frame rejection is Root/GlobalRead at 951–954, before any
selected-handler pop, binder publication or new continuation value. This
establishes an explicit provisional boundary, not the missing cache theorem.
For an available bound continuation, selection removes h, retains rather
than abandons the raw suffix, binds the original payload and allocates an
ordinary callable `ExecutableValue::Continuation(Arc<ResumeTemplate>)` under
the actual catch binder (1222–1259). It starts the actual original arm body
outside h. No selected-handler node or boundary receipt is introduced by
this allocation. The immutable template retains one original declaration and
event, not a fresh independent operation witness per field or use.

Thus the missing source-to-extraction premise is supplied by actual Call,
unwind and selection constructors on the available paths. Merely having the
node enum would not establish this result; the constructors above do.

### 10.3 Actual response entry and the distinct root completion

The ordinary Apply/Callee transition still obtains its callee first, then
allocates Delay of the whole original argument label/environment (602–619).
No argument prefix runs in that allocation. Selecting the continuation
executable enters a fresh ordinary invocation, installs its receiver return
and `ResumeArgument`, and executes that Delay once (621–632). This is the
source Value entry for k in the same invocation, not a shape-directed force.

When that computation returns, `ResumeArgument` (525–541) checks its received
view/value identity, Value interface and exact declared primitive response
through `primitive_matches` (875–884). The declaration includes Bool as well
as Unit/Int/Str; it is not an Int-only response assumption. A failed check
stops unavailable. On success it pushes one `ResumeReturn` and enters the
saved root with that response and `control:None`. No transition in this
entry executes the response value as another computation. Higher-order
responses are currently unavailable, not recursively demanded.

`EnterTemplate` is an actual machine state dispatched by `step` (351–356),
not a recursive host interpretation. Every call starts a new empty local
control link and new pending frames. The immutable Arc is not consumed or
mutated. `ResumeReturn` is the sole newly installed raw capture-root return
(534,543); the ordinary k invocation's ReceiverReturn remains beneath it.
Inner template owners, views, binds and handlers install their own local
completions above that root. Consequently their completion reaches the next
source suffix before the k caller. If an older ResumeReturn is recaptured,
it is an ordinary identity continuation, never a jump that bypasses later
pending frames; its consumer is simply `State::Return(received)`.

### 10.4 Actual owned/borrowed scopes and parent continuation

The control environment is a persistent arena of `{parent,original,resolved}`
links (65–69), local by its per-call root. `resolve_control` (925–940) uses
nearest enclosing binding; unrelated prior calls' arena entries are unreachable
from the fresh None root. Entering an Owner (1023–1059) saves the lexical
current owner, resolves its original occurrence in that environment, then
tests exact activity with `owner_active`. ModuleRun is its distinct always-live
ambient case; Invocation activity uses membership, not last-position equality.

If active, entry assigns the resolved executable owner and records `owned=false`
without pushing an activation. If inactive, it retrieves that original
occurrence's retained descriptor, calls the same fresh invocation constructor
and records `owned=true`. It never calls `receiving.enter` here. It adds the
original-to-current control link for the child and installs
`OwnerReturn {owner,owned,previous}`. This is the required concrete realization
of Owner(i,u,T), with i obtained from the occurrence-indexed descriptor arena.

`leave_owner` (903–923), used by both ordinary receiver and template completion,
checks exact executable attribution. Owned completion removes exactly its own
fresh active occurrence; Borrowed checks activity and removes none. Both
restore the lexical previous owner. Normal completion sets Return and feeds
the parent at 544–550 or 749–758. In particular a borrowed owner u below the
resumer r is entered with active list containing `[...,u,...,r]`; membership
succeeds, current_owner becomes u, no duplicate u is pushed, and its completion
restores r while leaving u and r active. The original return for u remains
outside the capture and can later end u through its own ordinary delimiter.

The owned pop still uses the last active occurrence, which is correct here:
each genuinely owned entry pushes both its new active occurrence and matching
pending completion before source child execution. Later owned entries install
later pending completions. LIFO return/unwind therefore ends all later owned
occurrences before this completion; borrowed entries change no active order.
Induction on those actual entry/completion operations establishes the owned
top-position invariant despite executable attribution to a lower borrowed
owner. This does not equate executable ownership with active-list order.

The other real consumers now use the explicit register: handler installation
and validation, original Name receipts (1399–1401), nested source Call and
capture. Validation additionally tests exact activity. Receiving's Grant query
uses membership at 236–239, so a still-active lower borrowed receiver is not
lost merely because its resumer is the last activation. Expired occurrences
are never inserted again. A fresh owner can share a descriptor while lacking
the old receiver's boundary and original receipt authority.

Bind entry (1019–1021) pushes the retained Frame and descends into its inner
node. Its ordinary completion is the already identified consumer in §3, now
at the corresponding current source method. It retains the same cell/env/label
and source cursor. Thus a child response is consumed by F, and F's completion
continues the next frame. The source g-then-f example follows from these actual
push/pop operations; no OwnerReturn or ordinary F installs a new direct jump
to the k caller.

### 10.5 Forwarded handlers, fresh execution views and original evidence

ForwardHandler entry (1061–1080) resolves the saved owner slot through the
current control links, checks exact live/executable attribution and allocates
a fresh handler occurrence. It installs the retained source Catch code and
environment with that new owner. The ordinary CatchReturn consumer (557–594)
removes that delimiter first, binds the original value pattern if present,
and evaluates its actual value-arm body outside the handler. The parent
pending context stays below that computation, including any requests it
raises. Operation forwarding/selection uses the ordinary source path at
1148 onward. This is the full existing local shallow image, not a wrapper
that skips value arms or reuses historical handler identity.

View entry (1082–1088) calls only
`receiving.execution(original.view,original.receipt)`. That constructor
(receiving.rs 186–197) authenticates the receipt/view pair, appends a fresh
execution occurrence and returns the same original view and receipt. It does
not append a receipt, change its owner, create an image/boundary, resolve a
typed binder or call `receiving.enter`. Therefore even a new executable owner
receives no fabricated Receive edge by computation-scope restoration.

The fresh execution is appended to the existing `executing_views`, preserving
the resumer's ambient scopes. Its exact RootCompReturn completion checks and
ends the `(view,receipt,occurrence)` triple (1112–1122), then applies the
original ground-result projection (552–555). Source Name execution separately
creates its genuine new receipt under explicit current_owner (1399–1414).
These two operations are distinct in the actual code, as required in §9.

New requests allocate fresh events at 1470–1483 and call Observe on the entire
current executing view stack. Observe authenticates each execution and allocates
fresh observer identities (receiving.rs 198–219). The stored template's old
event is never replayed as the new event. `local_grant` authenticates the
observation's original view and joins either genuine candidate-owner receipt
for that exact view from `receipt_index` (275–294); the observing execution's
receipt need not belong to the candidate. Receipt indexing itself occurs only
at the real receipt constructor (160–178). Thus View re-entry does not need,
and does not manufacture, a receipt for the new executable owner.

The receiving query's local RootComp relation and unknown-coverage limits
remain as in its separately reviewed certificate. Its changed activity test
matches the now-explicit source active-membership condition, and its added
execution authentication matches actual occurrence construction. This argument
does not extend that query into arbitrary typed-view completeness or negative
visibility. Fresh handler entry recomputes current evidence; original boundary
receivers, receipts, event lineage and view images remain unmodified.

### 10.6 Recapture and finite reusable interaction histories

The real request unwind (1285–1325) converts newly pending OwnerReturn by
first executing its current owned/borrowed leave action, then saving the
**resolved owner identity** as ReceiverBoundary or AmbientBoundary. It does
not save the old `owned` bit or `previous` as a future pop command. A later
capture/entry retrieves that occurrence's descriptor and resolves activity
again. Forwarded handlers retain their current installation owner; crossed
views end their current execution and retain its original view/receipt for
a later fresh execution. Completed children have already been popped and
cannot reappear in the new suffix. Other unfinished F frames, including
ResumeArgument and the identity ResumeReturn, are retained by ordinary Bind.

These are actual constructors for the conditional recapture premise. Induct
jointly on machine/source steps and finite continuation uses: the entry and
completion cases above preserve local parent order, exact live owner scopes,
original evidence and current shared cells; the request case captures exactly
the unfinished pending context with the new event. Each next k call repeats
those same proven constructor cases with fresh None control and fresh pending
frames. No use counter, uniqueness of call, store reset or old receipt renaming
is involved. Arena references remain shared: later Local completion writes
the original captured cell, and later Name/lookup reads its current contents.
Only genuinely executed later bind operations allocate new cells.

This discharges the conditional control/extraction/entry/recapture premises
for the actual available local paths, subject to the shared source typing and
ordinary transport premises stated in 10.1. It is an implementation bridge
derivation, not a proof that candidate inference supplies those global premises.
The cache-bearing, general visibility/transport and full source parents remain
OPEN. Fresh independent proof review is required before promoting this section.

### 10.7 Coverage, resources and revised commit packet

Every added machine Frame/State/template tag and all actual owner entry,
completion, capture, binder and View consumers were inspected. Program/mod
delta inspection shows only the private continuation module and explicit
unavailable variants added there; source role/body/binder lowering is unchanged.
The nine source controls in `tests/runtime_resume.rs` were read, not executed:
they cover still-active containing owner, two uses/shared Local cell, inner
completion and outer request, forwarded value arm, effectful response entry,
recapture, expired receiver grant, cache unavailability and Bool response.
They corroborate intended checks but are not premises of the derivation; no
claim of compilation or test success is made by this leaf.

Capture traverses F retained frames, O(F) in one fuel step, with ordinary
frame-field cloning costs additional. Entry uses explicit machine states;
activity membership scans at most A live occurrences and control resolution
scans at most C lexical links, giving O(F(C+A)) for entering F nodes, with
ordinary frame-field costs additional. No constant-work-per-fuel-step,
overall linear runtime, timing or heap/RSS claim is made.

Before this first-pass section froze, the primary reported an accepted major
resource finding: `Frame::ResumeArgument` owns an Arc of a template, whose
Bind nodes can own another ResumeArgument. Repeated recapture during response
forcing can therefore produce deeply nested chronological template ownership;
dropping the machine or HashMap may recursively drop that Arc chain outside
source fuel. The explicit EnterTemplate state proves neither bounded Rust
drop stack nor safe total lifecycle for that representation. The primary is
assigning the owning representation repair. Accordingly this first-pass
derivation cannot certify that resource property or support final freeze;
its actual dependency hash set must be rechecked after the repair. This is a
resource owner issue, not a changed raw-resumption source law.

Checks performed: initial exact dependency hashes, bounded source and focused
delta reads, actual constructor/consumer induction, test-source inspection and
final dependency/whitespace audit reported at handoff. No tests/builds/probes,
code writes, Git mutations, network or delegation. One static proof leaf;
requested normal Sol/high, observed runtime model/effort unknown. Primary owns
runtime verification and fresh independent review. Step-budget exhaustion keeps
the private partial control state resumable; an explicit transition error stops
unavailable rather than returning a Completed result. Allocation-success and
ordinary existing error-path assumptions have not become a new all-resource
recovery theorem.

Revised commit packet: exact lease remains this file; assignment baseline
`46bb232a4cfbdab20fd28026f0893da41d875bc3`, actual source hashes in 10.1;
§§1–8 retain their primary-reported independent review at the original hash,
while §§9–10 require fresh review. Suggested checkpoint:
`research: bridge runtime resume templates to actual constructors`.
Shared-record delta for primary: consume the available local actual control
bridge after review; distinguish it from full Resume/source coverage and
cache/visibility/principality/production parents. Next action: independent
review of this frozen actual-source derivation and primary-owned runtime
verification on the same hash set, without replaying the old absent-descriptor
obstruction that the actual Call constructors now address.

## 11. Local index equivalence before the representation repair

The primary requested a narrow proof before replacing the first-pass lexical
link scans and activity membership scans. This section derives an equivalence
from the actual first-pass owners; it does not assert that the proposed repair
has already been implemented or independently reviewed.

**Lexical control lemma.** For every successful finite administrative entry
prefix from `ResumeArgument`'s `control:None`, replace the parent-linked
ControlBinding chain by a fresh map M from original Invocation ID to resolved
Invocation ID. For an Owner insertion write `M[original]=resolved`. Lookup
returns M's entry or the unchanged original ID; ModuleRun always resolves to
ModuleRun. Then every owner resolution and ForwardHandler owner resolution
equals the first-pass `resolve_control` answer, and entry emits the same
frames, owners and fresh identities. The statement concerns the whole current
entry path, not a global map shared across calls.

Proof. `capture_template` initially has only Hole. Each appended constructor
sets inner to the preceding root, and its final containing Owner does the
same. Hence actual `EnterTemplate` follows one finite strictly descending
context chain. At each step it pushes ordinary pending frames or enters an
administrative owner/handler/view scope; none of those pushed frames executes
before Hole. It does not branch into source evaluation before that endpoint.
Therefore no ancestor entry environment has to be restored for a sibling.
Initially both the empty chain and M return the unchanged original. Bind and
View leave both environments unchanged. ForwardHandler reads but changes
neither environment. At an Owner, the induction hypothesis supplies the same
resolved identity/activity case and hence the same new owner. Prepending the
link makes it the nearest match for its original ID; overwriting M at that
key gives that same latest answer and leaves every other key unchanged. This
proves the invariant after every constructor, including repeated original IDs.
At Hole both environments can be discarded: no Frame variant stores a control
link or invokes `resolve_control` later. In particular OwnerReturn stores the
resolved owner/mode/previous owner, CatchReturn stores its resolved installation,
and a retained ResumeArgument starts a new empty entry after its response is
ready. Thus later completion/recapture needs no historical map restoration.

This proof depends on one descending entry chain and complete owner resolution
before Hole. A future lazy node entry, multiple holes or branching entry would
need a new environment lifetime proof; this lemma does not authorize a shared
mutable map across such paths. A fresh map moved through EnterTemplate states
is sufficient for the actual first-pass paths.

**Activity lemma.** Give each occurrence-indexed InvocationDescriptor a Boolean
active field. Initially the descriptor arena and active receiver stack are
empty. At the sole fresh invocation constructor append a fresh active record
and push its matching ID. On successful checked owned leave pop that exact ID
and clear only its field. Borrowed leave changes neither. Then for every
successful nonterminal prefix and every allocated ID u:

```text
invocations[u].active  iff  active_receivers contains u.
```

Proof is induction on all mutators in the inspected first-pass source:
initialization (298–305), `new_invocation` (891–900) and owned `leave_owner`
(912–922). Fresh allocation makes IDs unique, so push establishes the new
case and leaves old cases unchanged. Matching pop removes the unique matching
ID and clearing its field preserves every case. Borrowed entry/leave,
descriptor lookup, View/handler steps and capture change neither collection.
These exhaust the actual activity mutations. Consequently owner_active can
use the exact indexed bit, and a receiving candidate query can consume that
same bit obtained from its authentic candidate owner. ModuleRun retains its
separate ambient rule; it gains no invocation record or callback Grant.

The bit must be updated only after successful checked removal, or failure
must stop before a continued source transition. A mismatching pop is not a
successful inductive case. Keeping a stack in addition to the bit retains the
owned-completion order validation; the index does not justify removing it.
This is a lookup-equivalence lemma, not a new lifetime/authority source rule.
It preserves the borrowed-owner-below-resumer behavior and never rewrites a
receipt, view or boundary receiver.

The parent-selected flat template-arena repair has a separate ownership
obligation: every owning `Arc<ResumeTemplate>` edge, including those inside
ResumeArgument/Bind, must become a non-owning typed arena handle. Only the
machine owns the template arena. Then destroying an individual template cannot
recursively destroy a referenced template through those handles. Actual handle
construction, validity and teardown must still be inspected at the final
implementation hash. No bounded-drop claim is made for the first-pass Arc
representation in §10.

## 12. Final frozen arena/index implementation bridge

### 12.1 Final dependencies and unchanged statement

The primary's final repair freeze replaces three first-pass dependencies:

| Dependency under `tools/inference-playground/src/runtime/` | Final SHA-256 |
|---|---|
| `machine.rs` | `3c80ef1c6f8685f346f97b53fe819ce8ad3ef8bc9c345bb3d2dc9e08edd4e03f` |
| `receiving.rs` | `3d1ce66e6b68fd11463724431098216e0270d55cc5d6406b7aeb15ea802c8229` |
| `continuation.rs` | `c1d71046efec8dcc6393b81a85c686aef82a94edc1f5e43b9cb90c4efb49c86d` |

Program, module and both integration-test hashes remain exactly as in 10.1.
The final source was inspected at the same read HEAD `419c801bd96447efadbc6a1994c9a2f20b2e9d0a`.
This section applies the explicit §11 equivalence lemmas to the actual repaired
constructors and replaces §10's first-pass representation/resource premises.
The source statement, original witness/scopes and implemented-path coverage
remain exactly those of 10.1; the full-domain parent is still OPEN. No stronger
source availability, type inference, higher-order transport or cache claim is
introduced by changing representation.

### 12.2 Arena construction, reference validity and flat ownership

`TemplateHandle` is an integer newtype with Copy/Clone and no owning pointer
or recursive destructor (`continuation.rs` 10–11). `Machine` owns the single
`Vec<ResumeTemplate>` (machine.rs 40). Every runtime reference to a template
now contains only that handle: ExecutableValue::Continuation (129),
State::EnterTemplate (153–158), Frame::ResumeArgument (164–166), and therefore
every TemplateNode::Bind containing such a frame. The old `Arc<ResumeTemplate>`
and ControlBinding declarations/usages are absent from the inspected runtime.

`capture_template` (965–1034) still performs the same exact context fold and
containing-owner wrap. A retained ResumeArgument's old handle must already
resolve in the same arena (984–987). Cache-bearing rejection and all such
validations occur while the nodes are private, before arena publication. Only
after the entire scan succeeds does it allocate handle `arena.len()` and push
the complete template (1025–1034). The source-selected continuation binder
receives this returned handle, not a separately reconstructed template.

Induct on arena publication. It starts empty. Each published handle names its
new complete element. Every nested ResumeArgument handle in that element
names an already existing element by the just-executed validation. No runtime
path removes/reorders the arena elements or exposes a mutable template node.
Consequently retained handles stay valid through arbitrary later arena growth;
Vec reallocation moves elements but not their integer indices. Runtime reads
in ResumeArgument (534–553) and EnterTemplate (1043–1050) additionally check
their handle and node indices. Invalid private state stops unavailable rather
than executing a fabricated template. The original strictly descending inner
indices are unchanged, so entry still reaches exactly one Hole.

This replacement preserves control meaning by decoding a handle as its arena
template. Capture produces the same node fields, ordinary frame payloads,
declaration and original event as the first pass. Copying a handle in a Bind
or executable denotes the same immutable template as cloning its former Arc.
Fresh entry frames and response/control remain per use; sharing this arena
entry does not share mutable pending control or store snapshots.

For teardown, enumerate all dynamic owning paths introduced by resumption:
Machine owns the arena; an arena element owns its node vector; Bind owns a
Frame; a ResumeArgument in that Frame owns an integer handle. ExecutableValue,
State and pending/saved Frame vectors likewise own integers for template
references. None of these edges owns the referenced template or its arena.
Thus dropping a node, frame, executable, pending request or machine cannot
recursively drop another template through a template-reference edge. The
arena/vector destructor visits flat owned elements. A chronological chain of
arbitrary finite length contributes more iterations and memory, not dynamic
Rust drop-stack nesting along that chain. HashMap element drop order is
irrelevant to this conclusion. The per-entry control map owns only integer
keys/values and has no template-owning path either.

Source metadata Arcs such as Code/declaration retain their existing static
source-data ownership; they contain no owning raw-template edge. This proof
removes the specific dynamic chronological-template drop-stack dependency;
it is not a universal bound on every source metadata destructor, total memory,
allocator behavior or all existing runtime resources. It does not claim O(1)
teardown work or garbage collection during a live machine.

### 12.3 Actual map and activity consumers satisfy §11

Final ResumeArgument starts a fresh `HashMap::new()` (557). EnterTemplate owns
and moves that map from step to step (1036–1041,1126–1130). Owner entry resolves
with the exact original-ID key and overwrites it with the actual resolved
owner (1060–1086); ForwardHandler reads that same map (1101). Hole returns the
response without retaining the map (1052–1054). No completion Frame has a map
or control-link field. These are exactly §11's sufficient constructor facts,
so the nearest-parent-binding equivalence applies without assuming a future
consumer or a different context language. Repeated entries/calls have fresh
maps and unchanged shadowing. The actual owned/borrowed paths and original
evidence exclusions are unchanged.

Final `new_invocation` (904–923) appends `active:true` with the fresh indexed
descriptor and pushes that ID. Successful owned `leave_owner` (924–952)
checks/removes its exact stack ID and clears only its descriptor's active bit;
borrowed leave changes neither. Those are the only production activity
mutators in the inspected runtime. The §11 induction therefore establishes
bit iff stack membership for all successful nonterminal source prefixes.
Failure after a failed check is terminal/private unavailable, not a continued
source state satisfying the successful-prefix invariant.

Both real query owners use that same fact. Machine::owner_active (1161–1168)
reads the exact indexed descriptor bit, keeping ModuleRun distinct. The only
production `local_grant` call supplies `&self.invocations` and the authentic
validated handler owner (1219–1224); Receiving reads that owner's indexed bit
(receiving.rs 233–243). It does not accept a caller-invented activity Boolean
or make activity depend on an unrelated last receiver. Thus a borrowed owner
below the current resumer has identical activity answers in both consumers,
and a dead original receiver remains inactive after source-descriptor re-entry.
The retained stack still validates exact owned completion order.

View entry remains `receiving.execution(original.view,original.receipt)` at
1116–1123 with no receipt/boundary entry. It preserves the original receipt
identities and adds only the fresh execution scope. Final unwind 1322–1363
retains resolved OwnerReturn identities rather than stale pop mode. Together
with the unchanged frame meanings and source Call/selection paths derived in
§10, these actual repairs preserve that implemented-path correspondence.

### 12.4 Final cost, evidence and handoff

Let F be the number of captured/entered nodes and P the total cost of cloning
their ordinary owned payload/source fields. Capture costs O(F+P), amortizing
Vec growth, and occurs within one fuel step. Template entry costs expected
amortized O(F+P) for integer-key HashMap operations and Vec growth; map teardown
at Hole is included. This is not a worst-case hashing guarantee. Exact activity
lookup is O(1), and no entry control map is cloned at each step. Costs of fresh
descriptor/source identity cloning and ordinary source operations must be
included in P or accounted for separately. Source receiving queries keep their
existing boundary/row/observation/image work, now with O(1) activity lookup.
No constant-work-per-source-fuel-step or total memory bound follows.

The added `nested_resume_arguments_retain_only_flat_template_handles` unit
control constructs a 1024-link handle chain and drops its arena while retaining
one handle frame. It was read, not run by this leaf. It checks a bounded layout
case; the arbitrary finite-chain teardown conclusion comes from the ownership
enumeration above, not from that count. The primary separately reported nine
first-pass integration passes; final package verification is primary-owned and
not assumed here. This leaf ran no compiler checks/tests/probes.

All final dependency hashes were checked before the final source pass; the
handoff supplies the final note hash and final whitespace/dependency recheck.
Changed paths: this leased note only. Review status: §§1–8 have the earlier
primary-reported independent review at their original hash; added §§9–12 are
producer derivations pending fresh independent review. Requested Sol/high;
observed effective runtime metadata remains unknown. Zero delegated jobs,
heavy verification processes or measurement samples. The original cache,
full source/hygiene/Call, inference and production parents remain OPEN.

Final commit packet: exact lease is
`notes/theory/2026-10-16-runtime-resume-template-correspondence.md`;
assignment baseline `46bb232a4cfbdab20fd28026f0893da41d875bc3`; final changed
dependency hashes are those in 12.1 and the unchanged hashes in 10.1.
Suggested checkpoint: `research: bridge arena-backed runtime resume constructors`.
Shared-record deltas remain primary-owned: consume this local actual bridge
and lookup/ownership equivalences after independent review, record that the
first-pass recursive Arc drop risk was removed at its owner, and preserve all
explicit full-domain/source/cache/production gaps. Next action: independent
review of §§9–12 against this final source hash set and primary integration
with its own final verification results.
