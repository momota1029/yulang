# R73 helper suffix: cut-state reconstruction and exact unfinished ledger

Status: **UNREVIEWED SOURCE/NATIVE AUDIT; UNFINISHED/OPEN.** Neither A, B nor C.
Sole author `/root/r73_astra`; no coauthors or descendants. Requested
`gpt-6-astra` / medium; observed model and effort UNKNOWN. Session
`current-conversation-2026-10-19-r73`. Baseline supplied by Luna:
`69ecc0dc3c796f9ddbc4c7d815b1816dd97c5ccd`; no Git operation.
Contract revision 2 SHA-256
`25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f`.
The parent activation grants these outputs despite the frozen candidate heading.

## Parent and result

The original computation-forwarding preservation claim is unchanged at §§1,
6–7 of `2026-10-15-computation-forwarding-preservation.md`: one shared satisfying
assignment, original formal identities, whole resolved current-formal Name
arguments, arbitrary finite prefixes, repeated calls, simultaneous receiving
entries, and independent foreign-continuation obligations. Parent, full native
correspondence, Simple-sub A/B and production stay OPEN 0→0. R50 is NOT ADOPTED.
This packet preserves the exact R72 source printed in the R73 contract.

The complete requested cut-state was **not established**. The useful new
results are (1) the exact helper provider Argument constructor, (2) the two
independent FreshUse construction paths that must appear in its evidence ledger,
and (3) the serial restoration and Function-child scheduling obligations below.
They constrain the original mapped-admission proof and rule out a misleading
continuation table. They do not close R72-LATER-OCCURRENCE-1 or R71 coverage.
There is no authentic constructor rejection here, and absence of the requested
later occurrence has not been proved. No full-solve or runtime result is claimed.

## Stage 1: entry audit and the helper provider

All 32 direct contract dependency hashes and the contract hash match live bytes.
R72 note SHA is `504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5`;
its inbox SHA is `8e30e80a5e382fe6e3a88a65933ac5eb787e5b7773bae72657f3eb2348668401`.
Separate R72 reviews are Luna's activation context, not newly imported pins.

Use R72's symbolic names: Y is y's Value row, t its original entry effect,
n its Name effect, C the helper body's invocation effect, U its Apply result.
Let B be that Apply's application effect, R the helper Lambda RE, H the
helper Lambda root, and M the final helper-callee Name value row. The prior
qualified group lowers Y,n,C,U from 3 to 2 by redirecting copies to originals;
t remains 3 at that described boundary. Raw `(t,−,n)` does not change item
representative there. This retains R72's result, including its successful-prefix
conditions, and does not import R53's callable argument.

The helper positive Function has Argument **Int−**, not Y−. This follows from
`candidate_formal_value_pair` (`candidate_effect.rs:1340–1349`), which returns
Int+/Int−; `candidate_formal_annotation` stores `negative` in `formal_domains`
(`:1518–1524`); and `admit_lambda_fact` reads that domain (`lib.rs:11337–11340`).
The original Y still has both ordinary Int bounds and supplies the current
level used to allocate R (`lib.rs:11366–11385`). Thus the provider is

```text
Fh+ = Function+(Int−, t−, R+, U+),     level(R)=2.
```

This correction is about the positive provider. The earlier negative helper
demand remains `Function−(Y+,n+,C−,U−)` and its R72 group is unaffected.
The source emits B≤R at Lambda slot 4; Computation omits slot 3. Apply slots
1 and 2 previously emitted callee-effect≤B and C≤B
(`shadow_apply.rs:1907–1924`). These facts must be included when reconstructing
the shared R/B/C adjacency; an endpoint-level table is not their physical ledger.

## Stage 2: cut-state attempt, with unknown coordinates explicit

Fix the cut immediately after `route_candidate_local_run` has captured the
installed helper graph and prepared its fresh use, and has pushed its LocalUse
frame, before its first `step_candidate_local_use` call
(`candidate_scheme.rs:2011–2076`). All assertions are conditional on reaching
that successful constructor boundary. Numeric IDs were not observed or invented.

| State coordinate | Established information / exact missing part |
| --- | --- |
| Current source action | Final helper Name `Action::Local`, caller level 2, installed boundary 2; final x Name and final Apply remain later source actions. |
| Current typed item / queued typed work | Source admission drains its comparisons; Local restoration requires an idle typed worklist (`candidate_begin_bound_restoration:765–781`). A complete retained operation inventory across this prefix was not enumerated. |
| Local cursor | Exactly `next_bound=0`, `restoration=None`, `complete=false`, by `LocalUseCursor::default` at frame insertion. No Local restoration parent has yet been created. |
| Known original physical slot | `EffectUpperRow(t)[0]=n`, raw `BoundKey(EffectRow(t),Negative,EffectRow(n))`, from original y Name slot 1, as established by R72. Opposite Name equality was stored under n, not t's positive side. |
| Helper root slot | Positive Function admission targets H at 3; its lower-atom item is Fh+. Its exact evidence index and full physical multiplicity have not been reconstructed. |
| Representatives/levels | R72 group copies represent Y,n,C,U; originals now at 2. t is 3 at that prefix; H is introduced at 3, R allocated at 2. Complete subsequent alias/metadata inventory is unfinished. |
| Capture locality | H/t are structural local-row candidates above boundary 2; U/R/n are shared at the described levels. Provider Argument is an atom, so it does not itself reach Y. This is not a complete capture graph certificate. |
| Fresh row map | Each captured local row is fresh at caller level 2; each shared row retains its representative. Exact graph-row indices, context maps and evidence-remap indices are unfinished. |
| Fibers and evidence | Original t→n source relation and H's Lambda relation have known constructors. Full `bound_cursor`/`bound_entry` lists, evidence snapshots and physical emission/admission indices are not enumerated. |
| Memo | Earlier direct and helper comparisons retain session typed-pair state, and extrusion rewrites may be retained. Exact keys, completion generations, rewrite outputs and `by_output` groups are unfinished; idle queue does not mean empty memo. |
| Pending replay parents | Current Local cursor has none. Prefix-wide replay-operation retirement, replay-head caches, pending intrusion cursor and relation completion ledger have not all been reconstructed. |

This table intentionally exposes the failure to meet the contract's complete
cut-state requirement. In particular it does not replace absent data with empty
sets. A two-row/two-bound capture is a plausible structural projection, not an
established full capture count: `Capture::bound` emits one graph-bound record per
attached relation (or one None record when no relation is attached), deduplicated
by kind/side/lower/upper/relation (`candidate_scheme.rs:1001–1051`). Capture also
walks relation context payloads and retained demands (`:1251–1297`). The exact
fiber enumeration and its closure must therefore precede an exact next_bound
schedule. Source concrete permissions are not incoming-effect caps.

## Stage 3: restore/dispatch audit and application to the parent

For graph bound index i, `begin_candidate_fresh_bound` reconstructs lower/upper
from the one FreshUse map and retains its orientation. For each parent relation
it first invokes `candidate_context_fresh_transport_scoped`, which attaches a
child and records `Dependency::Transport` with the exact source BoundKey,
target BoundKey, use origin and FreshUse witness (`candidate_context.rs:4051–4066`).
It then imports the bound's captured evidence and starts physical restoration
with `BoundAdmissionCause::FreshUse` (`candidate_scheme.rs:1855–1906`).

In **ordinary mode**, `candidate_bound_origin_with_evidence` takes the unscoped
branch and calls `candidate_context_bound` even for FreshUse
(`candidate_effect.rs:522–545`). The latter chooses the retained processing
parent when applicable or constructs its origin relation, then attaches its
child and records `Dependency::Derived` (`candidate_context.rs:3663–3715`).
The FreshUse transport and ordinary admission are distinct constructions.
Interning may identify their RelationIds; that does not identify their
dependencies or witnesses. Neither may be silently omitted from the cut ledger.
This is immediately relevant to the parent's authentic mapped-bound premise:
an existing transport child does not, by its existence alone, identify the
relation/fiber emitted by the physical restoration or a later consumer.

Restoration inserts the physical bound and saves `opposite_count` after that
insertion. If count=0, the next step retires it without starting a replay.
Otherwise it canonicalizes owner/item at each saved opposite index, creates
ordered `(lower_input,upper_input)` keys, and drives that replay to completion
before advancing. Live canonical opposite vectors may differ after an earlier
child (`candidate_extrusion.rs:801–869`). `step_candidate_local_use` advances
next_bound only after completion; the fresh root link occurs only after every
graph bound (`candidate_scheme.rs:2153–2183`). Thus a missing fiber can alter
the number of restorations and replay ancestry even when scalar endpoints agree.

Applying this to the candidate H/t projection: H has positive Fh, while t has
negative n; freshly allocated H'/t' start without opposite bounds. Restoration
of just those one-sided families would have zero opposite counts, regardless
of repeated same-side records. This is a local check on the proposed projection,
not a proof that the complete captured graph contains only those families.

After restoration, root link and final Apply still require complete drainage.
For a Function comparison the four child tasks have the usual directions:
demand Argument≤provider Argument, demand AE≤provider AE, provider RE≤demand RE,
provider result≤demand result (`lib.rs:12653–12692`). Admission occurs in reverse
array order, with separate admission/enqueue stages and front insertion
(`candidate_step_function_dispatch:12807–12834`); admission order must not be
mistaken for pop order. Final helper Apply, both earlier loop demands, Block
result/effect facts, initializer effect slot 20 and loop Local boundary 1 all
remain part of the unfinished suffix. Omitting unused direct's initializer
effects is invalid (`candidate_source.rs:1105–1114,1430–1446`).

The level-based continuation attempt suggests no new high structural field at
the immediate helper comparison. It fails as a C proof because it does not
cover retained memo rewrites: `dispatch_live_item` reuses a retained rewritten
pair and calls `recapture_candidate_extrusion` (`lib.rs:12507–12529`), which
selects exact `(TypedPairKey,output)` groups and can activate their pending
Parents under a newly qualified source set (`candidate_intrusion.rs:388–422`).
That requires the missing memo/group/source ledger. No manual substitute
schedule, total unsigned FreshUse substitution or assumed consumer is supplied.

The first unresolved reconstruction obligation is therefore still before a
complete cut: enumerate the helper capture's exact bound-fiber/evidence records
and the surviving prior typed-pair/rewrite/group ledger. Later Work::Bound,
raw/canonical lookup and required provider/consumer lineage cannot be concluded
from this partial cut. `post_check_context` is relation-local
(`candidate_context.rs:3169–3174`), so common endpoints/ancestry do not discharge
residual or independent foreign-continuation obligations.

## Reuse, TODO and stop boundary

Reused: R72 `/root/r72_proof` for its conditional first group; R53
`/root/r53_ordinary_mixed_capture_proof` for applicable signed-operation and
source-set mechanics; R55 `/root/r55_original_name_attack` for partial-map and
original-domain cautions; R70 `/root/r70_ordinary_extrusion_proof` with
`/root/r70_extrusion_countertrace` for successful local worklist premises; R71
`/root/r71_raw_canonical_proof` for distinct raw/canonical fibers. Rejected:
R53's callable-provider capture conclusion, a total substitution inferred from
row sharing, FreshUse as Work::Bound, and equal endpoints as equal witnesses.

Mutual TODO `R73-CUT-LEDGER-1`, refinement of unchanged
`R72-LATER-OCCURRENCE-1`, owner Luna/source-native continuation: supply the
ordered source-admission → physical-emission → relation-attachment ledger up
to this Local cut, including prior direct/helper memo rewrites, groups, source
sets, generations, pending parents and replay cursors. Inputs are the same exact
source and 32 pins. Output is the complete cut certificate followed by the
admitted suffix; falsifier is an omitted relation, physical duplicate, pending
replay or retained rewrite that changes capture/restoration or later selection.
Do not spend another packet merely renaming the level projection. Change to
ledger construction or separately authorized source observation at these owners.

`NO_SAFE_CODE_SLICE`: physical insertion and ordinary FreshUse admission plus
fresh transport reveal no established violation of an approved clause. If code
evidence is needed, the minimal **PROPOSED provisional** TODO is an inert observer
at helper capture completion/restoration entry, recording exact graph bounds,
all relevant slot/evidence/fiber IDs and surviving memo/group/replay state, then
the first actual later Work::Bound and required consumer. Falsifier: actual
source constructors contradict the proposed cut or require an unavailable exact
lineage after all same-class physical slots are included. This requires Luna's
separate implementation lease; no production code or observer was written.

Three stages only; hard aggregate grant 300 seconds, no extension or carryover.
First internal clock observation 2026-10-18 22:53:08 UTC; final observation and
frozen hashes are in the single handoff. Model/effort, CPU/RSS and precise
launch-to-stop cost remain UNKNOWN where not observed. Static reads/searches
and SHA-256 checks only; no solver/parser execution, tests, builds, probes,
measurements, instrumentation, Git, network, external contact or nested CLI.
Only this note and `tasks/agent-loop/inbox/20261019-r73-proof.md` are new paths;
no scratch files. The entire 32-entry manifest is pinned by the contract hash
above; no new proof/source dependency was imported. Fresh review and authority
remain Luna's responsibility. Writer stops after freezing both leased outputs.
