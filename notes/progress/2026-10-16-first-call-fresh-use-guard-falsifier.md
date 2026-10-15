# First Call FreshUse: complete guards and the instantiation quantifier

Status: independently reviewed CLEAN complementary source/native audit. No compiler
counterexample found. A source-derived discriminator excludes promoting one
old-denotation copy model to arbitrary lawful instantiation. Baseline supplied
by primary: `adba69430`; native owners supplied stable at `bf0562382`.
Exclusive lease: this note only. The new constructive FreshUse note was not
read; no claim of independent review or joint theorem certification is made.

## 1. Accepted target and exact question

Use the selected
`notes/design/2026-10-16-source-application-checked-result.md` and its actual
constructor `first-call-checked-result-construction.md` §3.2. AppTarget is the
complete checked view of the original ReadInvoke, with the same provider,
independent domain, phases, world, scope, request/response and continuation
guards, plus the full A1 value check and local E1 guarantee. This interpretation
and the independently reviewed local FORWARD-FIRST-CALL are accepted inputs.
No target is reopened or replaced by a four-field product.

The audit asks whether actual capture/materialization can act coherently on
every guard, including shared anchors and historical source evidence, and
which quantifier a proposed old-denotation construction proves. The input
pre-capture model is independently source-valid. New restoration/caller
constraints remain additional obligations; native success is not defined to
prove a source model.

All original xi, actual providers/private captures, both same-z packet inputs,
pending/future observations and source scopes remain. Whole-Call W/Z extras
retain the selected definition's separate final-guard obligations; this note
does not certify them from a receiver witness.

## 2. Actual copied/shared classification in this source class

The original source is:

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

The reviewed demand-frontier construction §2–§3 supplies the following source
level facts from the actual collector/dispatch, rather than from graph shape:

| Cut / coordinate | Actual treatment |
| --- | --- |
| f's annotation alpha | Created at the formal's level 1. |
| First initializer result r | Created at level 2; the first demand's negative extrusion creates lowered y at level 1. |
| Local g capture, boundary 1, merged r/y | The representative is level 1 and shared. Its bounds remain live; they are not missing copied fields. |
| Local g capture, boundary 1, unmerged | r is local at level 2, becomes one fresh root h at use level 1; its positive lower y remains the shared level-1 anchor. Captured polarity/orientation is restored unchanged. |
| Outer receive capture, boundary 0 | The source-created frontier rows are above the boundary with false non_generic metadata, including rows shared at the earlier g cut. They are eligible for copying at this different cut. |

Native owners re-read for this audit:
`Capture::intern/row` (`candidate_scheme.rs:343–379`) canonicalizes before
interning and classifies `level > boundary && !non_generic`.
`expand_row:645–651` deliberately stops at a shared row.
`prepare_candidate_fresh_use:1134–1147` canonicalizes again, uses one
`canonical_rows` entry per current representative, and copies only when the
captured local flag and current level/metadata still permit it.

Capture immediately precedes preparation on actual module and local use
routes; no typed child runs between these two decisions. Structural cycles
return through rows; preparation allocates row entries before rebuilding
Function nodes. Two equal canonical source rows cannot independently acquire
two different current images in this preparation. Source-fixed rows use the
same live anchor, not a frozen snapshot of its bounds.

This is a real mixed copied/shared construction. It does not identify the
native level predicate with every Source-Generalize binder category by fiat.

## 3. Complete-guard read audit

| AppTarget guard/read | Actual preservation found / precise semantic condition |
| --- | --- |
| Original source c, parameter/Name references and source formation | Original HIR/source records remain. Copied native selectors must use the actual use map; source c is not renamed into a new runtime operation. |
| Fixed provider, private captures, world and actual event | No runtime provider/world is created by preparation. These remain the original witness's fields. A proof for a different invocation must instantiate its event family, not reuse one old actual f value or configuration. |
| Alpha/A1 and the full returned Value certificate | Current row occurrences use the same row map. The target membership selector must be interpreted at that use's actual source description. Old membership at one fixed selector is not automatically membership at an independently changed selector. |
| E_A/E_R/i/E1 and symbolic tails | One row map is used throughout structural fields and operands. Copied Support/Allowance/member views share a map keyed by original view and mapped tail (`:1165–1233`). Concrete source identities remain fixed. Shared tails remain live anchors. |
| Source K predicates and D incidences | Typed-boundary transport keeps original predicate identities and maps only matching typed paths. A source predicate or event is not freshly allocated merely because a native handle is fresh. Full Value(A1) must supply its current-path checks. |
| Context/payload operations | Capture follows relation_context, payload views/tails and retained latent demand roots (`:840–875`). Preparation validates the old weight/view pair, remaps the view/tail, and reconstructs the ordered context DAG. This preserves construction; semantic validity at changed generic arguments still needs the source law of that operation. |
| Historical admission/emission/Replay evidence | Captured EvidenceSnapshots keep source_bound, original relation and historical evidence. FreshUse imports those snapshots unchanged and records Transport(parent, current child, use id, from/to). An old ancestor is interpreted in its template/history environment, not globally renamed into the current caller. |
| Original requests, responses, raw continuations and pending Bind | These are source-event fields/families of the same complete witness. Type presentation does not execute, snapshot or rebind them. The original response/current-state telescope remains; g is installed only at its Return. |
| Later returned-provider observations and eligibility | The whole Value(A1) certificate carries these dependent/future checks. Observe/Receive/Inc/Grant are evaluated at the later live event, not at a copied first-call activity snapshot. |

For the selected neutral slot43/slot0 first-Call route, original context and
scoped payload are Identity/default. Identity is preserved by context renaming;
the exact source annotation supplies no omitted-formal stamp. Unrelated
nonidentity ancestors exposed by a broad evidence-reader closure cannot be
treated as this route's current support. Nonidentity bounds actually captured
elsewhere in a use retain their own ordered context and source interpretation
obligations; the neutral route does not discharge them.

`begin_candidate_fresh_bound:1380–1426` materializes its current endpoints from
the common tables, preserves captured side/owner orientation, attaches the
mapped context, and records the exact source BoundKey/use. Source sets remain
original. A copied native Contribution handle is not a new runtime request.

No concrete required read was shown absent or incorrectly associated. The
source/future objects remain available through their genuine source witness;
absence of a direct runtime field in FreshUse would not prove loss.

## 4. Completion and canonical changes: what they do and do not establish

The reviewed `extrusion-replay-capture-completion.md` supplies completion of
the actually emitted owned work at source action/restoration/publication
boundaries. It does not prove every generated constraint satisfiable or
every copied semantic guard true. Thus an outstanding unrelated FIFO item is
not this audit's discriminator.

After preparation, restoration may run typed children and qualifying intrusion.
`begin_candidate_fresh_bound` reads current canonical endpoint terms when each
bound is installed. Canonical transport keeps the actual parent/from/to
evidence; qualified row merging transfers both sides and invalidates old
intrusion-generation completion. These are the operational owners, not a
proof of a semantic quotient.

If a merge used by the semantic interpretation identifies two current rows,
the corresponding CanonicalEq obligation must hold in that interpretation.
Pre-capture CanonicalEq does not, merely by its name, prove every additional
post-preparation equality. Nor is the possibility of such an additional
constraint a counterexample: it is a genuine model obligation, potentially
derived at its independently established source owner. No authentic source
case violating that obligation was produced here.

Module routing recaptures its live root; local routing retains one prepared
FreshUse while restoring its bounds. Neither rereads an arbitrary sibling
use's materialization. Caller root links are admitted after copied-bound
restoration. They can constrain an otherwise legal copied fragment and are
not assumed true by a transport lemma.

## 5. Discriminator: one old model is not all lawful new instances

Distinguish these statements:

```text
Existential presentation copy:
  for an old valid model sigma0, construct sigma_u(mu(q)) = sigma0(q)
  and preserve its fixed anchors/guards in one copied presentation.

General source-use applicability:
  for an arbitrary lawful joint incoming description/strategy satisfying
  the allocated source clauses and client W, preserve the complete guards
  in that frame, fixing only the genuine shared/established coordinates.
```

The first can be a useful theorem. It cannot establish the second by giving
every fresh instance the same old denotations. Native preparation allocates
names; it does not choose their semantic denotations.

Here is a minimized **source-derivation discriminator**, not an executed native
acceptance claim or a compiler counterexample:

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
my make_int (u: ()) = { my k (v: ()) = 1; k }
my make_unit (u: ()) = { my k (v: ()) = (); k }
my got_int: int = receive make_int
my got_unit: () = receive make_unit
```

Only ordinary source Literal, Value-parameter Lambda, Return, Unit Call and
result Bind rules are needed. In one new description, make_int's complete
Unit invocation returns its actual k provider, and that same k's Unit call
returns Int. In the other new description, make_unit returns its own actual
k and the later call returns Unit. Each first Call is exactly the selected
Name/Unit/unannotated-result class. There is no cast, handler, State operation,
opaque guard or proposed effect-family law. No provider is changed **within**
either z; the two uses are independent source events of the same published
receive closure.

The two closed ground result contracts are disjoint. Both executions return,
so the relevant result interpretation cannot be empty. If both fresh receive
instances are assigned the same old output denotation, their exact Int and
Unit client constraints cannot both hold: that denotation would have to
contain the two actual returned ground values and be included in each of the
disjoint targets. Independent source description frames can choose the
ordinary Int and Unit instance descriptions separately. The same argument
applies to the intermediate returned-callable descriptions. A prior Int-only
model copied unchanged cannot certify the lawful Unit instance merely by
changing row IDs.

These are distinct allocated Desc binders in one joint scoped strategy; the
original shared anchors and K/D identities are not independently reassigned.
The result-type Desc is chosen before its invocation challenges. Giving one
old result denotation a new dependence on the later supplied f/runtime result
would change that binder's scope, rather than rescue the identical-denotation
argument. A pullback proof may legitimately use a different template valuation
for each independently instantiated description, subject to the same fixed
anchors and the joint client constraints; it need not preserve one arbitrarily
prechosen template valuation across all instances.

This refutes only the promotion from an old-denotation copy witness to
arbitrary lawful instantiation. It does not require every caller link valid,
show a native failed inference, or refute copying one already chosen source
instance with its original denotations. A uniform proof may instead take the
arbitrary current model, pull it back to the eligible template parameters and
apply the local theorem **at that instance**, after proving the actual source
anchor/binder correspondence. That is the relevant next obligation.

## 6. Owning source responsibility and stopping point

Selected Source-Generalize §2–§3 and construction §§3.3–3.4,5.1–5.2 specify the
required partition: owned Desc choices may vary per new frame; Shared,
Established, OneShot and intrinsic fields remain fixed; ViewLogic stays below
its description dependencies and before its challenges; EventFields follow
actual event keys; EventProof may vary per description at those same events.
Aliases retain one existing frame. Its soundness theorem starts from one
global satisfying strategy of the **joint** allocated program, including W.
It does not derive that strategy from one old model.

The first exact semantic responsibility not supplied by merely allocating the
native map is therefore the publication-indexed correspondence between these
source binders/anchors and the actual copied/shared native rows and current
AppTarget selectors. At a copied A1 read, this means the full
`ValueMem_(A1 at this incoming frame)` predicate, its dependent proof scope and
current-event arguments—not the old A1 selector renamed as a closed fact.
At a shared dependency it means the same original binder/contract in every
frame, not independent witnesses with equal printed types.

The current code/source objects were not shown incapable of providing that
correspondence. For the concrete original local/outer cuts, §2 records the
actual mixed partition. Extending it uniformly to every relevant source
publication, external monomorphic dependency and recursive capture requires
the selected source ownership/eligibility laws. Source-Generalize's genuine
L1–L5 premises remain; a recursive graph's finite storage is not hereditary
recursive introduction, and an independently valid supplied recursive f need
not have its introduction reproved by this local Call theorem.

Recommended next action: require the constructive result to state whether it
proves existential presentation copying or arbitrary lawful incoming-frame
preservation. For the latter, apply local FORWARD-FIRST-CALL under the actual
pulled-back current description and prove the source binder/anchor map; keep
new canonical equalities, context interpretations and caller links as their
explicit obligations. Do not add a registry, assume no-errors implies MODEL,
freeze all fresh types to old denotations, or narrow the source domain.

## 7. Checks, resources and commit packet

Bounded static reads only; one leased Markdown write. No tests, builds, probes,
Git operations, children, compiler/shared-record edits or runtime execution.
The new discriminator's native parsing/admission was not checked. Its evidence
is the displayed ordinary source-rule derivation, not historical acceptance
of that exact text. No independent operational oracle was used. The audit
shares the accepted source rules with the constructive lane and attacks its
quantifier scope using independently instantiated source events.

One assigned 25-minute static pass; CPU/RAM unmeasured. No claim of exhaustive
enumeration of all providers, W/Z alternatives, recursive source graphs or
nonidentity contexts. Original full first-result, arbitrary FreshUse/source
Generalize correspondence, native MODEL establishment, H2/U, principality and
cutover retain their primary-owned gates.

Sole changed path:
`notes/progress/2026-10-16-first-call-fresh-use-guard-falsifier.md`.
Baseline `adba69430`; native `bf0562382` supplied stable. Producer review completed below.
Proposed checkpoint: `research: distinguish FreshUse guard copying from lawful instantiation`.
Primary owns fresh semantic review and shared task/theory/design synchronization.

Frozen read snapshots (SHA-256):

```text
c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076  notes/design/2026-10-16-source-application-checked-result.md
89fb62b1fe9e10d6972a79f17399d4a0332cf57817bb06a07f5e054ecb4b9dfa  notes/theory/2026-10-16-first-call-checked-result-construction.md
f286eb3d0280b614caf2a870aa36204ff766241033c9dc49b75f01cde9d87fd7  notes/theory/2026-10-16-extrusion-replay-capture-completion.md
f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6  notes/theory/2026-10-16-first-call-joint-forward-preservation.md
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  crates/yu-solver/src/candidate_scheme.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
```

No dependency was edited by this worker. Dependency snapshots identify reads;
they are not a claim that all parent theorems close at these revisions.

## 8. Independent review and primary consumption

`ordinary_carrier_semantic` returned CLEAN at producer SHA-256
`197b6ba3b40dbb989d143e8d829267d1f00e7c92ad3d0de3e4e59c5947114921`,
reviewed with the companion constructive packet. The source-rule discriminator
is valid at the selected independent-frame rules; its exact new spelling was
not parsed/executed and it is not a compiler counterexample. The actual owner
audit found no concrete lost read/copy or missing-field argument.

The primary accepts that bounded result and retains arbitrary-client source
allocation, new canonical equalities/context interpretation, restoration/caller
links and universal FreshUse correspondence OPEN. The next actual source owner
is local Call/Return/ResultBind publication's complete fixed-dependency walk,
distinguishing unchanged f/alpha/returned contracts from an owned A1 logical
checking description. No new registry, source restriction or code follows.
