# Approved extrusion occurrence: source construction audit

Status: bounded static characterization; unreviewed research checkpoint;
frozen at handoff. No theorem, semantic approval or production closure.
Baseline supplied by primary: `c15ecbaa3`.
Exclusive lease: this file only. No Git commands, builds, tests or delegation.

## Objective and exact governing premises

Audit whether the actual source-to-extrusion route constructs the approved
record `(occurrence, origin Value, receiving Value, produced polar pairs)`.
The main equality-preservation obligation belongs to the primary's prover
lane. This complementary audit traces constructors and their information
boundaries; it does not select a replacement association or caching policy.

Governing sources:

- `2026-10-11-yulang-inference-top-level-principles.md` §§1–5: mathematical
  Simple-sub operations, proof before dependent implementation, efficiency and
  necessary abnormal-path safety.
- `2026-10-10-parent-copy-scc-intrusion.md`: “Selected operation and compiler
  responsibility”, “Value-reference SCC clarification”, Apply-result and
  nested Apply membership, and definition-root ownership.
- `2026-10-12-intrusion-value-type-association.md`: “Approved extrusion-event
  qualification”, “Qualification”, and “Implementation and proof boundary”.
  Each actual occurrence retains its origin, receiver and produced pairs;
  those two Values' SCC equality qualifies the pairs. The displayed nested
  `f/g` event has origin `G`, receiver `F`, and pairs `(C,B,+,1)` and
  `(D,R,-,1)`. Freshening alone is not extrusion. Type rows are not automatically
  semantic Value vertices or permanently owned by one Value.
- `2026-10-12-value-reference-copied-row-ownership.md`: “Decision” and “Scope
  and proof boundary”. Description/bound copies do not inherit Value-reference
  incidences or retarget resolved Names.
- `2026-10-08-source-generalize-definition.md` §2 and its selected construction
  §§3.3, 4, 5.2–5.3: actual introductions, resolved references, simultaneous
  recursive relation, independent frames and shared actual operands.
- `2026-10-10-local-self-recursive-binding.md`: “Selected source behavior” and
  “Proposed source-to-solver seam”. Active recursive locals use one open root;
  adjacent local declarations remain sequential. No local mutual group is
  silently introduced by this audit.

The supplied baseline was not checked with Git, as this packet forbids Git.
The live files actually read are pinned by the SHA-256 snapshot below. Primary
validation of their equality to `c15ecbaa3` remains necessary for integration.
No dependency was changed by this producer.

## Information retained at each seam

Locators are line numbers in the hashed files, not assertions about every
compiler path. “Value row” below names a solver type coordinate.

| Constructor / carrier | Actual retained data | Boundary for the approved occurrence |
| --- | --- | --- |
| HIR `module/local_source.rs:99–171,329–364,740–791` | Expression occurrence/source/scope, resolved `DefId`/`HirLocalId`/parameter identity; local binder and initializer; parameter-to-local ownership. Initializer Lambda starts in `LocalInitializer`; body enters parameter scope. | Original local identity is available before solving. Scope or parameter ownership is not yet an extrusion origin/receiver certificate. |
| `candidate_source.rs:187–217,238–245` | Occurrence-to-component recipes, parameter recipes, formal registration and formal Name incidence. Parameter Names reuse the parameter endpoint. | Recipe/type sharing does not identify a semantic Value or every copied occurrence. Formal registrations use the module definition root as `owner`. |
| `candidate_source.rs:250–327,369–410` | Levels, active initializer endpoint map, direct recursive links; Apply callee/argument indices and typed operands. | The nested local owner is not carried as an Apply origin: `ApplySourceInput.owner` is always `source.definition_root()` at line 402. The active map supplies type endpoints, not an occurrence certificate. |
| `candidate_call.rs:30–59`; `shadow_apply.rs:1335–1404` | Apply checking/cause, source index and native four-port demand; `NativeInterface` remembers its Terms. | App syntax/checking identity exists, but the demand constructor receives no selected origin/receiver Value pair. A checking occurrence is not automatically an extrusion occurrence. |
| `lib.rs:3997–4003`; `candidate_extrusion.rs:763–803` | Typed task, optional context relation/replay acknowledgment; replay lower/upper bound incidence and diagnostic parent. | Replay preserves useful derivation data but its signature supplies no source Value endpoints or extrusion event ID. |
| `lib.rs:12415–12439`; `candidate_extrusion.rs:4–12,21–35` | Extrusion input is endpoint, polarity and target level. Local maps are keyed by exactly that triple. | This interface cannot directly retain the required origin/receiver or distinguish their occurrences. |
| `candidate_extrusion.rs:90–162`; `candidate_intrusion.rs:23–28,171–219` | Every newly allocated younger row gets true `Parent { copy, parent, polarity, target }`, before bound traversal. | Pairs are genuinely retained, but without grouping under a source extrusion identity or two Value endpoints. A vector index identifies a pair record, not the approved whole occurrence. |
| `candidate_scheme.rs:36–82,110–165,981–1020,1316–1334,1500–1518` | Captured type graph/bounds/evidence, live local root and boundary, use occurrence, row and context remaps, restoration cursor. | These records have no approved occurrence certificate to capture/transport. Fresh-use IDs and type remaps cannot substitute for one. |
| `candidate_intrusion.rs:375–486` | SCC graph interns solver Value/Effect endpoints, walks bounds/Function ports and compares canonical parent/copy rows. | This is not the selected origin/receiver SCC comparison over independently constructed Value-reference incidences. |

**First source construction hole:** when the nested Apply demand is formed,
the source constructor does not materialize the already selected origin `G`
(inner declaration) and receiver `F` (resolved outer recursive value) as
inputs to the level-crossing operation. `ApplySourceInput.owner = F` would
give the wrong origin if used for this purpose. The HIR still retains enough
identity to locate the inner declaration; this is a missing construction and
handoff, not proof that all source information was destroyed.

The decisive downstream hole is stronger and narrower: the actual extrusion
interface and `Parent` representation retain neither those Values nor a common
occurrence ID. Even an externally established source-origin law cannot be
consumed from these records as currently defined. Recovering an association
from row IDs, levels, port shape or bound direction would repeat the withdrawn
construction rather than implement the selected occurrence rule.

## Concrete nested recursion: original source derivation

Use the actual original reference
`shared/src/main/scala/simplesub/Typer.scala` (primary reference pin
`9bae772624c23b52a93c1b226157e16898b4d9db`; file hash below):

```text
let rec f = lambda x.
  let rec g = lambda y. f y
  in g x
in f
```

Hypotheses: this term is supplied to the reference's ordinary constructors;
normal allocation succeeds; the listed successful constrain calls complete.
No Yulang Value association is assumed to follow from Scala's type variables.

1. `typeLetRhs:48–55` introduces outer recursive `o` at level 1. Inner `g`
   gets recursive type `e` at level 2. `Lam:64–67` gives inner formal `B` at
   level 2; `App:68–72` gives result `R` there.
2. `Var:62–63` and monomorphic `instantiate:205–207` return `o` itself. The
   inner call requests `o <: Function(B,R)`.
3. `constrain:121–123` extrudes that high-level demand negatively to level 1,
   using a new operation-local polar cache. `extrude:143–156` reverses
   argument polarity and preserves result polarity. It creates exactly
   `C = extrude(B,+,1)` and `D = extrude(R,-,1)` in this first prefix: B has
   no lower bounds and R has no upper bounds at its introduction.
4. The one-sided links are `B <: C` and `D <: R`; the rebuilt demand
   `Function(C,D)` enters `U(o)` (`115–117`). These links are subtype facts,
   not Value-reference edges. Ordinary replay uses subsequent opposite
   bounds; it supplies no Yulang intrusion rule.

Under the **accepted** Yulang occurrence rule, this event's Values are `G/F`.
The approved definition-root references give `F → G` and `G → F`; the
occurrence therefore qualifies its two retained type pairs. This is an
application of the recorded source decision, not an independent proof that
the current compiler emits that certificate or that equality preserves typing.
No demand-port owner alternatives are reconsidered here.

`freshenAbove:166–188` is different: it uses one unpolarized variable map per
instantiation, copies both sides above the boundary, and leaves older variables
unchanged. `PolymorphicType.instantiate:201–202` calls it after publication.
The Scala reference has no Yulang Value SCC or retained extrusion event, so
its type construction validates the prefix only; it cannot prove the extension.

## `my odd/even`: native candidate prefix and its exact limits

The user example is:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

No parse/execution of this text occurred. The inspected `LocalSourceForm`
inventory (`local_source.rs:107–137`) has no conditional form. Hence this audit
does not claim an actual private native trace of its conditional/arithmetic
body. For the source-readable Call-bearing analogue, use:

```yulang
my odd n = { my even n = odd(n); even(n) }
```

Hypotheses for the candidate prefix: the corresponding LocalSource has been
admitted; authentic module/internal-use and local-root registrations exist;
the private graph/effects route runs successfully; no unrelated mutation
intervenes. This is finite hand evaluation of inspected code, not an executed
test or theorem of source admission.

Let `O/E` denote semantic definition Values; use lowercase `o/e` for their
type roots. Inner formal type `b`, inner result type `r` and module Name type
`n` are separate coordinates. `candidate_source.rs:254–305` puts outer
roots/formal at level 1 and inner initializer/formal/Name/result at level 2.
Lambda preserves level; only the local initializer enters the next level.

`execute_candidate_graph_plan:842–882` activates module roots and internal
uses before member source schedules. The module Name of `odd` routes through
`candidate_source.rs:672–676` and `lib.rs:15765–15782`, requesting `o1 <: n2`.
Row admission (`candidate_extrusion.rs:816–831`) stores this as a lower bound
on n. The inner Apply builds its negative demand

```text
d2 = Function−(b2, argument_effect2, invocation_effect2, r2)
```

and requests `n2 <: d2`. Opposite-bound replay (`763–803`) requests `o1 <: d2`.
The structured-upper branch (`lib.rs:12428–12439`) calls negative extrusion to
level 1. The four-port traversal (`candidate_extrusion.rs:224–253`) produces
the following initial direct-port records in traversal order:

| Pair | Kind | Polarity / target |
| --- | --- | --- |
| `(c_b,b)` | Value type coordinate | `+,1` |
| `(c_ae,argument_effect)` | Effect type coordinate | `+,1` |
| `(c_ie,invocation_effect)` | Effect type coordinate | `−,1` |
| `(c_r,r)` | Value type coordinate | `−,1` |

For this unannotated prefix, b has no lower bound, r has no upper bound, the
argument Name effect has only its purity leaf bounds, and the invocation effect
has just been allocated (`shadow_apply.rs:1347–1357`). Initial Call effect
forwarding occurs after value admission (`1412–1443`). Thus copying the selected
bounds in this prefix adds no other row parent pairs. This exact four-pair claim
does not extend to annotated bodies or later operations; those may traverse
additional younger rows in bounds/effect capture incidence (`extrusion:124–175`).
The two Effect pairs are recorded as emitted type evidence, not as semantic
Value graph vertices or a proof of effect-intrusion correctness.

The source root cycle is `O ↔ E`, and the corresponding selected event has
origin E and receiver O. Type parents b/r need no incoming Value edges to
qualify through that occurrence. The old argument “copies have no source
incoming edge, so the event cannot qualify” does not apply. Conversely, the
emitted Parent records alone do not establish that the compiler constructed
this E/O event.

After the prefix, inner Lambda admission uses its actual parameter/body
endpoints (`lib.rs:11233–11265`); installation retains e and boundary 1
(`scheme:1316–1334`). Later local `even` capture classifies younger generic rows
as local (`301–325`), stops expansion at older anchors (`567–574`), and allocates
fresh description rows at use level 1 (`1008–1019`). It creates no extrusion
Parent in that allocation loop. The fresh bounds are restored before linking
the fresh root to the Name occurrence (`1500–1518`). This is type lifecycle
evidence, not a complete later occurrence-certificate transport trace.

## Sharing, recursion, levels and consumer obligations

- **One operation:** rows and structure have separate operation-local maps;
  memoization precedes bound traversal (`extrusion:27–35,73–79,121–123`). Cyclic
  selected bounds reuse their mapped polar row; two signs of the same row use
  distinct keys. All newly produced pairs, including recursively reached bound
  rows, must be attributable to the actual occurrence. Older rows return
  unchanged (`90–94`) and produce no new pair. Structural rebuilds/atoms are
  not themselves row parent pairs.
- **Across tasks:** `lib.rs:12350–12374` can return for a current relation or
  replay an already transformed child instead of allocating a new copy graph.
  Currency is relation/generation sensitive (`11463–11473`), not simply a
  global pair hit. `RelationKey` includes pair/context (`context:203–210`).
  However `TransportReason::Extrusion` stores endpoint/polarity/level
  (`220–230`), without the two Values or event identity. No conclusion follows
  that semantic occurrences may be collapsed just because type work is reused;
  the approved design deliberately leaves the faithful caching policy open.
- **Nested recursion:** active outer local initializers remain in the map
  while helpers are visited; recursive references emit direct Link actions
  (`source:300–309,381–388`). Their type roots stay monomorphic. Module internal
  roots likewise stay active until all member schedules finish (`scheme:842–915`).
  These mechanisms preserve type sharing; they do not select the source event
  origin. A nested module Name is recorded with the enclosing module parent
  (`source:375–378`), which is coarser than the approved nested declaration owner.
- **Mutual recursion:** the module graph planner activates all member roots
  and captures them after schedules finish. Source Generalize §5.3 retains one
  whole recursive description relation per incoming frame with the same actual
  closures. This is distinct from asserting that the candidate's bound scanner
  is the approved Value graph. Sequential locals do not imply a local mutual
  group; no such new route was traced or assumed.
- **Lambda ports:** both `Function(A,A)` and distinct argument/result rows are
  possible (`lib.rs:11247–11260`; reference `Lam:64–67`). Shared type identity
  does not give every port a permanent Value owner. Four-port polarity copies
  preserve the selected signs, while occurrence qualification belongs to the
  source event, not a port-shape reconstruction.
- **Generalize/fresh use:** Source Generalize's `Desc`, `Build`, and `new/alias`
  rules (construction `205–236,364–377,525–530`) preserve introductions,
  equation references and description frames. They do not construct this
  extrusion certificate. Candidate `Graph`/`FreshUse`/`LocalUse` preserve
  captured type/evidence/use data; adding or reusing a frame is not automatically
  an extrusion occurrence and does not copy Value incidence. Boundary/use
  levels are type-allocation conditions, not filters on O/E references.
- **Actual consumer:** the inspected intrusion loop compares type-row SCCs,
  including Effect rows and Function structure, then merges those rows
  (`intrusion:375–486,504–505`). Parent polarity/target are only creation
  provenance there. A faithful source-event carrier and approved Value graph
  are both missing premises for replacing this consumer; reversing bounds or
  inserting type-copy vertices does not supply either premise.

Runtime object references, approved source Value-reference incidences, subtype
bounds, contextual derivation edges and extrusion provenance are therefore
five different relations in this audit. In particular an Apply result's
reference to the actual callee binder survives even if the returned runtime
provider is another object; no copied type row retargets that reference.

## Coverage, failure conditions and next owning action

Commands were bounded `cat`, `rg`, `nl`/`sed` source reads, `sha256sum`, and a
single leased-note write. A search of `candidate_extrude(` in solver sources
located the two non-test structured-bound branches in lib.rs; additional
candidate_effect.rs callers are inside its `#[cfg(test)] mod tests` at 1580.
No build/test, checker, parser execution, seeds/ranges, mutations, performance
samples or Git commands ran. Some locator outputs truncated; decisive
constructors were reread in small windows. No exhaustive repository-wide
absence search is claimed.

The independent original source supplies ordinary type-construction evidence.
It shares none of Yulang's proposed event/SCC extension. The candidate prefix
shares the actual candidate transition rules, so hand evaluation cannot prove
those rules' soundness. The accepted Value decisions supply normative graph
incidence and the displayed event endpoints; they are not execution evidence.
The prefix fails to apply if admission/registration, normal allocation, graph
route selection or successful replay hypotheses fail. Dependency hash changes
invalidate the affected source locators and must be adjudicated before use.

Resource use: one leaf, no children, no heavyweight process, lightweight shell
reads only, within the assigned 30-minute wall cap. Exact CPU time, peak RSS
and reasoning wall time were not measured. Unverified scope includes exact
conditional-text admission, full post-prefix event inventory, all-source
origin/receiver construction, semantic Value identity through arbitrary
invocations, certificate behavior under errors/replay/canonicalization and
fresh use, complete Call, effects, equality preservation, soundness,
principality, normal progress and combined termination. Parent gates stay OPEN.

Recommended next action: assign the **owning source-demand/replay construction**
the narrow certificate obligation for the admitted nested Call prefix: retain
inner declaration E/G, resolved receiving recursive Value O/F, one actual
extrusion identity and its emitted signed pairs through replay/memo reuse.
Submit its exact construction invariant to the existing prover lane before
any dependent production implementation. No encoding, cache policy or
compiler edit is authorized by this research note.

## Dependency snapshot and commit packet

SHA-256 of the direct files read:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd notes/design/2026-10-12-value-reference-copied-row-ownership.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895 notes/design/2026-10-10-local-self-recursive-binding.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987 crates/yu-solver/src/candidate_context.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df crates/yu-solver/src/candidate_effect.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

- Exact leased/changed path:
  `notes/progress/2026-10-12-extrusion-occurrence-source-audit.md`.
- Baseline SHA: `c15ecbaa3`, supplied; Git baseline comparison remains
  primary-owned. No source dependency edited; baseline-relative dependency
  changes unknown until that comparison. File hashes above identify this audit.
- Review: producer characterization, unreviewed, frozen; no independent
  self-review claim or proof/implementation promotion.
- Checks already run: exact constructor/consumer reads, bounded caller search,
  dependency hashing and leased-note textual integrity check; no executable
  inference verification.
- Proposed checkpoint message:
  `research: audit approved extrusion occurrence source construction`.
- Shared-record deltas intentionally left to primary/curator: attach the
  first missing origin/receiver/event handoff and memo-reuse obligation to the
  OPEN occurrence-construction gate; distinguish the original two Value pairs
  from the candidate's four direct-port pairs; withdraw copy-vertex
  nonqualification applicability; retain equality, source admission, complete
  Call, effect and F5 gates OPEN. No shared task/index/design/theory or question
  file was changed.
