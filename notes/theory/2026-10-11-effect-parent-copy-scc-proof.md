# Effect parent/copy SCC reachability: rank obstruction and local discriminator

Status: frozen, unreviewed research checkpoint; bounded source/operational
derivation, not an established all-source theorem or a reachable merge witness.
Baseline: `0aa618f8d0fab512de4b401df4bca66950c0b8cb`
Branch assigned by primary: `research/simple-sub-intrusion`
Exclusive output: this file only
Owner: constructive proof leaf; independent review and integration belong to primary

## 1. Frozen original claim and authority

The original question ranges over finite authentic native candidate histories
formed by the current source constructors, ordinary constraint admission and
opposite-bound replay, Support/Allowance and annotation-tail transport,
freshening/restoration, extrusion, qualifying intrusion, and generalization.
For every retained **actual extrusion** record `(copy,parent,polarity,target)`
of Effect kind, determine whether distinct canonical copy and parent can enter
one SCC of the actual `G_store`. Required output is either an all-path exclusion
with its construction premises established, an authentic source-qualified
merge, or the first exact missing source premise. A copied captured row is not
itself an extrusion copy; equal names or numeric IDs are not parent provenance.

All coordinates retain their original source scope and binder. In particular,
an annotation variable is keyed by `(AnnotationScope,name)`; separately named
`'e` and `'t` below are not identified, and independent incoming uses are not
one instance. Polarity is creation provenance and bound-side meaning, not an
extra SCC edge. The graph is the existing physical adjacency; no edge inversion
or new SCC authority is selected.

Governing sources and exact sections:

- `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Direct decision**,
  **Selected operation and compiler responsibility**, **Retained boundary**:
  retain genuine extrusion parents and equate qualifying same-SCC pairs.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5:
  native mathematical inference, proof-derived implementation, efficiency,
  ordinary inference behavior, and necessary abnormal-path safety.
- `notes/design/2026-10-08-source-generalize-definition.md` §§2–4: retain the
  full scoped simultaneous relation; source Generalize is distinct from its
  implementation/public correspondence. This note introduces no alternative
  Generalize semantics.
- `notes/theory/2026-10-11-intrusion-scc-dependency-graph-proof.md` §§2–7 and
  `notes/progress/2026-10-11-intrusion-scc-dependency-orientation-audit.md`:
  frozen supplemental graph definitions/discriminators, not graph authority.
- The supplied reviewed Value invariant in
  `notes/theory/2026-10-11-local-restoration-value-scc-preservation.md` is used
  only for its separation of Value and Effect adjacency and owner locators.
  Its Value rank conclusion is not instantiated at Effect kind.

Exclusions: injected test graphs, the legacy two-sided solver, code changes,
tests/builds/probes, arbitrary reused failed states, changed source domains,
new effect restrictions, semantic redundancy of intrusion, soundness,
principality, full Call/hygiene, and public cutover claims. The exclusions are
evidence boundaries, not restrictions on ordinary supported source behavior.

## 2. Actual Effect graph and mutation owners

`candidate_intrusion.rs:415–442,476–491,614–630` establishes these edges:

```text
EffectRow(x) -> every stored direct lower/upper Effect row
EffectRow(x) -> every interned stored exact lower/upper Effect endpoint
Allowance(v) -> EffectRow(v.tail), if present
Support(v)   -> EffectRow(v.tail), if present.
```

Contributions, AnnotationMember endpoints, capture incidence, contexts,
attachment bundles and parent records do not independently supply graph edges.
Value Functions may point into Effect ports; Effect endpoints cannot point
back into Value. Thus an Effect path has only Effect rows and views after its
first Effect vertex. The same view ID does not identify Support with Allowance.

The production Effect-bound insertion owner is
`candidate_extrusion.rs::candidate_insert_bound_with_evidence:406–565`.
Its native production inputs are:

| Constructor/consumer | Physical writes and relevant level duty |
|---|---|
| `candidate_apply_effect:840–863` | Row/row selects the greater-level owner; row/view stores the view directly. It then explicitly replays opposite bounds. |
| `candidate_extrude:73–156,157–212,258–321` | Creates strict lower-level copies, installs the original-to-copy link, reconstructs views with mapped tails, installs selected copied bounds, and transports incoming Allowances. |
| `candidate_signature_effect`, `candidate_effect.rs:1441–1579` | Installs source Support/Allowance facades at the supplied annotation/operation level; a composed-negative symbolic row can instead return its tail directly. |
| `candidate_begin_bound_restoration:657–678` | Installs the captured physical owner/side with no level guard; saves the opposite count for ordered replay. |
| `merge_candidate_rows`, `candidate_intrusion.rs:525–610` | Copies both sides to the authentic parent, lowers its level to the minimum, aliases the copy, transports incidence/evidence, then replays retained lowers. |

`lib.rs:10052–10103,10181–10216` initializes empty Effect rows and false
`non_generic` metadata. `candidate_source.rs:532–541` sets source levels before
admission. Native subsequent level/representative changes are the qualifying
merge (`candidate_intrusion.rs:579–584`) and restoration of journaled state
(`lib.rs:9473–9485`); the legacy lowering body is bypassed at
`lib.rs:11689–11693`. Test metadata mutations are not authentic source events.
An authentic extrusion parent has `L(copy)=target < L(parent)` at its creation
(`candidate_extrusion.rs:88–123`).

Source facts use the native drain. Effect dispatch goes directly to
`apply_effect_task`/`candidate_apply_effect` (`lib.rs:12333–12347,11689–11693`).
It has no analogue of the Value structural-extrusion guard at
`lib.rs:12412–12456`. Context filters can also invoke `candidate_apply_effect`
directly (`candidate_context.rs:2744–2798`). Identity context returns to normal
propagation (`:2753–2755`), rather than removing the constraint.

## 3. The numerical Effect-rank route fails at an actual owner

Consider the proposed invariant

```text
R: every Effect row x storing a view v has L(v.tail) <= L(x),
   and every stored direct row edge x -> y has L(y) <= L(x).
```

Assign a view the level of its tail. R would make every Effect path
nonincreasing in level, excluding any reverse path from a strict extrusion
copy to its parent. This is a sufficient route to the original conclusion,
not an assumption of that conclusion.

Direct row/row application preserves its row-edge clause by the actual
level-selection branch. Source signature installation also preserves R when
both its fresh facade and scoped tail are created at the supplied level.
Successful view extrusion reconstructs its tail at at most the target;
ordinary copied-bound installation consequently has the expected bound
ceiling. These observations do not cover all Effect writes.

The first failed preservation case is ordinary row/view application:

```text
candidate_apply_effect(EffectRow(c), Allowance(v))
  => insert upper Allowance(v) at c; replay opposite bounds.
```

There is no tail-level check or view extrusion in this branch. The Support
dual likewise installs `Support(v)` directly as a lower of a receiving row.
A higher-level facade can replay its original view into a lower-level row.
This is an executable source-owner transition, not a transition assumed by
an abstract checker. Its authentic source activation is traced next.

Support and Allowance cannot be equated to justify a different rank:
`candidate_effect.rs:893–917` expands positive Support into all members and
its tail comparison, while `:919–959` discharges allowed atoms at Allowance
and forwards only unmatched atoms to its tail. A Var-to-Allowance comparison
instead installs the bound via the row branch. In particular the physical
edge `c -> Allowance(v) -> tail` does not assert the scalar relation `c <: tail`.

## 4. Source-shaped rank discriminator with authentic parent activation

Use this finite source form, with unique resolved family E:

```yulang
act E
my outer (f:int -> ['e] int) = {
  my x: [E, 't] int = f 1;
  x
}
```

**Claim class:** static source-constructor derivation conditional only on the
displayed source lowering to its displayed LocalSource shape and successful
ordinary finite owner operations. No parser/compiler execution or successful
whole-program typing is claimed. The syntax-to-HIR owners support the two
annotation forms: `yu-hir/src/module/source_annotation.rs:399–479` parses the
prefix computation row and arrow result, and `:505–565` retains concrete E
and the singleton symbolic names. Candidate preflight accepts these HIR
shapes (`candidate_source.rs:83–132`): the formal result is a singleton
symbolic row and x's root row is positive. There is no negative concrete
formal or unsupported multi-tail assumption.

Freeze the scopes and rows before deriving the trace:

| Coordinate | Source owner/scope | Level |
|---|---|---|
| f's parameter Value and formal `'e` Effect row | outer's formal/Definition annotation scope | 1 |
| a | computation Effect of x's initializer `f 1` | 2 |
| r | fresh original invocation Effect allocated for that Apply | 2 |
| c | actual negative extrusion copy of r in f's demand | 1 |
| t | fresh annotation `'t` in `AnnotationScope::Local(x)` | 2 |
| q | root computation-check facade for x's annotation | 2 |
| v | exact x root-row view, allowed={resolved E}, tail=t | view identity, not a row |

The source scheduler starts outer at 1 and visits a Block initializer at its
containing level plus one (`candidate_source.rs:251–326`). Formal `'e` is
allocated at f's level by `candidate_formal_effect_variable`, and its singleton
formal port is the row directly (`candidate_effect.rs:978–999,1054–1063`).
The formal construction links both Function views at the parameter before
body actions (`:1080–1100`; source action at `candidate_source.rs:282`).

1. **Real parent.** `admit_candidate_fact` allocates r at a's level and places
   it as the negative invocation port in the Apply demand
   (`shadow_apply.rs:1327–1383`). Comparing that demand with f at level 1
   negatively extrudes its structure (`lib.rs:12428–12442`). The result-Effect
   child keeps negative polarity. The younger-row branch creates c at 1,
   retains `(c,r,Negative,1)`, and directly installs c lower at r
   (`candidate_extrusion.rs:83–123`). Thus `G_store` already has `r -> c`.
   The initial direct insertion alone does **not** activate its opposite pairs.

2. **Source activates the seed.** After the Value demand drain,
   Apply's actual slot 2 emits **the original r**, not c, as lower of a
   (`shadow_apply.rs:1423–1437,1445–1465`). Equal levels choose r as upper-bound
   owner for `r <: a`. Ordinary `candidate_apply_effect` explicitly replays its
   stored c lower against the newly inserted upper a, producing `c <: a`.
   Greater-level a becomes owner, storing c as its lower. This supplies the
   enqueue event missing from an argument based solely on direct extrusion
   storage. No complete reference saturation is assumed.

3. **Actual computation Allowance.** x's annotation construction allocates
   scoped t and a negative q facade holding `Allowance(v)` at level 2
   (`candidate_effect.rs:1130–1174,1324–1353,1510–1579`). Since the annotation's
   value is Int, no latent Effect port or positive Support for t is constructed.
   Its computation owner admits `a <: q` at slot 42. Equal levels store q
   upper at a; replay of its c lower emits `c <: q`. Greater-level q stores c
   lower and replays that lower with its already installed Allowance upper.
   The resulting actual child is `c <: Allowance(v)`.

4. **Rank ascent.** `candidate_apply_effect` stores that original view upper
   at c without extrusion. Hence actual physical adjacency includes

   ```text
   r2 -> c1 -> Allowance(v) -> t2.
   ```

   The last row-to-row composite has `L(t)=2 > L(c)=1`. The open view has no
   executable closed-row filter (`candidate_effect.rs:755–766`); the identity
   propagation and explicit replay owners supply this child. Exact pair memo
   suppression cannot remove the first such physical bound: if the pair has
   already run, the same bound is already installed. There is no required
   mismatching concrete contribution in this derivation.

This is a rank discriminator at the native source constructors. It is **not**
a source-qualified parent/copy SCC merge: obtaining an ascent does not supply
the required return from t to r. Complete Call meaning is not inferred from
these present Apply constraint emissions.

## 5. Why this local discriminator does not close a parent/copy SCC

For this frozen finite source history through x's ordinary local use and
outer's capture/publication, t has no outgoing `G_store` edge. Its only source
occurrence is the root computation row of x's Int annotation.

- The root row creates the Allowance facade/check; its positive initializer
  support is explicitly excluded by the source construction's responsibility
  (`candidate_effect.rs:1324–1326`). `candidate_signature_value` for Int creates
  only the Int endpoint (`:1363–1371`). No Function latent port names t.
- Var-to-Allowance registration installs a bound at its Var owner, including
  capture incidence indexed by t. It does not install a bound on t
  (`candidate_effect.rs:552–561`; `candidate_extrusion.rs:840–863`). Incidence
  is not SCC adjacency.
- The only atomic forwarding rule could install a concrete/member lower on t
  after an unmatched atom. Such endpoints are not interned SCC vertices, and
  the displayed source supplies no concrete effect-producing operation anyway.
- x's exposed local root is Int. Its local fresh-use capture reaches no t or
  view, and reconstructs no Effect bound from this annotation
  (`candidate_effect.rs:1167–1174`; `candidate_scheme.rs:1373–1374`).
- Outer publication captures its live root at boundary 0
  (`candidate_scheme.rs:893–899`). Capture reads bounds with immutable session
  access (`:691–744`) and does not manufacture outgoing t edges. This fixture
  contains no independent client use of outer; arbitrary future clients are
  outside this local conclusion, not outside the original theorem's scope.

The remaining scalar Effect writes have nonincreasing row edges. Demand
extrusion can also copy the integer argument's Effect row, but that source
row has only Bottom/Empty atoms and scalar descendants at the target level;
it introduces no second ascent. The sole higher-level view tail reachable
from lower rows here is t, a sink and not an extrusion parent in this history.
Excising paths that end at that sink leaves a nonincreasing level graph.
Therefore no reverse path can reach either strict higher-level demand parent
from its copy. By induction to a hypothetical first Effect merge, no level or
representative update occurs that could invalidate that calculation. Thus the
specific r/c pair is separate through this finite fixture's formation and
publication. This is a local exclusion derivation, not universal absence of
Effect intrusion.

The exact missing relation for turning this discriminator into the requested
merge is `t -> ... -> r`. This source has no owning rule that emits it. Merely
reusing `'t` in an abstract graph, reversing a lower edge, treating the
Allowance edge as a scalar comparison, or demanding complete replay of a
stored constraint would invent that premise.

## 6. Restoration and transport expose the remaining global premise

A second attempted induction used the Value restoration argument: every
captured bound owner is Local, so its fresh owner has use level U and all
mapped endpoints have level at most U. This statement is false as an Effect
owner characterization.

`Capture::expand_row` for a local Effect tail first traverses incoming capture
incidence and captures the **source row's** negative Allowance bound
(`candidate_scheme.rs:619–626`). That source is not necessarily the local row
being expanded. It can be Shared at level at most boundary B. Fresh preparation
preserves a Shared source while mapping the local tail to U
(`:1008–1021,1052–1073`). `begin_candidate_fresh_bound` preserves that physical
source owner/side (`:1227–1247`). Consequently the actual restoration owner can
install

```text
Shared source at s <= B <= U -> Allowance(mapped view) -> fresh tail at U.
```

When `s < U`, this is another ascent. This is a conditional owner derivation,
not a second source-qualified merge. In particular fresh tail allocation does
not retain an extrusion parent. The local discriminator above authenticates
the low-source/high-tail **capture incidence** (`c1,v,t2`), but its Int local
scheme does not reach t2; no restoration of that incidence is claimed for x.

Positive extrusion of an Effect tail also traverses incoming incidence
(`candidate_extrusion.rs:157–175`). Its `IncomingAllowance` work item remaps
the source at the same target and installs an Allowance with the copied tail
(`:289–306`). If the source is older than the target, it is returned unchanged;
the reconstructed tail is at target. No owner inequality follows merely from
both outputs having level at most target. These are exact source owners that
an all-path argument must cover, not permission to discard incoming incidence.

Restoration itself has explicit saved-count/live-index replay
(`candidate_extrusion.rs:667–677,715–761`). Zero opposite count retires without
a child drain. Neither capture nor storage proves that all previously existing
opposite combinations were activated. The discriminator used an actual later
Apply upper admission to activate its extrusion lower; another construction
needs its own activation event.

The original universal Effect claim remains OPEN at this precise premise:
for an authentic ascent `c -> view(t)` reachable from an extrusion copy, prove
that all subsequent original-scope tail constructors and activated consumers
exclude a path `t -> ... -> parent(c)`, **or** exhibit its source-owned emission
and activation. The first responsible source seams are the scoped annotation
tail's direct/composed-negative ports and latent positive Support ports
(`candidate_effect.rs:1054–1072,1510–1579`), Function port comparison
(`lib.rs:12493–12524`), and incoming-incidence capture/restoration just listed.
The physical insertion and SCC consumer are established; what remains is the
source ownership and activation of the reverse path. A source where the same
original scoped tail occurs in a latent port is the next decisive case, not
an already established witness.

Economy audit after the two different induction routes: the operational
reachability characterization is research evidence for the selected mechanism;
the mechanism's original safety/natural-inference parent obligations retain
their class A/B status. Both numerical-rank and local-owner induction fail
for concrete constructional reasons. The next action is source construction
of the reverse path, not a third equivalent rank proof, a new reconstruction
relation, artificial annotation restrictions, or reclassification of the
original semantic obligation. No source fact known at an owner is proved lost
here; adding a certificate or changing architecture is not authorized by this
result. Required full Call, effect hygiene, soundness, Generalize correspondence
and principality remain in their original scopes.

## 7. Evidence, dependencies, and handoff

Static reads only: bounded `rg`, `sed`, `cat`, read-only Git dependency
comparison and SHA-256 capture; one lightweight shell process at a time.
Zero compiler executions, Cargo/build/test/probe/Oracle processes, benchmark
samples, Git mutations, children, or external/user contacts. The 45-minute
wall budget was respected; aggregate CPU, RAM peak, and exact wall time were
not measured. The primary remains the verification owner.

Requested runtime: `gpt-6.1-sol` / high. The registered prover role is present
and unpinned in `.codex/config.toml` and `.codex/agents/prover.toml`; callable
schema supports the role and explicit overrides. Observed effective model and
effort metadata are unavailable, **unknown**. No Astra request or execution.

Named compiler and frozen governing dependencies were compared with baseline;
the dependency diff was empty. The HIR annotation parser used for the displayed
source-shape premise is included explicitly; its baseline diff is also empty.
SHA-256 snapshot:

```text
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
f8c06bd945ca586dc2ee43ac970f138ab7b2ed2b8c6566b0aa11a1fafb109330  notes/theory/2026-10-11-intrusion-scc-dependency-graph-proof.md
3554e418f55d0d588b74aabe7adb02f26445babb88f1a2d4b7d9a93a4d04c44a  notes/progress/2026-10-11-intrusion-scc-dependency-orientation-audit.md
3dfd8ba4b21b76ee434a6b30697c5197213eae0679b84b98a6908e8a512fe6c4  notes/theory/2026-10-11-local-restoration-value-scc-preservation.md
```

Unverified: parsing/execution of the new displayed fixture, all-source Effect
reverse-path exclusion or reachable merge, arbitrary later incoming clients,
all replay completeness, publication/public schemes, semantic adequacy of
`G_store`, and the full inference correctness/principality gates. No test pass
or independent review is reported.

One next action: trace an actual source history in which the original scoped
annotation tail participates both in the low-row Allowance ascent and in a
latent port that emits/activates `tail -> ... -> original invocation parent`;
retain the precise parent record and the admission that closes the path.

## Commit packet

- Exact leased changed path:
  `notes/theory/2026-10-11-effect-parent-copy-scc-proof.md`.
- Baseline SHA: `0aa618f8d0fab512de4b401df4bca66950c0b8cb`;
  changed compiler/governing dependency hashes: none observed.
- Claim/review: bounded static source/operational derivation; local rank
  discriminator and local no-merge result; independent review pending. Original
  universal Effect reachability, semantic and production parents remain OPEN.
- Checks already run: static owner/dispatch/activation/capture inspection,
  exact baseline dependency diff and hash capture, lease-scoped whitespace
  check; zero builds/tests/runtime probes. Producer stopped writing before
  submission; no shared record or Git mutation.
- Proposed checkpoint message:
  `research: isolate Effect rank ascent and parent-copy reverse-path premise`.
- Shared-record deltas left for primary/curator: record that the numerical
  Effect-rank premise is not established and has the source-shaped discriminator
  above; link the exact tail-to-parent source/activation residual; preserve the
  selected operation and all parent gate statuses. No theory-status promotion
  or claim of semantic redundancy is proposed.
