# Mutual recursion: retained Name certificate and native owner interpretation

Status: frozen bounded constructive source/route derivation; unreviewed
Parent Value-reference / retained-parent-copy theorem: OPEN
Baseline supplied by primary: `39968b554`, branch `research/simple-sub-intrusion`
Exclusive output lease: this file; leaf, no delegation

## Frozen claim, authority and method

The parent quantifies over every supported source program P, every actual
native inference history h of P, and every retained distinct Value extrusion
pair (c,p). Its graph has actual Value variables as vertices, including distinct
copies. The edge u -> v means that the value owned by u references v. The
required SCC qualification is mutual directed reachability before the equality
being justified. Comparisons, bound orientation, lexical containment and
parent metadata are not edges. Original scopes, binders, shared captures,
fresh-use independence, complete Call, effect hygiene, soundness and required
principality remain in scope; none is discharged by a provenance certificate.

Authority is `2026-10-10-parent-copy-scc-intrusion.md`, **Selected operation and
compiler responsibility**, **Value-reference SCC clarification**, and
**Retained boundary**, under top-level inference principles §§1–5. The
source-value-reference draft supplies research notation and separate ownership
boundaries; its Draft status supplies no new semantic authority.

The exact bounded source is:

```yulang
my f x = g;
my g y = f
```

f,g are distinct module definitions. x,y belong only to their respective
Lambdas and are unused. This source contains no Apply, annotation, local
initializer, external use or source-created copy. Its successful source
formation and original-root reference result are reused from the independently
reviewed `2026-10-11-mutual-recursive-value-scc-proof.md`. The present local
derivation additionally assumes successful checked session allocation and
normal completion of the selected native Name/Lambda admissions, with no
intervening equality changing the named raw identities. These are operational
guards, not an assumed owned-value map or scanner-correctness premise.

Method: follow the original occurrence certificate through component
allocation, frozen use formation, route validation, actual admission and
durable route provenance. Test that evidence against the exact candidate
owner interpretation, instead of reconstructing references from replayed
Function bounds. Only after an actual native owner interpretation is
established would extrusion/fresh-use transport and a new scanner comparison
be justified. That prerequisite is not established below.

## 1. Joint source-to-original-row certificate

Let Rf,Rg denote the definition-root rows, Lf,Lg the LocalSource Lambda
expression rows, and Ng,Nf the Name occurrence rows for g in f and f in g.
These denote actual allocation outputs, not prescribed numerical ordinals.
Let b(k) = session.live_components[k].ordinal for a Value component position k.

HIR retains each Lambda's actual body index and resolves its body Name with
parameter-first, then unique-module lookup (`module/local_source.rs:286–317`,
`:636–656`). Thus the source-owned values and reference witnesses are the
reviewed ones: Lambda(x, Name(g)) belongs to Rf, and Lambda(y, Name(f)) to Rg.
The reviewed source-root theorem gives Rf -> Rg and Rg -> Rf, without using
occurrence rows as intermediary edges.

The occurrence-side construction has an explicit certificate too:

1. `candidate_source.rs:187–201` calls `candidate_component` with each actual
   expression's occurrence. `shadow_apply.rs:1022–1037` creates separate
   Value/Effect components and freezes their positions.
2. `lib.rs:384–410,1873–1895` constructs
   `ComponentId::Occurrence { occurrence: o, kind: Value }` and its term.
   `lib.rs:10047–10089` gives each Value component one distinct checked live
   row. In this source the module Name endpoint remains its occurrence
   component (`candidate_source.rs:209–217`); the parameter-alias exception
   is not used. There are no ascription aliases.
3. The Name arm appends the same parent-definition ordinal, resolved target
   and occurrence (`candidate_source.rs:375–378`). The final endpoint pass
   resolves the target through the actual collected definition map and
   stores `parent`, `target`, `occurrence`, `target_root_component` and
   `use_value_component` jointly (`lib.rs:1275–1327`).
4. The corresponding Lambda recipe retains its own occurrence, expression
   root component, actual body endpoint and Effect components
   (`candidate_source.rs:445–458`). The final source action links that
   Lambda endpoint to its separately constructed definition root (`:477–495`).

Consequently the following table is recoverable from this one batch/session,
without bounds, SCC membership, independently selected witnesses or a copy
quotient:

| Source record | Containing definition root | Occurrence endpoint | Resolved target root | Lambda expression/result |
| --- | --- | --- | --- | --- |
| Name g in f | Rf | Ng = b(use_value_component) | Rg = b(target_root_component) | Lf / Ng |
| Name f in g | Rg | Nf = b(use_value_component) | Rf = b(target_root_component) | Lg / Nf |

This establishes the identity and source origin of each endpoint. The
certificate is not merely a guessed relationship between two numerical rows.
It also does not identify Ng with Rg or Nf with Rf.

## 2. The certificate survives the authentic recursive route

`route_candidate_open_use` (`candidate_scheme.rs:938–945`) retrieves the same
use record, verifies that the use and both parent/target roots are active,
and invokes `route_internal`. `validated_route_use` (`lib.rs:16968–16976`)
looks up that use in the retained batch and checks its cause identity.
`route_internal_inner` (`:15765–15784`) reads exactly the frozen target-root
and use-component positions and constructs the live pair Rg <: Ng, or Rf <: Nf.

`route` (`lib.rs:16836–16918`) couples fact admission and durable route
provenance. It creates the actual occurrence/cause, admits the fact, invokes
`constrain_live_value` on that exact pair, marks the use routed and appends
`RoutedUseProvenance { use_id, fact: Some(fact), kind: Internal }`. The retained
use ID joins back to the same immutable batch record. The route record itself
is not a duplicate owner graph; it is a completed-admission provenance link.
The statement here concerns the completed successful route, not an abnormal
attempt that never publishes its route record.

Thus the native route does not lose the exact source target, containing
definition or occurrence identity. A diagnosis that the target must be guessed
later from Function bounds is too strong for this source prefix. The precise
joint certificate remains recoverable after route completion. This is the
new constructor/consumer contribution of this packet.

The actual Lambda admission reads the Name endpoint Ng, not Rg, as its result
(`lib.rs:11233–11260`) and forms the complete positive Function with parameter,
argument Effect, result Effect and result Value (`:11267–11342`). It then admits
that Function against Lf (`:11343–11370`). The reciprocal admission uses Nf.
No Effect port is removed from this derivation. These are typing constructors;
their provenance supplies no automatic owned-value reference clause.

## 3. Candidate source-owner map and the first missing implication

The certificate permits a specific candidate partial interpretation on the
original source rows. In proof notation, induced by the actual source tree:

```text
C_src(Rf) = C_src(Lf) = Lambda(x, Ref(Rg))
C_src(Rg) = C_src(Lg) = Lambda(y, Ref(Rf))
C_src(Ng) = Ref(Rg)
C_src(Nf) = Ref(Rf).
```

This is a recoverable assignment of source constructions to original rows,
not an assertion that the native owned-value interpretation C_h obeys these
equations. In particular, native Function result Ng is not converted into
the source-reference edge Rf -> Ng. The source walk follows the owned body
Name to its actual resolved target Rg. The unused parameter declarations
create no source-reference edge by themselves.

The first unproved implication is now exact:

> When a module Name with occurrence o_g is allocated the Value component Ng,
> and its validated internal route admits the resolved target Rg against Ng,
> the actual value owned by Ng is represented by Ref(Rg), with this target and
> scope, and the subsequent Lambda/root introductions preserve that owned
> reference rather than merely consuming Ng's inferred type.

The source origin of Ng and its resolved target Rg are independently
established above. What is not established is the semantic owner-constructor
clause converting that origin/route certificate into C_h(Ng) = Ref(Rg).
`ComponentId::Occurrence` identifies an occurrence component; its construction
does not define the value that this inference variable owns.
`DefinitionUse` identifies a resolved use from an admitted body. `route`
executes its typing admission and records which fact it produced. Neither
declares whether the occurrence row owns the source Name construction or
represents the value/type obtained from the target. Lambda consumes a type
endpoint and builds a positive Function type; it supplies no additional clause
settling that distinction.

This distinction matters even with perfect identity evidence. Following the
source Name as `Ref(Rg)` yields the candidate equation above. Following the
target's available value/type through the admitted comparison can instead
expose its Lambda construction or its Function bounds. The native admissions
and provenance examined here do not themselves certify which interpretation
defines the selected owned-value reference relation. This is a test of the
certificate's evidentiary limit, not an assertion that both alternatives
satisfy the user's semantics or permission to choose either arbitrarily.

Conversely, an explicit second AST field is not necessary to discharge the
premise. A justified constructor-directed interpretation of these existing
joint records could supply it. The proof gap is a semantic introduction and
preservation law, not absence of a particular representation or source ID.
This packet neither adopts that law nor proves its impossibility.

## 4. Consumer boundary and economy audit

The native owner interpretation remains unproved, so this packet performs no
new extrusion/fresh-use reference transport proof and derives no new semantic
SCC from payloads. The prior reviewed native audit remains usable only within
its stated conditional operational scope; its payload SCC is not used to
select C_h or to prove C_src is the native interpretation.

The inspected scanner entry (`candidate_intrusion.rs:358–422`) reads bound
payloads and then structural nodes. It does not consume the retained resolved
Name/use certificate described above. It also early-exits when parents are
empty. This is an actual consumer-read boundary, not a newly proved semantic
graph discrepancy. Even after a Name-owner law is supplied, it must be shown
how the chosen interpretation reaches this consumer. The copy-SCC bridge's
row/row nonextrusion and guarded root-sharing facts remain separate operational
results; they cannot substitute for the missing owner clause.

The earlier owner-introduction and native-payload methods met the same owner
premise. This new pass tested their obstruction against a concrete additional
certificate and its completed route retention. It removes a possible
identity-loss diagnosis; it does not close the semantic interpretation premise.
Another occurrence-map inventory or payload SCC computation would leave that
implication untouched.

The parent fidelity obligation remains A/B. Recovering resolved targets from
bounds would be D reconstruction debt, but that recovery is unnecessary for
these original Names: the canonical source evidence already survives. The
next owning work is to establish the semantic Name/Lambda interpretation and
its consumption using that evidence, rather than allocate another target
certificate or weaken ordinary inference. No graph semantics, representation
or implementation change is adopted.

One next action: the primary's source/native construction owner should resolve
the displayed Name-owner implication against this exact joint certificate and
successful route, then specify the matching Lambda/root preservation law and
consumer interpretation. Only after that should the actual extrusion and
fresh-use maps receive reference-transport proofs. The universal retained-pair
theorem, complete Call, hygiene, soundness, principality and cutover remain OPEN.

## Checks, resources and frozen dependencies

Commands: bounded `cat`, `rg`, `sed`, `sha256sum`, one clock lookup and one
`apply_patch` to this lease. Some initial combined captures truncated; decisive
constructor and route sections were reread narrowly. No code, test, build,
Oracle execution, executable probe, Git operation, delegation or shared-record
write occurred. At most three concurrent lightweight reads; zero heavy/probe
processes or measurement samples. The 45-minute stop bound was not exhausted;
exact reasoning wall time, CPU and RSS were not measured.

Requested normal route: Sol/high under the primary's proof packet and inspected
configuration. Native launch arguments and effective model/effort metadata are
unavailable to this leaf: observed settings unknown. No Astra or reload claim.
This producer does not independently review or certify its result.

Baseline identity is supplied by the primary; no Git comparison was performed.
The following hashes pin the live read snapshot. Solver/HIR hashes match the
prior constructor snapshots; no dependency was edited by this leaf.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-source-value-reference-intrusion-draft.md` | `4323a2223dbeb563f7822e6ff4fb889438c36d5a9139c0872070ac8112fefd94` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-value-reference-scc-source-bridge.md` | `1bc8b29b7b1f3995bf3adedf604fe15db80be8e4bc8f1d0771644a449d086aef` |
| `notes/theory/2026-10-11-value-owner-introduction-proof.md` | `f9c9d648d2bcfb91e97c2549c06819608860a73e0b59831695347be691946943` |
| `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` | `332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d` |
| `notes/progress/2026-10-11-mutual-recursion-value-scc-source-audit.md` | `04be51c44e2ead3805ffee59a4a9587eff64fe4952e3b5b74d29f6caf1bd55cc` |
| `notes/theory/2026-10-11-mutual-recursion-copy-scc-bridge.md` | `2e797c0004a38ddd2f2c4dd7e75caf04f85c9fd46dcfe2b92ae386e8adf24f23` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |

## Commit packet

Exact lease/change: `notes/theory/2026-10-11-mutual-recursion-native-value-reference-bridge.md`.
Baseline: primary-supplied `39968b554`. Changed dependency hashes: none caused
by this leaf; baseline-content comparison remains primary-owned. Claim/review:
bounded source/route certificate derivation and candidate interpretation,
unreviewed; all parent gates OPEN. Checks already run: static constructor/route
reads, dependency SHA-256 snapshot and output inspection; no tests/builds.
Proposed checkpoint message:
`research: retain mutual Name certificate through native route admission`.
Shared-record delta left to primary/curator: source identities and resolved
targets remain jointly recoverable after native admission; the precise remaining
premise is the semantic Name-owner/Lambda preservation law and its consumer,
not recovery of a lost target ID. No shared records or authority changed.
