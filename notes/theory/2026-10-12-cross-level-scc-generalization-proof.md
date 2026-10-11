# Cross-level Value SCC and the nested generalization boundary

Date: 2026-10-12
Status: unreviewed conditional derivation and bounded source/consumer characterization
Baseline: `ddcc6e8ef9a211eb400262a83da82d7f8e268903`, `research/simple-sub-intrusion`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; constructive proof leaf, no delegation

## 1. Frozen question and dependencies

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Keep distinct binders O, E, a (outer n), and b (inner n). The inner n shadows
the outer n. The approved definition ownership gives `O -> E -> O`; the
nested initializer belongs to E. Neither numerical level nor subtype
direction filters these source references. O/E are definition Value roots,
not type variables, Lambda rows, Apply rows, or extrusion copies.

The question is whether this cross-level SCC **alone** requires identifying
the two descriptions, or makes E's generalization generalize O's lower-level
variables. This note adds the SCC-to-generalization bridge to the
[reviewed native derivation](2026-10-12-cross-level-odd-even-inference-derivation.md)
§§3–6; it does not repeat the Call/extrusion derivation.

Quantification for the native result: every successful finite execution of
the reference rules with the lexical tree above, outer recursive placeholder
o and outer formal A at level 1, inner initializer at level 2, E's publication
boundary 1, and the reference stored-bound level invariant. Any missing
arithmetic, comparison, branch, and full Yulang Call laws remain actual local
derivation premises, with their original scopes, providers, effects, and
witnesses. No successful exact-source execution or `int -> bool` scheme is
assumed or concluded. The native result describes the reference operations;
it does not assume that arbitrary added intrusion transitions preserve their
invariant.

For the selected Yulang rules, the bounded conclusion is non-forcing: SCC
membership alone supplies neither a retained parent/copy pair nor the
registration/provenance data consumed by source Generalize. A stronger claim
that every complete Yulang E publication fixes O's entire description remains
conditional on those actual inputs. Absence of a qualifying pair does not
prove that description is fixed.

Governing sources, at the baseline above:

- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
  §§1–5 and Authority and integration.
- [Parent/copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
  Selected operation, Value-reference SCC clarification, Apply ownership,
  Nested Apply membership, Definition-root ownership, and Retained boundary.
- [Local recursive binding](../design/2026-10-10-local-self-recursive-binding.md),
  Selected source behavior and Proposed source-to-solver seam.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md),
  §§2–3, selecting its [construction](2026-10-08-source-generalize-definition-and-proof.md)
  §§3.3, 5.1–5.3.
- Reference `shared/src/main/scala/simplesub/Typer.scala:48–83,115–156,166–227`;
  local paper `/home/momota1029/rust/simple-sub-reference-paper.pdf`,
  §3.5/Figs.6–9 and §5.3. The paper's §5 explicitly excludes let polymorphism
  from its soundness/completeness sketches.

This is research evidence pending independent review, not semantic adoption,
an executable probe, or a new established soundness/principality theorem.

## 2. Direct native bridge

Let G be the approved Value-reference graph and B the separate finite graph of
type structure and stored bounds. The reviewed result establishes:

```text
every bound of v has level <= level(v);
E's scheme is PolymorphicType(1,tE);
instantiate at E's later use is freshenAbove(1,tE).
```

Define `Generic_native(E)` operationally as the variable identities entered
in the single `freshened` map by this instantiation. This avoids replacing
the algorithm with a new scheme interpretation. The constructor inserts v
in that map only after `v.level > 1` passes the guard. For every v of level
at most 1, the first branch returns exactly v, before traversing its bounds
(`Typer.scala:168–181`). Therefore

```text
Generic_native(E) intersect {v | level(v) <= 1} = empty.
```

In particular o and A remain their original identities wherever E's type
mentions them. The same holds for escaping level-1 approximations; those
copies are not thereby O-owned declarations. Bound cycles do not change the
test: the memo is installed before copying both bound lists, so a repeated
higher-level identity has one copy, and a lower-level identity remains itself.
By the bound invariant, a path from level-1 o through B cannot reach a
level-2 variable. A path from O to E in G does not contradict that fact.

The missing SCC bridge is a direct examination of the operations' inputs:
`typeLetRhs`, `constrain`, `extrude`, `PolymorphicType`, and `freshenAbove`
read terms, the type environment, levels, types/bounds, and their local memos.
None reads G, its reachability, or an O/E component number. The publication
constructor is literally `PolymorphicType(lvl,res)` after RHS inference and
the recursive-root check (`:48–55`). It neither scans a Value SCC nor changes
any variable's immutable level. The only freshening eligibility test is the
displayed level guard. Recording the genuine `O -> E -> O` incidences therefore
adds no native transition that merges O/E descriptions or admits a level-1
variable to `Generic_native(E)`. This is an input/consumer argument about the
actual reference functions, not a checker assuming their behavior.

This does not mean the two descriptions are independent. Ordinary constraints
link their uses, and E's scheme can retain shared o and its bounds. Retaining
one joint constraint relation is not an equality of the two descriptions.
No claim is made that arbitrary simplification or additional justified
constraints could never derive an equality.

## 3. Order and the selected intrusion consumer

The reference order, already derived in the reviewed note, is:

| Cut | Operation and live boundary |
| --- | --- |
| Outer introduction | Allocate o/A at level 1; O remains monomorphic. |
| Inner initializer | Infer E at level 2, resolving odd to existing o. Generate and propagate actual inner constraints; perform required polar extrusion before inserting wrong-level demands. |
| E publication | Complete its initializer/root check, then construct its boundary-1 scheme. |
| Outer final expression | Instantiate E at level 1 with coherent freshening; infer the actual outer argument and Call while O remains live. |
| O publication | Check the completed outer RHS below o and propagate its demands, then publish at boundary 0. |

This reference order does not specify a Yulang intrusion schedule. The
approved intrusion operation has the separate antecedents: an **actual**
retained extrusion pair `(copy,parent)` and two-way reachability of that pair
in the selected Value graph before equality. It concludes equality for that
pair. There is no approved rule `same Value SCC => equate every member`.
O/E SCC membership supplies no pair whose endpoints are O and E and no
incidence transport for an extrusion or fresh-use copy. The forced inner
result copy D has parent R, not O or E; root membership does not qualify D/R.

A timing shortcut would be unjustified. Definition incidences are owned at
publication, but the approved text does not settle whether an implementation
pre-registers them, nor a complete incidence-emission/settlement schedule.
Furthermore the actual private Rust driver invokes
`settle_candidate_intrusion` at typed-worklist exhaustion
(`crates/yu-solver/src/lib.rs:11994–11996,12226–12229`). Such a drain can be
part of initializer inference, before E's Install. It is false to infer from
lexical publication order that all SCC processing must wait until O is
published or E is already generalized.

At the pinned implementation, the intrusion loop considers stored parents
only (`candidate_intrusion.rs:476–488`); its adjacency still comes from bound
rows, Function ports and Effect dependencies (`:358–473`). This is an actual
consumer characterization, not an approved source-graph bridge. Consequently
neither this scanner nor successful settlement certifies the graph G or
invariant preservation for the original parent theorem.

## 4. Source Generalize: the exact obstruction to a stronger conclusion

The source package is `ScopedClosure(p_E,C_E,T,anchors,templates,N,FinalRoot)`.
Construction §5.1 supplies C_E through actual recursive-group/definition
registration. No examined approved clause identifies C_E with a
Value-reference SCC; definition ownership specifies incidences, not that
registration or the typed dependency edges.

The Generalize consumer actually distinguishes these inputs:

| Actual provenance | Consequence of construction §5.1 |
| --- | --- |
| Established external Mono contract containing O's descriptive fields | Fix every free dependency of that whole contract. Those fixed Desc declarations are ineligible. |
| Internal reference to a registered live peer in C_E | Retain the complete joint relation; do not fix its inferred description merely because its raw provider is fixed. Ordinary Desc(C_E,...) declarations remain eligible unless a real fixed dependency reaches them. |
| Value incidence `E -> O` alone | Supplies neither of those typed provenance records nor a template eligibility judgment. |

The selected same-component pair in §5.3 proves why the distinction matters:
both parameter descriptions can be eligible at either member publication,
without identifying the descriptions. That approved pair is not the nested
odd/even program and cannot supply its missing registration by analogy.
The table is an inversion of consumer rules, not two legal registrations or
two legal type clients of odd/even. No supplied source derivation establishes
either that E has a separate component with an Established O contract, or that
E may open an O/E joint description frame. The discriminator would be whether
such an opening exposes still-open O to fresh component instantiation: every
active-outer lookup must continue to reuse its monomorphic root without new.
Whether that opening is lawful with the original outer scope already supplied
is part of the missing registration/allocation bridge, not a counterexample.
Conversely local self-recursion's monomorphic open-root rule proves sharing
during initializer inference; it does not relabel the eventual source
Generalize edge as Established. Numeric reference level 1 is not itself a
source `fix` edge.

Every eligible source template remains at its **original type scope**.
Shared/OneShot/provider fields and event witnesses keep their original
telescopes, and each independent incoming frame retains the whole active
relation. Thus even genuine same-component eligibility would not authorize
an inner E use to choose O's already supplied outer description or Shared
witness independently. The exact allocation/source correspondence for that
nested publication is still needed; this note does not assume it.

The minimum missing input for the stronger full-source assertion is the
authentic E-publication registration and provenance judgment for this exact
lexical tree: C_E, original Desc ownership/type scopes, live-peer versus
Established edges for O, actual fixed dependencies, and the complete active
local clauses. It must then be connected to native boundary-1 sharing. No
source-qualified refutation of that assertion has been constructed here.
There is no reason to narrow the source domain or invent another semantic
layer to remove this input.

The Rust owners provide a narrower operational characterization:
`candidate_source.rs:254–328` schedules initializer level 2 and Install at
boundary 1; `candidate_scheme.rs:1320–1334` stores a live root/boundary rather
than a full ScopedClosure; `:1363–1374` captures/freshens it at later use.
Capture marks a row local using `level > boundary && !non_generic`
(`:300–325`); preparation rechecks that test on the current representative
(`:1009–1019`). These are actual eligibility consumers, not proof that all
source anchors, typed component edges, complete Call clauses, or replay
obligations have been constructed and consumed.

## 5. Scope, economy, and checks

The native non-forcing result follows directly. Its extension to a complete
selected Yulang publication remains conditional at the registration/source
bridge above. The universal parent/copy equality-preservation gate remains
OPEN with its original source domain, quantifiers, Call/effect/attachment/
residual meanings, soundness and required principality. This note does not
qualify a retained pair, prove copied incidence, or establish exact-source
admission, which remains unavailable in the reviewed source audit.

Economy audit: actual generation, Generalize and qualifying equality are A/B.
Recovering registration/provenance from an SCC or bound graph would be D.
The needed facts belong to original registration/Name and publication
constructors; the next evidence should come from them. The previous reviewed
note already named this source bridge. This pass adds the native consumer
argument and rejects the publication-timing shortcut, without counting the
unchanged missing registration premise as parent proof progress.

Static source/rule/PDF reads and SHA-256 baseline comparisons only; no builds,
tests, probes, measurements, compiler edits, additional workers or Git mutations.
One leaf, lightweight reads (at most five read commands concurrent),
45-minute ceiling; CPU/RSS and exact reasoning time unmeasured. The primary
retains verification/integration and independent review ownership.

Requested route: `prover`, `gpt-6.1-sol/high`. The callable schema lists prover;
its inspected role file omits model/effort pins and project defaults are
Sol/high. Effective runtime model/effort metadata is unavailable: **unknown**.
No Astra escalation or hot reload claimed.

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-cross-level-scc-generalization-proof.md`.
  It was absent before writing; primary's exclusive lease supplies ownership.
- Baseline: `ddcc6e8ef9a211eb400262a83da82d7f8e268903`; reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Direct dependencies were compared byte-for-byte with baseline blobs; no
  changed dependency hashes at the snapshot. SHA-256 changes relative to the
  preceding note's recorded snapshot: reviewed derivation now
  `839e80f5c1426531bb761d9ae6ef9475d8f89104e766a5973c356656f89ae41c`
  (it contains the prior independent review). Other listed design, construction,
  candidate_source/scheme/intrusion/lib, reference Typer and paper hashes match
  that note's snapshot. Revalidate this dependency set before integration.
- Review status: unreviewed research-only conditional derivation; writes frozen
  at submission. No theorem promotion or production certification.
- Checks: focused source/PDF reads; dependency blob/hash equality; narrow
  document whitespace, local-link and lease-scope inspection. No runtime checks.
- One next action: primary obtains the authentic C_E/provenance and original
  scope judgment, then assigns fresh independent review of this bounded bridge.
- Proposed checkpoint: `research: separate cross-level Value SCC from generalization eligibility`.
- Shared deltas left to primary/curator: record the native graph-independent
  eligibility result, potentially pre-Install intrusion consumption, and the
  exact C_E/provenance bridge still OPEN; preserve all parent statuses. No
  shared records were edited.
