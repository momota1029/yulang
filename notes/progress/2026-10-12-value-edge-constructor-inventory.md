# Value-reference constructor and binder installation inventory

Date: 2026-10-12
Status: frozen static research characterization; one minor coverage finding repaired and delta-reviewed; global reachability OPEN
Baseline: `ab477fb78ebe43859b581e168b559ea9da775a2d`, `research/simple-sub-intrusion`
Lease: this note only; complementary source audit, no delegation or implementation authority

Applicability correction (2026-10-12): under the user's
[value-to-type association clarification](../design/2026-10-12-intrusion-value-type-association.md),
the absence of a type-copy-to-binder installer or incoming edge into a type-copy
row does not establish nonqualification. The original gate compares SCCs of
the values associated with the type occurrences. Retain the bounded installer
inventory, but replace its proposed incoming-copy-edge critical path with
actual value/type association construction and transport. The earlier review
did not certify this corrected application.

## Objective and exact premise

Audit the source constructors and pre-qualification identity operations needed
to apply §5 of the reviewed [odd/even qualification proof](../theory/2026-10-12-odd-even-copy-qualification-proof.md).
This packet supplies source/artifact evidence, not another constructive proof
or a repeat of its finite graph calculation. Its questions are whether the
approved Value-edge catalogue is exhaustive, whether an edge can end at a fresh
extrusion copy without changing its resolved binder, and whether an independently
approved installation/equality can put a copy in a binder's canonical class.

For a cut before a proposed distinct parent/copy merger, let `q` be its already
justified canonical map and `K = {q(row(b)) : b is an original resolved binder}`.
The reviewed codomain lemma applies if all incoming edge targets lie in K and
`q(copy) ∉ K`. Neither condition is assumed globally in this audit. In particular,
the proposed merger cannot justify its own incoming path. A prior merger requires
its own authentic qualification history.

Authority is the [parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md)
lines 26–48, 56–121; [copied-row decision](../design/2026-10-12-value-reference-copied-row-ownership.md)
lines 12–46; [source Generalize](../design/2026-10-08-source-generalize-definition.md)
§§2–5, selecting construction §§3–5; and the top-level inference principles.
Accepted meanings are fixed: actual Value references qualify SCCs; comparison,
ports, providers, containment and parent metadata do not generate edges;
extrusion/freshening inherit no incidences and do not remap Name targets.

## Answers (a)–(d)

**(a) The approved catalogue is not specified as exhaustive.** The inspected
Authoritative Value-edge laws explicitly select Apply-result ownership, its
nested-Apply recursion, and definition-root ownership excluding nested
initializers. No additional Name, Lambda, Block, Group, record, projection,
Branch, literal or formal *Value-edge owner family* is explicitly selected by
these sources. Such source typing constructors exist, but their typing and
typed-dependency records do not establish SCC adjacency. The general reference
clarification does not equate every Value reference with a Name incidence.
Therefore absence of an additional selected family is not a global exclusion
theorem.

**(b) A selected Name incidence cannot directly target a newly allocated copy
of a different original binder row.** Its target remains `row(b)`. Extrusion
allocates a fresh distinct row and records its parent; freshening copies
descriptions only. An independent source owner may assign outgoing incidences
to a copy but must preserve that same target. Such an assignment alone supplies
no incoming edge to the copy. A Name edge can end at the *canonical class* of
a copy if that class already contains its original binder target. That is a
separate installation/equality premise, not target remapping. No selected
non-Name owner targeting a raw copy was found in the inspected Authority.

**(c) No separate approved pre-intrusion copy-to-binder equality/installation
was found.** In the inspected candidate local-source path, source component and
formal rows are installed before solving; unannotated local publication selects
its source initializer endpoint; annotated publication allocates a new target
root. Parameter Names select the original formal row. Published uses freshen
descriptions and constrain distinct occurrence facades; they do not replace
the binder registration. These paths do not explicitly install an extrusion
copy as an original binder. Canonical lookup may nevertheless observe a prior
intrusion union. The only forward candidate canonical union found is the
intrusion owner, so the audit cannot certify arbitrary prior unions using the
implementation's present graph. Source Generalize's alias/rebind and final-root
selection preserve actual source handles/objects, but give no rule identifying
an extrusion copy with an original binder row.

**(d) Global pair reachability remains blocked by an unclosed constructor and
installation boundary.** A proof of nonqualification needs complete incoming
edge coverage and canonical separation for the actual source history. A witness
of qualification needs an independently licensed incoming edge into the copy
class and a reverse path into its actual parent class, or an independently
justified earlier installation/equality that makes those Name targets possible.
Neither is supplied by bound storage, Function ports, provider identity,
Generalize dependency edges, or the equality being proposed. For result pair
`(D,R)`, R is itself an Apply result rather than a binder in the traced carrier;
if both classes remain outside K, both directions require the missing bridge.
The exact odd/even program additionally lacks the complete source admission
and primitive/Branch formation route described below.

## Authority inventory and limits

| Owner family | Exact evidence | Selected scope / unresolved seam |
| --- | --- | --- |
| Apply result | Parent-copy design:58–72 | Result row to actual resolved binder row, before/after dispatch; not returned-provider pointers. |
| Nested Apply | Same:80–89,110–115 | Recursively owns callee/argument subtrees of nested Apply; no containment edge to an intermediate result. Lambda/Block/wrapper/local-initializer membership is expressly unsettled. |
| Definition root | Same:97–108 | Own initializer/body Name references; nested initializers have their own root; roots are not universally identified with Lambda/Block/Apply rows. |
| Copied row | Copied-row decision:14–24,41–45 | No inherited edges; independently specified source ownership may supply incidences with unchanged binder targets. It selects no such additional constructor. |
| Source typing forms | Generalize construction:133–150 | Literal, Name/projection, tuple/record, parameter, Lambda, Operation, Return, Delay, elimination, Bind, Call, Branch/handler, recursion, conditional State laws. These are complete typing/evidence obligations, not a selected Value-edge catalogue. |
| Typed provenance | Generalize construction:224–268,426–495 | Internal/Established/Description/Alias/Shared/Event etc. preserve their original dependent fields; none is declared a parent-copy SCC edge. |
| Signature incidence | Native signature formation design §§2–4 | Support/license/attachment and port ownership, including registered slot aliasing. These do not equate provider/witness/source occurrences or supply Value-reference adjacency. |

The [value-content draft](../design/2026-10-11-value-content-intrusion-interpretation-draft.md)
lines 3–19 explicitly remains Draft for other constructors and transport. Its
§3 lines 105–111 proposes Name/Lambda/record/projection/group/block owners;
these rows are not additional approved families. Its §5 lines 154–170 proposes
inherited and target-remapped copy incidence, which cannot be consumed under
the later Authoritative no-inheritance/no-remap decision. No draft rule is used
as a missing edge. The separate source-value-reference draft likewise states
that it has no authority (lines 3–7).

## Compiler constructor and identity crosswalk

Paths below are relative to `crates/`; line intervals locate the inspected
baseline. The inventory covers every enumerated `LocalSourceForm` and
`Action` variant on the relevant local-source route, including the primitive,
operation, and group paths listed above. It is not exhaustive over all lawful
Yulang source semantics, every compiler subsystem, or unspecified extension
laws.

| Phase / operation | File:lines | Evidence and separation |
| --- | --- | --- |
| Retained forms and binders | `yu-hir/src/module/local_source.rs:107–172` | Nine forms: Unit, Operation, Integer, Name, Apply, Group, Ascription, Lambda, Block. Resolutions carry ModuleDef/Parameter/Local IDs, not extrusion IDs. |
| Lambda/local scopes | Same:289–319,327–372,738–803,819–830 | Parameters installed into lexical lookup; temporary local self-binding during a function initializer; publication restores then installs the same HirLocalId. Local IDs/source keys are created during lowering. |
| Resolved Names and calls | Same:487–579,636–657,665–694 | Call operands receive source indexes; Name resolves current lexical ID or module namespace. Group/Ascription retain child indexes. None manufactures a copied binder identity. |
| Module root registration | `yu-solver/src/lib.rs:1676–1697` | Dedicated definition component is registered during collection. |
| Source endpoint planning | `yu-solver/src/candidate_source.rs:187–234` | Every expression gets components; parameter Names select formal recipes. Ascription peels child Group/Ascription before execution, changing collection aliases, not selecting a later extrusion copy. |
| Active local self-reference | Same:300–328,369–390 | Open initializer endpoint supplies Link; after publication Local uses slot scheme. Nested initializers increase level; slot installation uses source endpoint. Link is a subtype constraint, not equality or Value incidence. |
| Unit / Integer facts | `yu-solver/src/candidate_source.rs:336–350,640–650,664–665` | Emit primitive and empty-effect constraints for existing Value/Effect endpoints. No Name target is present; these facts do not select a Value-reference edge. |
| Operation | `yu-solver/src/candidate_source.rs:351–368,682`; `yu-solver/src/candidate_effect.rs:786–806` | Builds the declared signature and links it to the operation endpoint by a subtype constraint. The owner and declaration are retained for signature construction, but this action emits no Value-reference incidence. This implementation fact does not rule out another approved source-owner law. |
| Group | `yu-solver/src/candidate_source.rs:435–444` | Retains a `CandidateRelation::Group` relating child and result endpoints/effects. This is solver/type structure, not an approved Value-reference edge. |
| Apply / Lambda / Block | Same:394–411,445–470 | Apply records exact inputs/result/effects; Lambda records formal/body/root ports; Block uses a Group relation to final expression. These records are not selected SCC edges. |
| Module definition link | Same:477–498 | Annotation checks actual target; otherwise body endpoint constrains separate registered root. This does not identify both owners. |
| Initial live identity | `yu-solver/src/lib.rs:9780–9781,10046–10103` | Collected component/formal rows allocated before source execution; stable component map and parameter offset. Fresh rows subsequently append to bounds. |
| Formal native registration | `yu-solver/src/candidate_source.rs:540–559`; `candidate_call.rs:406–424` | Native root comes from original formal endpoint and is paired with the same retained HirParameterId. Domain annotations do not replace this binder registration. |
| Endpoint lookup | `yu-solver/src/shadow_apply.rs:1291–1306` | Component ordinal or original parameter offset, passed through live canonical lookup. No extrusion return value is installed here. |
| Local forward installers | `yu-solver/src/candidate_source.rs:624–652`; `candidate_scheme.rs:1316–1334` | Both direct Install and retained PublishLocal lead to the sole LocalScheme assignment. Installed root is the endpoint of the provided source term, with original local ID and boundary. |
| Annotated local installation | `yu-solver/src/candidate_effect.rs:1117–1177` | Generates paired annotation descriptors, allocates fresh root at line 1162, returns that root; checks are constraints. This fresh root is not an extrusion-copy allocation. Ordinary canonical lookup can still reflect an earlier merger. |
| Formal / expression / module annotations | Same:1073–1114,1180–1205 | Formal applies constraints to original row and stores a domain view; expression constrains existing child endpoint; module checks existing target component. No direct union or copy installation. |
| Published local freshening | `yu-solver/src/candidate_scheme.rs:981–1019,1362–1382,1500–1518` | Memo over canonical rows; allocates generic descriptions, retains anchors. Final fresh term constrains original Name occurrence facade. LocalScheme root/local ID are not overwritten. |
| Active / published module use | Same:938–960,1277–1304; `yu-solver/src/lib.rs:15765–15782,16842–16888` | Original target and use components route a comparison; fresh structured incoming description is constrained into the use component. No binder retargeting or direct union. |
| Extrusion / fresh allocation | `yu-solver/src/candidate_extrusion.rs:90–163,224–253`; `yu-solver/src/lib.rs:10156–10180` | Wrong-level row gets fresh copy; actual parent retained; selected bounds/ports copied with polarity. No source Name-incidence inheritance or binder installer. |
| Canonical forest initialization | `yu-solver/src/candidate_intrusion.rs:171–219` | Every newly covered row starts as its own representative; parent records are separate. |
| Canonical forward equality | Same:474–505,513–605 | Only found forward class-union owner: settle selects retained pair, then merge writes copy representative to parent. Compression (:305–355) preserves existing classes; rollback (:103–114) restores prior representatives. |
| Current qualification graph | Same:374–469 | Enumerates bounds, Function ports, Effect rows and Support/Allowance tails. This is not a source-owned Name-incidence constructor or proof that a prior union was approved-graph qualified. |

The searches for live-component writes found production startup construction
and test-only direct row mutations; those test mutations are not source rules.
Formal-root writes found initialization and test corruptions only. LocalScheme
forward assignment has one owner; rollback clears journaled slots
(`lib.rs:9389–9399`). Candidate forests' forward union call has one call site
inside settle; forest restore/compression do not establish new equivalence.
This closes the inspected installer list, while deliberately leaving the
semantic source-owner catalogue open.

## Exact source and faithful carrier scope

The unchanged exact source is

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Its approved definition-root edges O→E and E→O remain source facts. The
[admission audit](2026-10-12-odd-even-source-admission-audit.md) is reused for
its bounded compiler result: indented BindingBody becomes ordinary HIR Error
(`yu-hir/src/module.rs:1597–1609`), while LocalSource requires an OperatorChain
body (`local_source.rs:223–255`). No If form appears in LocalSource; arithmetic
operators/true require their actual environment and laws. Syntax constructs
the indentation (`yu-syntax/src/declaration/binding.rs:317–335`), but this does
not install a native binder. This audit did not repeat parsing or execute it.

For `my odd n = { my even n = odd(n); even(n) }`, the inspected retained
Apply/Block/Lambda/local-definition route accounts for O/E roots and A/B
formals, active odd use, inner result R, E installation, fresh E description,
and final result S. It preserves the reviewed distinction between actual
retained pairs `(C,B)`/`(D,R)` and source root SCC `{O,E}`. Its source-plan
endpoints preexist C/D; E installation selects its original Lambda endpoint,
not either copy. A root may coincide with its installed source endpoint on
this path without a universal root/Lambda/Apply equality law.

Conditional source evidence: **before any forward canonical union**, the
unannotated carrier's source-row allocations and installers cannot select C/D
as O/E/A/B; copies are distinct singleton rows. After an arbitrary prior
union, this conclusion requires its justified history. The carrier changes
the exact Branch/arithmetic computation and is not an operational-admission
or full Call theorem for the original source.

## Checks, dependency freeze, resources and next action

Static `rg`, `nl`/`sed`, rule/skill reads and read-only Git identity inspection;
Python byte comparison of 21 direct inputs against baseline blobs, with SHA-256
capture: all SAME. Note whitespace and local-link checks only. No build, test,
Oracle, source execution, executable probe, seed/range, mutation or Git mutation.
No independent executable oracle is involved: compiler evidence and Authority
are separate inputs, and neither implementation graph nor previous assumed
transition checker validates source semantics. One unsuccessful `spec/` search
found no directory; no standalone spec catalogue was inspected. Broad initial
captures were truncated and relevant inputs were reread narrowly. No claim of
whole-repository semantic exhaustiveness follows from text search.

Budget: static 45-minute lane; at most four lightweight read subprocesses,
zero heavyweight processes. CPU time/RSS and exact reasoning wall time were
not measured. No child agent or model change by the producer. Independent
`spec_auditor` review found one minor crosswalk coverage omission (Operation,
Unit/Integer, and Group execution); those paths were added and the finding was
delta-reviewed clean. This review covers the artifact's bounded static scope,
not whole-language semantic exhaustiveness or global pair reachability. No
dependent input was edited.

Direct frozen SHA-256 anchors:

| Dependency | SHA-256 |
| --- | --- |
| Parent-copy decision | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| Copied-row decision | `103209a79ec590e8bdb8ae54204b18aa9ef4e0f2853e7b49546820a49f75fe52` |
| Source Generalize decision | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Reviewed qualification proof | `8b16da070740a7966e26284532444f2a6d44bd2f3bd7e08d90d3e63a71674d3a` |
| Local-source HIR | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| Candidate source | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| Candidate annotation/effects | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| Candidate schemes/installers | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| Candidate intrusion | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |

One recommended next action: primary obtains the exact missing Value-owner
constructor contract for the retained source forms, including whether any
non-Name references exist and how binder/final-root installation relates to
copy classes. Then apply the reviewed codomain lemma or return a concrete
incoming-and-reverse witness. Another outgoing copy-Name rule or finite SCC
probe leaves the decisive premise untouched. Actual selected incidence emission,
prior-union justification, complete source admission, equality preservation,
soundness, required principality and cutover remain OPEN.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-value-edge-constructor-inventory.md`.
- Baseline: `ab477fb78ebe43859b581e168b559ea9da775a2d`.
- Changed dependency hashes: none; 21 direct inputs compared equal to pinned blobs. HEAD had moved to `eaf2671431c8921e443f3248cc9c611f165f241b` at the freeze check; every inspected dependency still matched the pinned baseline.
- Review status: independent `spec_auditor` review and minor-finding delta review clean; bounded research characterization only; existing reviewed lemma reused without promotion; parent/production gates OPEN.
- Checks already run: narrow static source/authority reads, baseline byte/hash comparison, leased-note whitespace and local links; no runtime checks.
- Proposed checkpoint message: `research: inventory Value edge constructors and binder installation seams`.
- Shared-record delta integrated in `tasks/current.md`: inspected installers do not select extrusion copies as binder targets before intrusion; this closes only the current carrier inventory and leaves the approved Value-owner catalogue, graph emission, pair qualification, and global coverage/separation OPEN.
