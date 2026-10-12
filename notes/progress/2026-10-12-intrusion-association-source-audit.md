# Intrusion association: static constructor audit

Status: unreviewed research characterization; frozen for primary review.
Gate/method: source-construction correspondence for Value/type association,
not a constructive soundness proof or a new association convention.
Baseline: `0e621f549035537e4d3e799c78f79dd9385df350` on
`research/simple-sub-intrusion`.
Lease: this file only. No compiler, test, shared-record or Git mutations.

## Objective and governing premises

Determine what the inspected actual constructors retain for both occurrences
of an extrusion parent/copy pair, and whether those records determine the
associated values used by the selected SCC comparison.

Authority is the selected operation and Value-reference sections of
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, the full
`notes/design/2026-10-12-intrusion-value-type-association.md` and
`notes/design/2026-10-12-value-reference-copied-row-ownership.md`, Source
Generalize §2 and its selected construction §§3.3, 4, 5.2, and the top-level
inference principles §§1–3. These require actual association retained by
construction, actual resolved Name targets, no incidence inheritance from
description copying, and no new association inferred from ports/bounds.

For a retained type pair `(alpha_copy, alpha_parent)`, the qualification is
`SCC_G(v_copy) = SCC_G(v_parent)` for the values actually associated with the
two type occurrences. An occurrence-level association, if needed, is not
automatically a function of the type row alone. This note selects neither a
global row map nor an enclosing-description convention.

The original reference is `simple-sub-reference` commit
`9bae772624c23b52a93c1b226157e16898b4d9db`, specifically
`shared/src/main/scala/simplesub/Typer.scala`. Its ordinary type operations
provide independent evidence for the stated type construction; they do not
define Yulang's Value graph or its association.

## Retained data and missing handoff

Locations below are pinned-baseline line numbers.

| Owning constructor / representation | Retained evidence | Limit for this gate |
| --- | --- | --- |
| `yu-hir/src/module/local_source.rs:99–171` | Each expression has `HirOccurrenceId`, `SourceNodeKey`, scope and form; Names retain resolved `DefId`, `HirParameterId` or `HirLocalId`; local bindings retain binder source, parameters and initializer. | These distinguish syntax/binders. They declare no Value identity for each type occurrence or copy transport. |
| `local_source.rs:750–769` | `record_local(id,binder_source)` and `local_parameter_owners[parameter_id] = local_id`. | Local ownership exists before constraint formation; it need not be guessed from levels or row numbers. |
| `candidate_source.rs:187–217,238–245` | An expression component recipe and parameter recipe; formal registration and formal Name incidence. Parameter Names select `CandidateEndpoint::Parameter`, other expressions select `Component`. | Source identity maps to a type recipe. A component of kind Value is still a type coordinate. |
| `shadow_apply.rs:1026–1037`; `lib.rs:1873–1901,10047–10103` | Occurrence/definition component IDs and their dense live row mapping; formal recipe rows. | Live metadata is only `Collected/Fresh` and `non_generic` (`lib.rs:789–797`). Forward recipe mapping is not an association of every copied occurrence to a Value. |
| `candidate_source.rs:394–410`; `candidate_call.rs:30–58` | `ApplySourceInput` retains owner, expression index, callee/argument source indices, operand/result recipes, checking/cause and native ports/demand. | `owner` is always `source.definition_root()` (`candidate_source.rs:402`), including nested local initializers. It does not identify the nested local root as the associated value of a demand suboccurrence. |
| `shadow_apply.rs:1343–1385`; `lib.rs:10266–10291` | The App demand is constructed from four typed terms and stored in `NativeInterface`; Function constructors accept the four terms. | No associated Value arguments or per-port occurrence association are supplied to these constructors. App source evidence remains useful, but its interpretation as association is unproved. |
| `lib.rs:12415–12435`; `candidate_extrusion.rs:4–12,21–26` | Extrusion receives endpoint, polarity, target level; its memo key is exactly this triple. | The call supplies neither source occurrence nor source Value identities for either side of a resulting pair. Reused type suboccurrences are keyed by type identity/polarity/level. |
| `candidate_extrusion.rs:112–123`; `candidate_intrusion.rs:23–27,171–219` | Fresh type row; `Parent { copy: RowKey, parent: RowKey, polarity, target }`. | This records the true type parent but contains no associated-value pair, source occurrence, or association certificate. |
| `candidate_scheme.rs:36–82,110–164,1008–1019,1320–1333` | Captured type graph, local binder ID/root/boundary, use occurrence, row remap and evidence/context remaps. | These retain type/capture/use identity. No association field is present in these inspected graph/row/node/use records. A fresh-use remap does not create an extrusion pair. |
| `candidate_intrusion.rs:375–449,477–486` | SCC vertices are solver endpoints; adjacency walks bounds and Function children; qualification compares canonical copy/parent RowKeys directly. | This consumer does not perform the selected comparison of associated values. |

The earliest visible place requiring a new **explicit correspondence** is
source type construction: recipe endpoints are allocated with occurrence and
formal identities, but no selected association is declared. App-demand
construction then combines those endpoints into Function suboccurrences
without supplying their describing-value association. The narrower decisive
preservation failure is the extrusion interface and `Parent` constructor:
even an independently supplied source association cannot be read from those
pair records as currently defined. This is a bounded statement about the
inspected route, not universal absence across all compiler subsystems.

Constraint occurrence/cause provenance and context/evidence transport are
not discarded wholesale. The failure is specifically that their existence
does not determine the selected associated values. Reconstructing a choice
from those records would need an independently selected construction law.

## Nested recursion trace and smallest discriminator

Source skeleton:

```text
my odd n = { my even n = odd(n); even(n) }
```

Use distinct descriptive labels: definition values `O` and `E`, outer formal
value `N`, inner formal value `Y`, inner Apply result value `V_R`, and outer
Apply result value `V_S`. These labels do not equate definition roots to Lambda,
Block or Apply rows. The exact string was not parsed or executed in this audit;
the Yulang planner trace below is conditional on an admitted corresponding
LocalSource tree and authentic root registration.

The approved root incidences are `O -> E` and `E -> O`. The approved Apply
incidences are `V_R -> O`, `V_R -> Y`, `V_S -> E`, `V_S -> N`, when each Name
resolves accordingly. Definition-root ownership can additionally include its
own formal Name references (`E -> Y`, `O -> N`). These shown incidences alone
place `O/E` together and leave `Y` and `V_R` outside that component. This is
not a claim that the shown clauses exhaust all admitted-source incidences.

Actual original Simple-sub type construction is independent of that graph:

1. `typeLetRhs` creates outer recursive type `o` at level 1 and inner
   recursive type `e` at level 2 (`Typer.scala:48–55`). Lambda introduces
   inner formal type `B` at level 2 (`64–67`).
2. Inner `odd(n)` uses monomorphic `o` unchanged (`62–63,205–207`), creates
   App result type `R` at level 2, and demands `o <: Function(B,R)` (`68–72`).
3. The higher-level right side is extruded negatively to level 1
   (`121–123`). Function argument polarity reverses (`144`), so genuine
   copies `C = extrude(B,+)` and `D = extrude(R,-)` are allocated (`146–156`).
   Their source links are `B <: C` and `D <: R`; `Function(C,D)` is stored
   in `U(o)` (`115–117`). These are actual polar type pairs, not Value edges.

For an admitted Yulang LocalSource tree, the planner likewise sets inner
initializer/formal/result level 2 and its publication boundary 1
(`candidate_source.rs:270–305,307–327`). The recursive module Name is a module
use (`375–378`); local publication/use follows its own slot (`381–388`).
Those facts establish a plausible construction route, not equality of this
candidate's constraints to the original derivation or runtime admission.

One retained pair is enough to discriminate the missing choice. Holding the
same type pair `(C,B,+)` and shown Value graph fixed:

| Candidate convention, already identified as unresolved by Authority | Parent occurrence | Copy occurrence | SCC conclusion from shown graph |
| --- | --- | --- | --- |
| Immediate operand / receiving description | `Y` | `O` | unequal |
| Enclosing description occurrence | `E` | `O` | equal |

The analogous `(D,R,-)` distinction is `V_R/O` versus `E/O`. These are
candidate hypotheses, not inferred associations and not a counterexample to
the final algorithm. Neither the actual `Parent` fields nor the native
Function demand distinguishes them. In particular, merely reading
`ApplySourceInput.owner` would choose outer `O` for the inner Apply as well;
the source's nested `HirLocalId E` remains elsewhere in the HIR.

## `id`, `konst`, nested Apply and split polarity

For `my id x = x`, `candidate_source.rs:213–214` makes the body endpoint the
formal recipe, and `lib.rs:11233–11260` builds a Function whose argument and
result refer to that same parameter type row. Original `Typer.scala:64–67`
and monomorphic lookup produce `Function(A,A)`. The closure value and formal
value remain distinct values. Thus reuse of `A` proves type sharing; it cannot
select whether each description occurrence associates with the formal or the
describing closure.

For `my konst x = 0`, the formal and literal/body component are distinct
type endpoints (`candidate_source.rs:336–349`; `lib.rs:11247–11250`), while
the Apply result of `konst(1)` owns `result -> konst` under the approved rule.
The returned literal provider cannot replace that callee reference. Neither
endpoint distinction nor the provider supplies an extrusion association.

For `my use f = f(0)(0)`, both Apply results own a resolved reference to the
original `f` binder. The outer demand's callee endpoint is the inner result
type endpoint (`candidate_source.rs:394–408`), but this type dependency does
not add `V_R2 -> V_R1`. Apply membership records source Names recursively;
ports and containment cannot supply the missing association.

A split-polarity construction check is conditional: if the source-shared
`Function(A,A)` is extruded at positive polarity below `A`'s level, original
`Typer.scala:131–156` creates distinct `(A,false)` and `(A,true)` copies.
Yulang's corresponding four-port traversal reverses the argument and retains
the result polarity (`candidate_extrusion.rs:224–250`); its key likewise
distinguishes the two signs. This directly checks the constructor behavior,
not source reachability of an extrusion of standalone `id`. No association
for either copied port follows from the shared type row. The nested App above
supplies source-derived opposite polarities on distinct `B/R` rows; the
same-row two-copy example supplies the narrower representation distinction.

## Generalize does not discharge the association premise

Selected Source Generalize retains `Desc(C,q,sort,sigma,Delta)` at its actual
introduction, source binder/event telescopes, resolved references, and one
simultaneous recursive description (`source-generalize-definition-and-proof.md:
205–236,364–377`). Its `new` allocation gives each eligible declaration a
`(i,q)` occurrence; aliases reuse the frame and actual runtime event fields
remain shared (`525–530`). This distinguishes a description frame from
actual value/event operands. No table entry assigns an extrusion copy's
Function suboccurrence to a describing Value. That bridge needs its owning
source/extrusion law; neither frame freshness nor containment supplies it.

## Coverage, checks and next owner

Commands: bounded `rg`, `nl`/`sed`, `cat`, read-only `git rev-parse`, and
`git diff --name-only <baseline> -- <explicit dependency paths>`, and
`git diff --no-index --check /dev/null <leased note>` (no whitespace findings).
No source
dependency differences were reported; original-reference HEAD matched its
pin. No tests, builds, runtime probes, seeds, ranges or mutations were run.
There is no model checker or executable oracle. The static oracle for type
construction is the independently pinned original source; the Value graph
and association requirements are the accepted Yulang decisions.

Resource budget: at most one lightweight shell read process at a time;
30-minute cap; completed within that cap. CPU time and peak RSS were not
measured. No heavyweight process or child agent was launched.

Unverified: exact-text admission; compiler-wide absence of other association
records; all-source occurrence catalog; copied-port transport; semantic Value
identity across invocation/fresh-use events; full Call; intrusion equality
preservation, soundness, required principality and normal progress. The search
was bounded to the source planner, native Function admission, live-row
metadata, extrusion/parent consumer and capture/fresh-use representations.
Broad searches with truncated output were only locators; the decisive fields
and constructors were reread in bounded windows.

Recommended next action: the primary resolves the already isolated association
constructor premise through the accepted decision process, then assigns the
prover a source-qualified derivation for those exact pairs and an explicitly
authorized implementer the corresponding retained evidence. Another graph
probe assuming the association would leave this premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-intrusion-association-source-audit.md`.
- Baseline SHA: `0e621f549035537e4d3e799c78f79dd9385df350`.
- Direct dependency changes: none detected against the pin; original reference
  remains `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Claim/review status: bounded static characterization, unreviewed, frozen;
  no theorem closure or implementation authorization.
- Checks already run: read-only baseline/dependency comparison, exact
  constructor reads and leased-note whitespace check; no executable verification.
- Proposed checkpoint message: `research: audit source identities at intrusion association seam`.
- Shared deltas left to primary/curator: attach this source evidence to the
  OPEN association/construction gate; record the owner of the missing copied
  occurrence association. No tasks, design index, theory status or question
  bundle changed.
