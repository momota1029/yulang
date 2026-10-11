# Extrusion copy: retained source origin and the missing value ownership law

Date: 2026-10-11
Status: frozen bounded static source audit; unreviewed research checkpoint
Parent gate: OPEN; no parent/copy semantic SCC or scanner correspondence proved
Primary-supplied baseline: `35e88c8113c9c6516e260170503bea753e4ede6`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file

## Objective, fixed input, and authority

Determine whether existing source records and later scheme owners identify the
actual value and its references for the fresh result copy `C` in the corrected,
reviewed search note's fixed source:

```yulang
my f x = { my inner y = f y; inner g }; my g y = f
```

One bounded static owner pass; no source variants or constructive SCC attack.
The earlier theory note fixes a different extension (`inner z = g z; g`) and
chooses its argument copy. Its allocation analysis is historical input here;
its source and copy identity are not substituted into this witness. The
reviewed original-root proof covers `my f x = g; my g y = f` only and supplies
no new source cycle for this extension.

Exact governing sections: parent-copy SCC decision **Direct decision**,
**Selected operation and compiler responsibility**, **Value-reference SCC
clarification**, and **Retained boundary**; top-level inference principles
§§1–5 and **Evaluation**. Vertices are actual Value variables; edges are
references in their values. Comparisons, bound-storage direction and Parent
metadata do not independently determine those edges. No language meaning is
selected by this audit. A retained AST or a new certificate is not assumed to
be required by the selected operation.

Claim class: bounded source/artifact characterization with explicit prefix
hypotheses, not a semantic impossibility or a general theorem. Assume
**H_source**: successful formation/collection of this exact LocalSource with
the displayed resolutions; and **H_prefix**: native source execution and replay
reach the inspected extrusion of the nested Apply demand before row equality.
Neither exact-source execution nor replay arrival is established by this static
audit. These are the same execution guards retained in the corrected search.

## Retained ownership and actual original identities

The original source has not been globally discarded. `ConstraintBatch.hir`
retains its HIR (`crates/yu-solver/src/lib.rs:828`), whose LocalSource holds
owned expression and binding arrays (`crates/yu-hir/src/module/local_source.rs:16`).
`LocalSourceBinding.initializer` selects the inner Lambda; Lambda.body selects
the nested Apply; Apply.callee/argument select its exact Name occurrences
(`local_source.rs:105`, `:156`, `:335`, `:556`). The initializer is initially
scoped to `LocalInitializer(inner)`, then its body to the inner parameter
(`:335`). Following the binding/Lambda links retains the initializer owner
despite that narrower parameter scope. Parameter lookup precedes module lookup
(`:636`), so the nested `y` refers to inner's parameter, while nested `f`
refers to module `f`. The distinct `y` in module `g` is not interchangeable.

For the single jointly constructed batch/session, define:

```text
row(k) = session.live_components[k].ordinal
root(d) = row(batch.root_component_positions[batch.definitions[d.ordinal].root].component)
F = root(d_f), G = root(d_g)
N = row(batch.occurrence_component_positions[o_nested_f].value)
P = row(batch.occurrence_component_positions[o_nested_apply].value)
Y = session.parameter_live_base + q_inner_y
H = row(batch.occurrence_component_positions[o_inner_lambda].value)
```

Here `q_inner_y` is the actual parameter recipe position selected by its
`HirParameterId`, not a guessed ordinal. `candidate_source.rs:177` constructs
the positions and parameter map; `:210` selects the parameter endpoint for
Name `y`; `shadow_apply.rs:1022` retains occurrence/component positions;
`lib.rs:10047` allocates distinct checked dense Value rows. Source level
installation at `candidate_source.rs:532` preserves the source-plan levels.
Under H_source, `F,G` start at level one and `N,P,Y,H` at level two.

The Module Name record retains `parent=d_f,target=d_f,occurrence=o_nested_f`
(`candidate_source.rs:376`, `lib.rs:1275`). That `parent` is the containing
module's collection/scheduling identity. It does not make `F` the value owner
of every reference in inner's initializer. The HIR initializer links above
retain the actual local ownership. The graph-plan active-root/use tables and
`route_candidate_open_use` validate orchestration (`candidate_scheme.rs:869`,
`:938`); their native pair is `F <: N` (`lib.rs:15765`), not a graph edge.

## Exact information available at extrusion

| Record/owner | Actual information retained | Limit for this copy |
| --- | --- | --- |
| `ApplySourceInput` (`candidate_call.rs:30`, emitted at `candidate_source.rs:399`) | Module root, Apply index, exact callee/argument indices, original component/parameter endpoints and result component | Names original `P`, not fresh `C` |
| `NativeInterface` (`candidate_call.rs:48`, installed at `shadow_apply.rs:1380`) | Original live callee `N`, argument `Y`, result `P`, original demand `D`, all effect ports | Not updated to the extruded demand or `C` |
| `candidate_call::observe` (`candidate_call.rs:282`) | Checks exact HIR Apply/operand identity, scopes, original demand/port agreement | Validates original construction; supplies no copy-owned source value |
| Fresh row allocation (`lib.rs:10156`) | Actual new dense ordinal, level one, empty Value bounds, `Fresh` metadata | No occurrence, initializer or reference-owner field |
| `Parent` (`candidate_intrusion.rs:24`, `:178`, `:214`) | Actual `copy=C,parent=P,polarity=Negative,target=1` | Ancestry/provenance, not a reference or value definition |
| Extrusion memo (`candidate_extrusion.rs:29`, `:122`, `:365`) | Operation-local original endpoint/polarity/target to copy map | Dropped on return; not an owned source-value map |
| Reconstructed Function (`candidate_extrusion.rs:325`) | Actual remapped argument/result ports `Yc,C`, with both effect ports preserved | A negative type demand; no established source-value ownership for `C` follows |

The finite prefix from the corrected search is reused conditionally, not
rerun. `candidate_extrude(D,Negative,1)` visits the result `P` negatively
(`candidate_extrusion.rs:247`). Its empty selected upper snapshot gives an
actual fresh `C`, then Parent(C,P,Negative,1), and inserts the one-sided bound
link at `P` (`:95`, `:112`, `:121`, `:123`). It reconstructs the Function with
`C` as result. At this stopping point `lib.rs:12441` enqueues the rewritten
comparison and returns; it has not admitted that reconstructed demand on `F`.
No later admission is inferred from queue retention. No graph edge is inferred
solely from the comparison, link direction, structural port or Parent record.

There is a positive, narrower reconstruction: starting from the actual Parent
record for `C`, its parent `P` matches the live row of the original retained
Apply result component. That Apply input and HIR indices identify the exact
original nested expression `f y`, with actual callee Name row `N`, resolved
module target `F`, and parameter endpoint `Y`. Its lexical owner is inner's
initializer, recovered from the retained binding/Lambda links. This constructs
the origin identity chain `C --parent provenance--> P --component/Apply locator-->
o_nested_apply`; it is not a Value-reference path. It establishes more than
an anonymous fresh row and less than the value/reference identity sought for C.

## Later source and scheme owners do not supply the missing law

Source actions retain the original Lambda recipe with body endpoint `P` and
expression root `H` (`candidate_source.rs:445`). Installation publishes
`LocalScheme { id: inner, root: H, boundary: 1 }` (`candidate_scheme.rs:1319`).
The subsequent `inner` use captures from that live root and prepares a fresh
use (`:1363`). These later operations have not been executed in this audit.

The retained Graph is explicitly live algebra: Node/Row/Bound with actual row
keys, Function child nodes, source-bound keys and contextual evidence
(`candidate_scheme.rs:36`, `:77`, `:96`). Capture expands actual bounds
(`:566`) and stores their evidence (`:520`); fresh construction retains a
joint row remap (`:1008`). LocalFreshRoute also retains the local identity and
use occurrence (`:122`). These are real provenance and transport records.
They neither manufacture an AST for `C` nor establish which Value references
the user-selected meaning assigns to it. In this fixed prefix, level-one `C`
would be an older shared anchor at a local boundary of one, if capture reaches
it; fresh use is not by itself another extrusion parent allocation.

Consequently source origin recovery is available, while the exact unresolved
premise is: **the selected negative extrusion operation determines an owned
Value for C and maps each reference in that value to actual Value identities,
with a proved correspondence to the selected source-reference meaning.**
The inspected records are potential inputs to that law. A proof must establish
the law at the extrusion/source owners; a checker assuming it, a scheme row
remap, or associating C with the parent expression does not establish it.
This is not evidence that C has no semantic value, that copying references is
impossible, or that a new representation is necessary. No return path C to P,
same-SCC qualification or scanner equivalence is obtained.

Recommended next action: give the constructive owner this retained origin
chain and ask it to establish the owned-Value/reference law for the exact
negative result extrusion. Preserve H_source/H_prefix separately. Test that
existing evidence suffices before proposing any representation change. Do not
repeat a source variant or a graph lemma that assumes that law. Parent remains
OPEN; production changes require a separate exact lease.

## Coverage, resources, dependencies, and freeze

Checks: bounded `cat`, `rg`, `sed`, `sha256sum`, and leased-file patch/readback.
One static pass on this source and direct source/extrusion/Apply/scheme/allocation
owners. No independent oracle or executable experiment; seeds/ranges/mutations
do not apply. Shared assumptions are native level/polarity behavior and the
unexecuted source/replay prefix. Whole-source acceptance, replay arrival/failure,
later source admission, rollback, scanner, complete Call, generalization,
effects, soundness, principality and cutover remain unverified. Startup's combined
task/index capture was truncated; only current relevant steering and authority
locators were consumed, not the entire historical task backlog.

At most four concurrent lightweight read processes at startup; later reads and
the single artifact write were sequential. Zero Cargo/build/test/Oracle/Git
commands, children or measurements. CPU/RAM/wall time and observed runtime
model/effort are unknown; no model policy change. Existing authority, behavior
none, local research scope, cold path, internal surface. Independent review is
primary-owned and pending. Artifact writing stops before handoff.

Inspected SHA-256 dependency snapshot (no dependency edited by this worker):

```text
notes/theory/2026-10-11-mutual-recursion-parent-copy-proof.md d198a3392cee6907b37a3856c3582b05e9bf7ea490876d1a5a3cf38a5d47507a
notes/progress/2026-10-11-mutual-recursion-parent-copy-search.md e9241c2aa184ea7679525e912651e79b29f47a977d00aa28ffc0312e25dc8035
notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md 332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d
notes/design/2026-10-10-parent-copy-scc-intrusion.md 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
notes/design/2026-10-11-yulang-inference-top-level-principles.md edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
crates/yu-hir/src/module/local_source.rs 906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
crates/yu-solver/src/lib.rs c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
crates/yu-solver/src/candidate_source.rs 13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
crates/yu-solver/src/candidate_call.rs 79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
crates/yu-solver/src/candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
crates/yu-solver/src/candidate_intrusion.rs aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
crates/yu-solver/src/candidate_scheme.rs 9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
crates/yu-solver/src/shadow_apply.rs 230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
```

Commit packet: exact lease `notes/progress/2026-10-11-extrusion-copy-source-owner-audit.md`;
baseline `35e88c8113c9c6516e260170503bea753e4ede6`; changed dependency hashes
none caused by this worker, baseline comparison and integration revalidation
primary-owned; frozen unreviewed bounded research, parent OPEN; static reads
and hashes already run, no builds/tests. Proposed one-line message:
`research: distinguish extrusion copy origin from owned value references`.
Shared-record delta intentionally left to primary/curator: record that retained
HIR/Apply/Parent evidence identifies C's original source origin, refine the
remaining premise to copy-owned Value/reference construction, and preserve
source-prefix, semantic SCC, scanner correspondence and inference gates OPEN.
No shared record changed.
