# Nested lexical return: required sharing and actual Value references

Date: 2026-10-11
Status: independently reviewed bounded source/algorithm bridge.
Original all-source/inference parent theorem: **OPEN**.
Compiler baseline supplied by the primary's inputs:
`330d5432aff4b1f9655d501e17a9eefb7e75e098`.
Ordinary Simple-sub reference: `9bae772624c23b52a93c1b226157e16898b4d9db`,
at `/home/momota1029/rust/simple-sub-reference`.
Exclusive lease: this file. Leaf; no other writes, delegation, tests, builds,
Oracle, executable probes, or Git commands.

## Frozen statement and scope

Question: does an ordinary supported source constructor require an actual
retained Value extrusion parent/copy pair to enter one SCC of references in
their values? The remaining bridge in the supplied reachability and
source-qualified notes concerns source-required dependencies, rather than
another proof of the installed-bound level invariant.

This packet fixes one new source pattern:

```yulang
my outer = {
  my ancestor x = {
    my descendant y = ancestor;
    descendant
  };
  ancestor
}
```

The ancestor value is the function bound to `ancestor`, not its formal `x`.
The descendant returns that exact active lexical ancestor, and the ancestor
returns a use of the published descendant. These binder identities, their
scopes and the three Name occurrences stay fixed. There are no annotations,
applications, operations, shadowing, or additional recursive groups. Alpha
renaming is immaterial. `outer` supplies a containing block; assume no unrelated
module definition named `ancestor` or `descendant`.

Bounded claim, quantified over the ordinary constructor schedule for this
fixed LocalSource shape: the required monomorphic ancestor handle survives the
descendant's generalization/use. Actual capture and fresh reconstruction
retain it. The literal return dependency becomes a recursive Value payload
cycle among equal-level rows after the identified ordinary replay steps.
None of these Value constructors allocates a retained extrusion parent/copy
pair. Thus this pattern is not a witness of the existential parent/copy SCC
claim, and its lexical ascent does not establish the missing upward payload
edge for an already retained pair.

Claim class: **bounded source-to-algorithm correspondence and constructor
characterization**, independently reviewed with two wording repairs. This is not an
established all-source theorem, a source counterexample to intrusion, a full
semantic equivalence theorem, or an executable acceptance claim. In particular,
the existence/nonexistence and adequacy questions for all supported sources
remain OPEN.

Operational hypotheses: use the ordinary private native candidate source
route, starting from its fresh session; source identities and allocations
succeed; the named action admissions and worklist children complete normally.
No injected payload, reused failed state, test adapter, or synthetic family
edge is substituted. These hypotheses delimit the static trace; they do not
assume that a required source handle is retained. Its actual retention is
derived below. Global progress/termination and completeness of every replay
route are not conclusions of this packet.

## Authority and first source rule

Exact authority:

- `notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source
  behavior”, “Proposed source-to-solver seam”, and “Implementation checkpoint”.
  A nested helper mentioning an active ancestor uses that ancestor's one open
  monomorphic root. Publication subsequently uses the existing local boundary.
- `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation
  and compiler responsibility” and “Value-reference SCC clarification”. Only
  actual references form edges; genuine extrusion provenance qualifies pairs.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–3,
  “Evaluation”, and “Authority and integration”. Preserve native generation,
  propagation, levels, extrusion and generalization and the genuine Call,
  hygiene, soundness and principality gates.
- `rules/compiler-engineering.md`, “Natural compiler behavior and
  proof-obligation economy” and “Deterministic Simple-sub inference”;
  `rules/design-authority.md`, “Authority order”; `rules/research-lab.md`,
  “One semantic baseline, explicit dependency invalidation” and “Evidence
  quality and stopping unproductive loops”; `rules/git-concurrency.md`,
  “Disjoint-file mode”; `rules/agent-orchestration.md`, “Proof delegation and
  decomposition” and “Model routing and Astra escalation”.

The first decisive source constructor is HIR `Work::Initializer` at
`crates/yu-hir/src/module/local_source.rs:329–362`. A parameterized local
function temporarily publishes its own `HirLocalId` before its parameters and
body. The nested descendant initializer starts with this ancestor entry still
in the lexical stack. Identifier resolution at `:637–647` therefore resolves
its body Name to the **ancestor local identity**, not the descendant or `x`.
Descendant publication restores only the descendant initializer's additions
(`:366–373`); the ancestor remains active. The final descendant Name resolves
to the now-published descendant. Block restoration is at `:819–829`.

For comparison, deleting `x` to form
`my ancestor = { my descendant y = ancestor; descendant }` changes the first
constructor: `count == 0` creates no temporary local self binder. With the
fixed no-same-name-module context, the inner ancestor Name is `Unresolved`;
candidate Name scheduling accepts only module, parameter and resolved Local
forms (`candidate_source.rs:375–388`) and rejects that resolution. This is the
current carrier boundary, not a new language restriction. The authoritative
local-self document explicitly leaves zero-header lambda-valued initializers
and general value self-initialization outside its completed parameterized
slice. No inference conclusion for those forms is adopted here.

## Required dependency from ordinary Simple-sub

Use the pinned reference's actual terms as the algorithmic comparison:

```text
let outer =
  let rec ancestor =
    λx. let rec descendant = λy. ancestor in descendant
  in ancestor
```

Both local functions are translated with recursive-let binders, consistently
with the selected parameterized-local source rule. The unused descendant self
binder is harmless; this translation adds no occurrence of it. The reference
is an independent algorithm/storage baseline, not an oracle for all Yulang
effects or public source behavior.

`Typer.scala:48–55` introduces the recursive placeholder at `lvl+1`, types the
initializer with that same monomorphic placeholder in the context, then
constrains the initializer below it. `Var` instantiates its context scheme at
`:62–63`; a `SimpleType` instantiates to itself at `:205–207`. Therefore the
descendant body **must use the original ancestor placeholder A**, even though
that occurrence is in a deeper let. Lexical nesting does not generalize an
active monomorphic ancestor.

With outer's initializer at level 1, A and formal X have level 2; descendant
placeholder D and formal Y have level 3. The emitted reference constraints
before descendant use are:

```text
Function(Y, A) <: D
PolymorphicType(boundary=2, body=D)
```

The reference's descendant use calls `freshenAbove(2,D)` at level 2
(`:166–185,201–202`). It memoizes D and Y jointly as fresh D* and Y* at 2.
On the Function result A, `A.level <= 2` stops traversal and returns A itself.
Its later mutable bounds remain visible. It therefore restores:

```text
D*.lower contains Function(Y*, A)
A.lower contains Function(X, D*)  // enclosing ancestor initializer
```

Both structural installations have fields no higher than their receiving row;
the reference's actual constrain guards at `:115–120` need no extrusion.
The actual reference payload cycle is A → D* → A through those Function
results. Neither generic instantiation nor this cycle creates an extrusion
event. The reference has no retained-parent registry or intrusion consumer.

This establishes what this source/algorithm pattern requires: the original A
must remain shared through descendant use, including the ancestor Function
bound that arrives **after** that use. It does not require an identity between
original D and fresh D*, or between A and a nonexistent extrusion copy.

## Actual Yulang construction, levels, owners and edges

Unless otherwise stated, Rust locators are in `crates/yu-solver/src/`.
The source scheduler begins at 1 and increments only Block initializers;
Lambda and its body preserve the traversal level
(`candidate_source.rs:251–298`). Level maps initialize before admission at
`:532–541`. Fix these actual rows:

| Row | Source owner | Level | Relevant payload at this stage |
| --- | --- | --- | --- |
| A | ancestor initializer Lambda | 2 | initially empty |
| X | ancestor formal `x` | 2 | empty Value bounds |
| B | ancestor body Block result | 2 | initially empty |
| D | descendant initializer Lambda | 3 | lower Function(Y, effects, N) |
| Y | descendant formal `y` | 3 | empty Value bounds |
| N | ancestor Name in descendant body | 3 | direct lower A |
| J | final descendant Name in ancestor body | 2 | receives fresh descendant use |

1. `Work::Initializer` keeps A in `active_initializers` while it visits the
   descendant initializer (`candidate_source.rs:294–298`). The ancestor Name
   emits `Action::Link(A,N)` at `:381–385`, whose executor admits A <: N at
   `:657–661`. Native row/row admission selects N's direct lower side because
   2 < 3 (`candidate_extrusion.rs:815–830`). Physical insertion gives **N → A**.
   It allocates no copy and retains no parent event.

2. Descendant Lambda admission constructs the four-port positive Function
   from actual Y, body N, argument Effect and return Effect handles
   (`lib.rs:11233–11362`). It admits Function(Y,effects,N) <: D. Value ports
   Y and N already have level 3; structural extrusion at D's target 3 returns
   them unchanged (`candidate_extrusion.rs:83–103`). D's actual lower payload
   gives **D → Y** and **D → N**. Effect fields remain in the real Function.

3. Descendant `Install` stores `LocalScheme {root=D,boundary=2}`
   (`candidate_scheme.rs:1315–1334`). Installation is not a reference or a
   fresh allocation. The final descendant Name emits `Action::Local` at use
   level 2, not another open-initializer link. `route_candidate_local_run`
   captures that live root at its stored boundary (`:1358–1380`).

4. Capture classifies D,Y,N local because their levels exceed boundary 2;
   A is shared because its level equals 2 (`:300–326`). It captures D's actual
   Function and N's actual lower A (`:566–621`), and stops expanding shared A
   (`:569–570`). Fresh preparation maps D,Y,N jointly to D*,Y*,N* at level 2
   and maps A to **A** (`:1008–1021`). Function rebuilding uses the same joint
   remap (`:1141–1157`). The captured side owner is restored at
   `:1227–1266`, giving:

   ```text
   D*.lower contains Function(Y*, effects*, N*)
   N*.lower contains A
   ```

   Thus **D* → Y***, **D* → N***, **N* → A** are actual restored references.
   A's current empty payload is not frozen into a new variable or copied.
   Later A payload additions remain reachable through that exact A handle.
   `prepare_candidate_fresh_use` calls fresh allocation, not
   `retain_extrusion_parent`. D*/D and N*/N are not retained extrusion pairs.

5. After bound restoration, the Local cursor admits D* <: J
   (`candidate_scheme.rs:1500–1519`). Equal-level admission stores J as an
   upper row on D*: **D* → J**. The opposite bound already present is the
   restored Function(Y*,effects*,N*). Native replay requests that Function
   below J (`candidate_extrusion.rs:763–802`), and its executed Value child
   installs it in J's lower payload: **J → Y*** and **J → N***.

6. Block finishing uses the Group recipe J <: B
   (`candidate_source.rs:459–467`, `shadow_apply.rs:1327–1330`). Equal-level
   storage yields **J → B**. Replaying J's lower Function against that new
   upper B installs it in B's lower payload: **B → Y*** and **B → N***.
   Ancestor Lambda admission then installs Function(X,effects,B) below A:
   **A → X** and **A → B**.

Contracting the intervening immutable Function nodes gives the row path
**A → B → N* → A**, with all three row levels 2. In the literal graph, the
A → B and B → N* segments traverse owner-to-Function-to-Value steps,
including Function(Y*,effects*,N*) stored under B; N* → A is a direct row
reference. Other projected edges D* → J → B and the Y* argument
references remain real; they are not needed to close this path. Original N at
3 still points to A, and original D at 3 still contains Y,N. A's payload
reaches the fresh returned descendant shape through B, rather than retaining a
reference to original D. This distinction implements the selected descendant
generalization/use.

The two replay consequences above are not inferred merely from stored lists.
`candidate_insert_bound_with_evidence` retains the bound's admission origin
before physical insertion (`candidate_extrusion.rs:445–471`;
`candidate_effect.rs:420–435`, `candidate_context.rs:2814–2864`). Capture retains
the lower Function's evidence, and fresh restoration transports it with the
same side and owner (`candidate_scheme.rs:1227–1266`). Each newly admitted
upper J or B has its ordinary owner origin. The lower/upper pair therefore
has the actual fibers enumerated by `candidate_context_begin_replay`
(`candidate_context.rs:2911–2987`). That operation queues its concrete Value
task at `:3058–3101`; the outer worklist owns completion (`:3110–3123`). This
identifies activation and consumption owners for this finite trace, while
leaving their global completeness and progress theorems unproved.

Every listed Value structural dispatch receives Value ports at its own level
or below. Fresh restoration reinstalls the listed mapped ports. Consequently
none of these steps reaches the greater-level branch that actually allocates
a Value copy and retains its parent (`candidate_extrusion.rs:104–124`).
This is an explicit constructor calculation for this source, not another
universal level-rank proof. Effect extrusion/metadata are separate and do not
turn fresh Value rows into extrusion descendants.

## Dependency meaning versus literal graph identity

The source-required ancestor is preserved literally as the shared A in
N*.lower. The native administrative Name and Block rows subdivide the
reference's dependency through inequalities; they do not replace it with a
new ancestor. At the Value constraint level after fresh restoration:

```text
A <: N*
Function(Y*,N*) <: D* <: J <: B
Function(X,B) <: A
```

These are a direct projection of the owning emissions/restorations above,
with the real Effect slots left present in the implementation. Covariance
of the Function result and transitivity imply
Function(Y*,A) <: B and Function(X,B) <: A, the ordinary reference's returned
descendant constraints when its descendant-use root is B. This local Value
calculation explains the dependency being represented. It does not assert
principal schemes or equivalence of the full Yulang judgment by erasing
Effect ports. No independent marginal witness is selected for argument and
result: X,Y*,A,B are the single jointly fixed constructor handles.

Publishing the ancestor at boundary 1 and using it in the final outer block
captures these level-2 local rows together. Its level-1 use freshens the
recursive structure with one joint map; that allocation likewise creates no
retained Value extrusion parent event. Detailed full outer export and complete
Call are outside this packet. The ancestor's required monomorphic identity
during its initializer is established at the earlier shared-handle seam.

The SCC consumer follows both actual bound sides and the contained Function
ports (`candidate_intrusion.rs:390–413,445–468`). It can therefore see the
constructed A/B/N* cycle. Pair qualification independently enumerates actual
retained extrusion events at `:477–491`. It cannot equate D* with D, or N*
with N, by calling them a parent and copy: the emitting constructor never
retained those events. The pinned Scala reference also freshens this cycle
without extrusion. The literal SCC and the absent parent/copy qualification
are compatible with this source's required dependency.

## Remaining obstruction and economy audit

This pattern supplies a genuine source-required lexical self dependency and
locates its actual surviving handle. It removes this pattern as evidence for
a missing upward Value extrusion reference. It does not establish the
universal semantic bridge S in the supplied reachability note or refute the
existential question for all supported sources.

The precise remaining premise is a source-qualified dependency **across an
actual extrusion event**, where selected source meaning requires the original
higher-level retained parent to remain in the lower-level copy's payload or
requires another independently owned level/equality transition. The new
nested return alone supplies neither: its crossing operation is ordinary
generalization/use with an older monomorphic shared anchor. An example which
only labels fresh-use rows as extrusion copies misses the creation owner.

The previous level-rank proof and the Apply-source trace already left S open.
Under the existing economy audit, S is class A/B to the extent needed for
correctness and natural inference; it cannot be relabeled optional. An
arbitrary family-SCC converse is class C without a source requirement.
Reconstructing extrusion parent identity from lexical ancestry or freshness
would be class D debt and contradicts the existing retained creation fact.
This packet instead inspected the phase that knows the binder and the exact
fresh-use sharing map. It adds no semantic layer, certificate, source limit,
or proposed production change. Another copy of the rank argument is not the
next evidence.

Next action: pin a source construction that actually exercises extrusion and
its required approximation/identity meaning before another attempt to close
the all-source/ordinary-inference gate.

## Checks, dependencies, resources and omitted verification

Commands used: bounded `cat`, `sed`, `rg`, `head`, `wc -l` and `sha256sum`,
plus the one leased-file patch. Static owners inspected: HIR lexical
publication/resolution, source level/actions, native Lambda and Group
admission, capture/fresh restoration, replay activation and SCC qualification,
and the pinned reference's actual constructors. A guessed `spec/` path was
absent; no independent specification under that path was available. Required
source sharing instead comes from the exact Authoritative local-self document
and its real HIR/scheduler owners. No parser execution or source acceptance
check ran. No executable probe, test, build, Oracle, measurement sample,
child job or Git command ran.

Initial policy/input reads used up to four lightweight shell calls in
parallel; later source reads were bounded and sequential. Zero heavy compute
processes. CPU/RAM peaks and total wall time were not measured; no numerical
per-leaf allocation was supplied. The primary retains verification ownership.
Requested routing: normal Sol/high proof leaf; registered `prover` omits pins
and project defaults request `gpt-6.1-sol` / `high`. Observed runtime model and
effort metadata: **unknown**. No override, Astra run or hot reload is claimed.

The artifact trailing-whitespace search found no matches (exit 1); final
rehash found no direct dependency changes. Source and frozen-input SHA-256:

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference/shared/src/main/scala/simplesub/Typer.scala
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
39c64235bf61ebeeae18667eed527f784d2f9eb2713f4b91d9cbb7ab7d2afa8a  notes/theory/2026-10-11-value-parent-copy-reachability-proof.md
d73496fc376a9970d3a72e49208c3857e885b18b5ab2de074bc2cceae81a8a76  notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md
```

The Rust/reference hashes match the supplied notes' source snapshots. This
leaf changed no dependency. Baseline/ref identity is supplied by the primary's
frozen inputs rather than independently queried through Git. Full source
semantic correspondence, soundness, principality, complete Call, effects and
protection hygiene, abnormal-state reuse, public publication, zero-header
function-valued recursion, and all-source replay progress remain unverified.

## Commit packet

- Exact leased path: `notes/theory/2026-10-11-source-required-value-parent-copy-cycle.md`.
- Baseline SHA: `330d5432aff4b1f9655d501e17a9eefb7e75e098`;
  reference `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Dependency changes by this worker: none; hashes above pin inspected inputs.
  The current accepted parent-copy clarification is the supplied snapshot,
  not a new decision made here.
- Review status: compiler-referee reviewed research-only bounded bridge; its
  graph-path precision finding is closed. Parent theorem OPEN; no qualifying
  retained Value parent/copy SCC witness.
- Checks already run: static owning-source/algorithm comparison, final
  dependency hashes and artifact trailing-whitespace search (no matches).
  No executable verification or independent certification of source execution.
- Proposed checkpoint message:
  `research: trace required ancestor sharing through descendant freshening`.
- Shared-record deltas left to primary/curator: record the local source bridge
  for the fixed nested-return pattern; distinguish a shared older ancestor
  from fresh-use and real extrusion identities; retain the all-source and
  ordinary-inference gate OPEN with required meaning across a real extrusion
  event as remaining evidence. No shared record was edited.
