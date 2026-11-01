# R180 source correspondence — paused for constructor-owner admission

Status: STOPPED_SOURCE_TO_LOGICAL_GAP at revision 6, research evidence only; no App admission or
parent inference-soundness theorem is established.

## Revision 6 narrow charter audit — rigid scopes and retained identity

Contract SHA-256:
`5f6993f5ecfa977b3fac347ff78ea31c3b953e76c98b58af98ed3a4d08d40055`.
The ACK-only gate authenticated the four supplied artifacts (4/4) and strictly
counted 23 distinct direct-input rows, each with a full valid 64-hex digest;
all 23/23 recomputed hashes matched, with zero mismatches. No semantic owner
contents or output edits occurred at ACK. After primary read authorization,
the sole new source content read was
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§19–20,
lines 500–570, through a section-filtered read. No other owner was opened.

Section 19 (lines 515–534) records the user's rejection of narrowing a generic
operation arm's local type binder from selected Int call sites. The arm checks
at one fixed family instance; operation-local binders open as rigid names;
checking is uniform before instantiation at the actual request's retained
map. Captured/shared constraints stay shared and arm-local witnesses retain
their inner scope. The source rule cannot gain authority from
`ReachSel => OpCompat` alone. The source expressly leaves the complete generic
arm inference rule, effective scoped solving and principal template theorem
open.

Section 20 defines a substantive source typing choice: existential request
opening is essential. At a fixed known family instance rho, one use
instantiates operation-local beta once, and the existential request packet
contains payload, raw continuation, profiles/evidence, K,D and all latent
dependencies (lines 538–550). A dependent J belongs inside the same packet.
`Pack_s` records the existing witness and creates no new instantiation.
Elimination opens fresh rigid names and checks one uniform arm with captured
environment fixed. A caller-private equation remains retained jointly but
cannot become a rigid-arm checking assumption (lines 550–556).

The pack/unpack cut transports the same witness subject to existing primitive,
store and raw-suffix premises. Payload, continuation, profiles and dependent
views travel together; aliases and resumptions retain that witness. Fresh
proof names do not create independently solvable instances. Dependent result
or stored roots retain joint binder correspondence. These are scope and
identity obligations on the existing witness and its transport. They are not
an existence proof for an inferred App payload (lines 558–570).

Neither selected section defines an App descriptor constructor, a map from
the complete typed Call image into `Logical.descriptors/interfaces/viewMeaning`,
an inference-solution assignment/joint-witness readout, or an introduction for
`LocalAdmissions.logical`. They therefore preserve, rather than discharge,
revision 5's exact source-to-Logical bridge. This bounded conclusion follows
from the complete selected sections. It is not a claim that all charter
sections or all repository sources lack such a supplier. No further unpinned
owner was needed or read for this narrow result; the referenced operation
instance §7 and existing primitive/store/raw-suffix premises were not expanded.

Claim class: authenticated source-authority characterization. No theorem or
counterexample was constructed, no assumption was reclassified as a proof,
and no previously selected meaning was changed. Recommended next action
remains the constructive original typed Call-to-Logical/admission bridge,
with whole-packet identity and original rigid/shared scopes retained as
explicit invariants. Another request-packaging transport lemma would leave
that App-introduction premise untouched.

Checks/resources: successful section-filtered textual read and sole leased
handoff update, following successful exact hash authentication. No oracle,
experiment, tests/builds, Rust, Lean/Lake, runtime, scratch/cache/environment,
delegation or Git mutation occurred. No heavy process; cumulative CPU/RSS
were not measured. No new source owner or semantic consumer was inspected
beyond the selected charter sections in this revision.

Commit packet: exact sole changed leased path
`tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`; primary
baseline `b9d831177bb8a6d7fb95950f263781fbf851d342`; no dependency byte
changes; 23/23 direct input and 4/4 ACK artifact hashes matched; fresh
independent review pending. Proposed message:
`Record R180 rigid request scope and App admission distinction`.
Shared-record deltas left to primary: source lane STOPPED; R6 charter audit
complete within §§19–20; App source-to-Logical bridge and parent remain OPEN.
Writing is frozen after this revision-6 disposition.

## Revision 5 final disposition — what the typed core and joint law prove

### Authentication and read scope

Contract SHA-256:
`c733a9bc7d19efc4a98cae52f9617ce2d84cf30c1ef60938d3c37d48b6fac4b5`.
The ACK-only gate verified all four exact supplied artifact hashes and 22
distinct direct-input paths, each with a valid full 64-hex digest and matching
recomputed bytes (4/4 artifacts, 22/22 rows, zero mismatches). No owner
contents or handoff edits occurred during ACK. Subsequent primary read
authorization admitted only typed-core §§2,3,9 and linking §3, plus the already
pinned call sites as needed. A section-filtered read printed exactly those
selected sections with line locators. No unpinned owner was read or hashed.

### Source definitions versus retained premises

The admitted
`notes/design/2026-10-02-typed-computation-core-elaboration.md:55`, §2, takes
the existing judgments `Gamma |- d : Value(A)` and
`Gamma |- c : Comp(E,A)` as its declarative input. Its input is already a
finite source derivation graph containing typed introductions/eliminations,
parameter roles, typed paths, Flow/receipt correspondence, and K,D under one
assignment nu (lines 57–85). A raw occurrence does not itself determine
which source derivation applies (lines 95–107). Thus this is not an owning
App-introduction rule converting an inferred solution into that typed
derivation.

Typed-core §3 defines the structural V/X translation. The exact Call equation
at lines 133–135 is callee execution, inert whole-argument Delay, then
ExecuteCallable. Lines 151–178 define the complete declared result consumer,
receiver activation/receipt, source-selected entry and operation native-return
delimiter. These identify the actual whole computation that the original
App's descriptor/profile interpretation must describe. They preserve the
distinctions needed by revisions 1–4; they do not define a finite list of
descriptor writes at the Lean App endpoint or construct local logical
admission.

Typed-core §9 retains `J_arg`, `J_body` and `J_call` separately (lines
914–926). The complete J_call is the relational image of the actual producer's
ExecuteCallable, parameterized by the whole argument, environment and current
configuration (lines 959–976). The body alone or a union of support rows is
insufficient. The symbolic complete image remains an inference obligation
(lines 988–996). The semantic containment argument at lines 1087–1108 is
conditional: checked challenges are admitted by the actual description, and
for each such challenge actual observations lie inside the checked bound.
Satisfaction of the actual description is a premise of its conclusion.
Port directions explain how structural rules could prove those inclusions;
they do not prove the inclusions themselves.

The source states the remaining boundary directly at lines 1110–1119:
construction of a finite symbolic complete ExecuteCallable image and its
higher-order/store challenge relations remains a source gate. Executable
linking of finite supplied resolved interactions does not generate arbitrary
source templates or unknown caller domains. This admission prevents treating
the operational equation or direction classification as the missing complete
semantic App typing theorem.

The admitted
`notes/design/2026-10-02-parametric-component-linking.md:107`, §3, supplies an
algebraic preservation law. It assumes all external/shared/dependency
coordinates are retained, chooses admissible substitutions and required
identity transport, and alpha-renames genuinely local blocks to be disjoint
from one another and the client relation (lines 112–158). Its equality

```text
exists Z_1,...,Z_n. (H and conjunction_i F_i^sigma)
  = H and conjunction_i (exists Z_i. F_i^sigma)
```

is pointwise at the same joint external assignment. The proof restricts one
joint witness or combines disjoint local blocks. It does not prove that either
side has a satisfying witness, does not choose source-generalizable binders,
and does not create the required identity transport. Lines 166–173 explicitly
leave representability, effective solving and source instance completeness
open. Its source-provided Int/Bool shared-witness example (lines 175–187)
shows why independently hiding a shared witness changes a contradictory
conjunction into two satisfiable parts. This is a textual failure condition
for an invalid transport, not a discovered admitted Yulang counterexample.

### Exact bounded gap at the unchanged App consumer

Combining the authenticated source clauses yields a concrete sequence of
obligations:

1. Actual child Code derivations and Application origins construct the same
   Check_c and whole inert argument (source-input construction §3.4).
2. The actual typed-core Call equation determines the complete original
   CallView interpretation; it includes the actual provider's entry, body and
   designated result consumer with native return delimiters.
3. A source-to-Lean interpretation must translate that same complete original
   descriptor/profile into the App endpoint's Logical.descriptors,
   Logical.interfaces and viewMeaning, while transporting the same inferred
   solution's assignment and joint witness through the complete preceding
   decoded telescope.
4. That owning interpretation must establish the unchanged
   `admissions.logical state binder .viewLogic data` relation. Only then does
   `admitted_scoped_iff` make the genuine scopeCandidate usable at the App
   binder. The local `.descriptorFormation` atom and subsequent value and
   computation checks are separate consumers.

Steps 1 and the operational content of 2 have authenticated source
constructions. Steps 3–4 are the exact missing introduction/interpretation
bridge in the admitted material. No displayed source equation maps the
complete typed Call interpretation to the original Lean descriptor-write list
and owning local admission under this same solution. The typed derivation,
semantic actual-description satisfaction, admissible transport and shared
solution are retained assumptions where the admitted results use them.
Defining a Logical record with free fields or assuming its local admission
would leave this bridge untouched.

Claim class: bounded source/consumer characterization and an unclosed
formalization bridge in the authenticated sections. This is neither a proof
of whole-language soundness nor a counterexample, nor a global claim that no
supplier exists outside the admitted scope. No new language decision is
selected. A faithful introduction theorem would require formalization of the
already selected original Call meaning; any genuinely new semantic rule would
need primary design-authority adjudication instead of being invented here.

The selected sections refer to charter-controlled parameter roles, rigid
binders and request packets. Those remain their stated independent inputs;
this lane does not reinterpret them or expand into charter sections. The
bounded conclusion above requires no further owner read. In particular,
linking §7 is explicitly outside this packet's §3 read scope and was not read
to manufacture complete source-template construction.

Recommended next action: make step 3–4 the constructive proof packet: define
the faithful interpretation of the original typed Call derivation into the
existing App Logical payload and prove its original owning admission, with
same-solution and full-telescope equations visible in the theorem type.
Start from the actual whole Call image and genuine child derivations, then
use linking §3 only for its already justified transport premises. Repeating
the algebraic projection law or syntactic Check_c induction alone cannot
discharge that introduction.

### Checks, limits and commit packet

All completed hash/read/write commands exited successfully. Verification was
strict digest authentication and direct section/consumer inspection. No
independent executable oracle, theorem checker or test was run. No Rust,
Lean/Lake, Cargo/build/runtime, scratch/cache/environment, child delegation or
Git operation occurred. One source lane used only lightweight reads and this
sole leased write; exact cumulative CPU/RSS were not measured. Other App
checks, finite Checking, complete Call/Build and the parent inference theorem
remain unverified/open in this lane.

Commit packet: sole leased changed path
`tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`; primary
baseline `b9d831177bb8a6d7fb95950f263781fbf851d342`; no dependency bytes
changed; R5 22/22 direct hashes and 4/4 ACK artifacts matched before reads;
fresh independent review pending. Proposed message:
`Record R180 typed Call interpretation and logical admission gap`.
Shared-record deltas intentionally left to the primary: STOPPED source lane,
bounded source-to-Logical bridge open, parent OPEN, and no theorem/counterexample
or production promotion. Writing is frozen after this revision-5 disposition.

## Revision 4 final source-to-consumer mapping

Contract SHA-256:
`d8cac3e7e54d4d45931e0e4f4f95c9b2a969fda6143d9228752d2c8d40cf056a`.
The ACK-only gate authenticated contract, activation and both frozen handoffs
(4/4), strictly parsed 20 distinct direct rows with full 64-hex digests, and
recomputed 20/20 matching file hashes before read authorization. No input byte
change was observed at that gate. Subsequent primary authorization permitted
the two newly admitted source owners and necessary already-pinned consumers.

### Constructed source premises

The admitted `notes/theory/2026-10-07-call-input-construction-proof.md` §3 fixes
one original resolved binder graph, source, scopes, provider roots and
`xi=(nu,K,D)`. Its telescopes retain actual captured certificates, dependencies
and ordered binding/rebinding origins. They are not lists of independent
endpoint witnesses. §3.1 distinguishes inert Data from executable Code;
Carrier-Delay retains the actual whole-argument reification origin and lexical
references without performing entry or execution.

At §3.4, Code-Call requires:

1. `Code(E,cf,Comp(Ef,A_f);qf)` and
   `Code(E,ca,Comp(Ea,A_a);qa)`;
2. the actual Application/Gen-Call-0 origin with dependent `F_c,R_f`;
3. the actual whole-argument `ReifyOrigin`, from which
   `t_arg = Carrier-Delay(qa,o_arg)` is constructed;
4. the original complete Call-result interface and result port;
5. actual emitted `VIncl-origin(A_f,F_c)` and
   `WholeArgCompatible-origin(J_a,CarrierContract(F_c))`;
6. the dependent original-provider suffix, original roots/scopes and all
   operand incidences.

The resulting `Check_c` bundles those same objects. Its erasure is callee
execution followed by inert construction of the entire argument and
`ExecuteCallable(f,t)`. This gives an authentic syntactic operand-origin
construction within that grammar. §3.4 explicitly excludes a satisfying
assignment, result-inclusion truth, receipt authority, actual-provider inlet
acceptance and completed semantic Call typing. Bare Gen-Call-0 alone does not
construct Check_c. §4's source-induction theorem constructs these certificates
without a satisfying assignment or execution. Its whole-substitution equation
`theta(Check_c) = Check_(theta(c))` applies one legal sorted substitution to
the entire original graph; arbitrary semantic substitution still requires the
original interpretation's own lawful action.

The admitted theorem-C document
`notes/design/2026-10-04-source-generated-callback-structural-theorems.md`
§§2.1–2.4 retains decorated source/kernel witnesses as inputs and generates
Call from callee, whole inert argument, actual invocation/receipt, entry, body
and designated consumer. Its shared logical hiding has the explicit form
`P_G(X) = exists Z. F_G(X,Z)` at one external assignment. A local is bound once
around the whole relation; shared imports, lexical roots, source identities
and live K,D coordinates cannot be hidden per segment. These constraints are
compatible with the one-tuple/native-partition requirements authenticated in
revisions 1–3. They do not construct the particular inference solution or
its original local logical-admission relation.

### Exact Lean consumer and remaining bridge

The authenticated `OriginalSourceGeneration.lean:111` App branch emits
`.existsE ⟨site,.viewLogic,0⟩` around the App rule, whose local atoms include
`.descriptorFormation site context [callee.site,argument.site]`, whole-argument
compatibility, complete Call certificate, source Call incidence and callable
image. Its value check uses `callee.returnedValue` as lower endpoint and the
App's `.descriptor` as upper; its computation check connects App
`.callableImage` to App `.synthesis`. It keeps both original child source rules.

The authenticated `OriginalSourceEnvironment.lean:249` defines the required
Logical packet with descriptor writes, interface writes, view interpretation,
one assignment eta and one joint witness. `Decoded.logical` at line 346
applies the descriptor writes to the existing assignment and replaces eta and
joint witness together; it does not derive those fields from a Check_c.
`LocalAdmissions` at line 599 is the unchanged independent owning-rule
relation. Its `DataAdmitted` logical case at line 608 requires both the actual
binder-kind equality and `admissions.logical state binder kind data`.
`scopeCandidate` and `admitted_scoped_iff` at lines 644/648 retain the actual
environment event path and reduce scoped admission to that same local
relation after decode. They do not produce local logical admission.

Consequently the needed bridge has identifiable operands: the authentic
Code-Call/Check_c objects must supply the App endpoint's descriptor/interface
writes and view meaning, under the complete preceding decoded telescope;
their eta and joint witness must be the same inferred solution's objects;
and their owning introduction must establish that unchanged local admission.
The syntactic Check_c construction establishes none of those semantic
equalities by itself. The theorem-C joint projection also cannot replace them
with separate per-port existentials. This is a bounded source/consumer
characterization, not a theorem that the bridge is impossible or absent from
the unread original owners.

### First additional defining owners, kept unread

- `notes/design/2026-10-02-typed-computation-core-elaboration.md`.
  Exact admitted locators: source-input construction §3.1 identifies `T_D/T_C`
  with typed-core §3; §3.4 identifies the actual suffix's tags/ports with
  typed-core §§3,9 and the original producer declaration. The theorem-C
  document's "Governing source decisions" explicitly resolves that path;
  §2.1 takes its derivation constructors from typed-core §2. These are
  defining references for the retained original Call/entry/consumer meaning.
- `notes/design/2026-10-02-parametric-component-linking.md`, §3.
  Exact admitted locator: theorem-C document §2.4, "Complete bound denotation
  and logical witnesses", explicitly delegates its same-assignment/joint
  hiding law to this section. This is a later required branch when proving
  the complete-telescope/same-witness transport, not a replacement witness.

Neither additional file was opened or hashed. Recommended next action:
authenticate the original typed-core Call/entry/consumer equations first and
compare them against this exact Check_c-to-Logical bridge; authenticate the
linking law when discharging its joint-hiding transport. Retain the original
LocalAdmissions consumer and full same-solution quantifiers. Do not turn
syntactic origin retention into an assumed semantic introduction law.

### Read coverage, checks and commit packet

New revision-4 content: source-input construction §§3–4 (lines 121–420);
theorem-C document lines 1–210; exact searches and selected App/logical-packet/
admission definitions in already-pinned Lean generation/environment and
assignment-related locators in already-pinned interpretation. An initial
exact locator/link search covered the full two newly admitted documents,
including headings/references outside source-input §§3–4; no semantic argument
above depends on those out-of-section source-input references. No unpinned
document content was read. No theorem-C §4 proof or exhaustive all-constructor
audit is claimed. All findings above are textual source/consumer evidence;
there is no independent executable oracle or Lean theorem check.

No Rust, tests/builds, Lean/Lake, runtime, scratch/cache/environment or Git
operation occurred. Aggregate CPU/RSS were not measured; no heavy process or
additional worker was used. The full parent theorem remains OPEN.

Commit packet: exact sole leased changed path
`tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`; baseline
`b9d831177bb8a6d7fb95950f263781fbf851d342`; no dependency bytes changed;
20/20 full direct hashes and 4/4 ACK artifacts matched; independent review
pending. Proposed message: `Record R180 original Call origin and admission bridge`.
Shared-record deltas left to the primary: STOPPED disposition, exact typed-core
and linking-law dependency boundary, and unchanged parent OPEN. Writing is
frozen after this revision-4 handoff.

## Revision 3 final disposition — original source and relational owners

Revision-3 contract SHA-256:
`866c4c28ab923b311f6f6bc8b674ea721dd3350e80935646b34e81912be12b05`.
Before any new owner contents, a strict parser counted 18 distinct exact paths,
required a full 64-hex digest for every row, and verified all 18/18 current-byte
hashes. No dependency byte change was observed by those checks.

The primary admitted both the Call-interface construction and source-contract
documents. Their contents identify the next source/meaning boundary exactly:

1. `notes/theory/2026-10-07-call-input-construction-proof.md`, Theorem S
   §§3–4. Locator: admitted
   `notes/theory/2026-10-08-call-source-interface-construction.md:66`, §2
   "Inputs, and what the constructors newly produce". The latter explicitly
   takes the source grammar, actual registration/capture/parameter/Application
   origins, and actual child derivations from Theorem S. Its following clauses
   say a bare Gen-Call-0 record cannot manufacture the additional Application
   origins. The same admitted document §5 (locator line 346, seen by an exact
   in-file search) says construction uses Theorem S's actual derivations.
2. `notes/design/2026-10-04-source-generated-callback-structural-theorems.md`,
   theorem C. Locator: admitted
   `notes/design/2026-10-05-source-contracts-and-common-allowance.md:59`,
   "Governing sources"; §2.1, locator line 100, attributes its displayed
   relational operations to theorem C. Exact admitted contents distinguish
   independent primitive whole-tuple relation, conjunction on one shared tuple,
   original whole-tuple union alternative, capture-avoiding renaming of all
   incident operands, original scoped binding, independently specified
   constructor images (including Call), registered references and positive
   recursion by finite derivations. The independent primitive and owner/view
   kernel contracts remain inputs.

Neither additional owner was read or hashed. Their paths and references above
come only from the authenticated admitted documents. No conclusion about the
contents or completeness of those additional owners is made. Theorem S is the
explicit source-derivation supplier; theorem C is the explicit relational
operations supplier. The source-contract "Governing sources" paragraph also
lists coupled core, realization, certified transport, typed core and
compatibility documents; this lane has not read them or established that each
is necessary for the narrowly selected next step.

The accumulated admitted equations establish a bounded characterization:
native contextual injections preserve the complete dependent record and
constituent partition, while actual source/child origins and the independent
Call constructor interpretation are retained premises. They have not been
identified with the original App descriptor write under the same solution.
In particular, an actual Call constructor image is still independently
specified in source-contracts §2.1. A frame/readout does not supply an equation
equating that constructor's original interpretation with the App's
`.descriptorFormation` atom, its complete prior telescope, or its unchanged
`LocalAdmissions.logical` premise. This records the exact unadmitted source
boundary; it does not assert that the desired equation is absent in the unread
sources, or prove a specification gap or counterexample.

Recommended next action: authenticate and admit the two explicit source owners
above in a single bounded follow-up packet, then inspect their actual App/Call
derivation and interpretation equations against the pinned Lean consumers.
Retain same-solution and complete-telescope equalities as explicit targets.
Another descriptor readout or consumer iff calculation would leave the same
source-introduction premise untouched.

Revision-3 exact content/read coverage: admitted Call-interface lines 1–180;
an exact `rg -n` search in that admitted file and the admitted source-contract
file for theorem S/C and their related section references; admitted
source-contract lines 54–108. No broad repository search occurred. The
Call-interface lines 1–180 were read after the primary's explicit read/resume
instruction; a later correction said current state still recorded STOPPED.
The lane immediately disclosed the read to the primary and paused. It made no
new source read until subsequent primary resume authorization. This is not a
claim of uninterrupted state/receipt alignment. All read source files were
already authenticated under revision 3.

The revision-3 analysis is textual source evidence, not an executable
experiment or independent theorem check. No Lean consumer content was newly
inspected before stopping at the additional source-owner boundary. No theorem
or full constructor-to-Lean derivation was constructed. No Rust, tests,
builds, Lean/Lake, runtime, scratch/cache/environment or Git operation occurred.
No heavy process was run; aggregate CPU/RSS were not measured. All parent
inference-soundness cases remain open in this lane.

Revision-3 commit packet: exact sole changed leased path
`tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`; baseline
`b9d831177bb8a6d7fb95950f263781fbf851d342`; no dependency bytes changed;
18/18 full hashes matched before new content; independent review pending;
proposed message `Record R180 original source-constructor dependency boundary`.
Shared-record deltas intentionally left to the primary: STOPPED status,
additional Theorem S/theorem C owner admission, parent OPEN. Writing is frozen
after this revision-3 disposition.

## Revision 2 disposition — next constructing source owner

The primary sequentially admitted the incidence-construction owner and fixed
revision-2 contract SHA-256
`006e59a429c0bee035f3306eff401e1972e340683b16a6d546b18ce7687590d3`.
A second strict parser pass found 16 unique exact path rows, required a full
64-hex digest for every row, and verified 16/16 current-byte matches before new
content reads. The admitted incidence document's actual filesystem digest is
`7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`.
Its repaired-body artifact digest cited by the native definition remains
`e698ad0467a6986029f5f5d21ff3e0bf8a2cc836c9410f1fa0be4b717be915d2`;
these are distinct identities, not a failed equality claim. After the primary
recorded the fresh ACK, START receipt and RUNNING state, this lane read the
admitted incidence document.

The next required defining dependency is explicit in that document, rather
than inferred from a filename:

- §2 places the selected Name/capture/provider-field, Return/Result,
  designated consumer, Reify/Delay, Lambda/producer, Bind and Call envelope in
  `notes/theory/2026-10-08-call-source-interface-construction.md` §§2–6,
  including the finite registered monomorphic graph extension.
- §3.2 starts by requiring IF construction at each actual clause/source node
  under the selected IF definition. It attributes the contextual slots and
  complete Call constituent arrangement to the actual IF slot constructors.
- The admitted document's final dependency table identifies the IF construction
  file by SHA-256
  `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`.
  This is a cited identity only; this lane has not authenticated or read that
  additional file.

The incidence document itself exposes concrete contextual field injections in
§3.2: primitive fields map to `(prim-slot(alpha,m), v[m])`; operand fields to
`(operand-slot(n,j), v)`; root clause fields to
`(root-clause-slot(t,q), v)`; actual reference fields to
`(use-slot(v,t,m), z[m])`. It requires each injection to retain the full
dependent record, including providers, worlds, raw resumptions, future
interfaces, guards, licenses and original dependencies. Its declaration
placement is `j_decl(h) = ins_(t,q) o operand_(q,alpha) at pi_h`.

For an actual Call, §3.2 specifically retains distinct callee, whole carrier
hole, dependent actual-provider/current-world receiver, phase, result/future
and every declaration-arm slot. Alternative roots retain tagged clause
slots and complete witnesses; conjunction uses one shared tuple; Bind
retains the ordered dependent suffix. Thus selecting only the callee return
or only a per-port argument witness would fail the authenticated constituent
requirement. These explicit equations identify what a later bridge must
preserve. They do not identify the actual App's original descriptor endpoint
with that frame, or identify its tuple with the same inferred solution's
assignment and joint witness.

The lane stopped at this further unadmitted source-owner boundary. The first
recommended next action is sequential admission and authentication of the
explicit IF construction owner above. Its exact original placement and Call
equations can then be mapped to the pinned Lean consumer. No equation in that
unread owner is asserted absent. The incidence document also explicitly
retains source-contracts §2.1 and §3.4 as primitive/whole-transformation inputs;
their independently owning file,
`notes/design/2026-10-05-source-contracts-and-common-allowance.md`, remains
unread and may require a later exact admission when that branch is needed.
The current result is a source dependency boundary, not an App counterexample
or established formalization-gap theorem.

The actual original App descriptor write, `.descriptorFormation` interpretation
and `LocalAdmissions.logical` consumer were not newly content-inspected in
this lane before this next boundary. Consequently no constructor-to-Lean
derivation or same-solution/telescope equality is claimed. There is no free
descriptor parameter, circular admission assumption, Lambda reuse, per-call
witness, or substituted kernel in this result.

Revision-2 command coverage: strict row/digest authentication; read the revised
contract and admitted incidence document; update this sole leased handoff.
No further source owner was read. No Rust, tests/builds, Lean/Lake, runtime,
scratch/cache/environment or Git operation occurred. The source document read
was returned with output truncation, so this lane does not claim a complete
line-by-line audit of every constructor in §§3–7. The boundary above is
directly supported by the visible §2 and §3.2 clauses. No independent oracle
or executable experiment was used. Resource maxima remain unmeasured; no
heavy process was run.

Revision-2 commit packet: sole leased path is this file; primary baseline
`b9d831177bb8a6d7fb95950f263781fbf851d342`; no dependency bytes changed;
16/16 direct digests matched; independent review pending; proposed message
`Record R180 App formation source-owner dependency boundary`. Shared-record
delta for the primary is PAUSED_ADDITIONAL_OWNER under r2 and the exact IF
owner admission request. Writing is stopped at this revision-2 freeze.

## Preserved revision-1 handoff

## Objective, method and authenticated baseline

Objective: map actual source signature formation constructors and complete
constituent partitions to the original App descriptor write,
`.descriptorFormation`, and unchanged `LocalAdmissions.logical`, preserving
the complete prior telescope and the same inferred solution.

Baseline: `yulang3` at `b9d831177bb8a6d7fb95950f263781fbf851d342`, as pinned by
the primary's contract. Contract SHA-256:
`4d4b53059743cb19e36c08480c64c2ef59144cc7b10bbbcbb743992180afbffe`.
Before direct content reads, a strict Python parser counted all 15 input rows,
required a complete 64-hex SHA-256 per row, and recomputed every file digest.
Result: 15/15 matched. Hashing read bytes for authentication, without treating
them as evidence about document contents.

The lane then read the required process rules and the authenticated
`notes/design/2026-10-08-native-signature-formation-definition.md`. No other
direct-input contents or additional source owners were inspected.

## Exact source finding

The native formation definition §1 explicitly selects the native catalogues,
actual field injections, declarative support/license/attachment grammars,
certificate format and whole-family actions in
`notes/theory/2026-10-08-source-signature-incidence-construction.md` §§2–6.
It identifies that repaired mathematical producer by SHA-256
`e698ad0467a6986029f5f5d21ff3e0bf8a2cc836c9410f1fa0be4b717be915d2`.
The same section attributes correspondence and scoped consequences to that
producer's §§7–10. This is an explicit delegation of the constructing rules,
not an inference from a filename.

The definition's own §§2–4 constrain those rules:

- Complete port provenance precedes applicability; complete original
  constituent/field partition `Omega` is distinct from receiving registration
  `beta_r`.
- Primitive/local introductions retain their actual origin and independent
  law; operand/reference/scope/rename operations retain antecedent origins.
- Union, conjunction and operator results retain complete partitions on the
  original whole tuple, including empty or unselected contractual schemas.
- Conjunction and dependent Bind use one shared tuple. Recursive registered
  references produce graph edges and finite proof developments.
- Support, static license and attachment are independent indexed judgments;
  compiler construction is a separate implementation, not their definition.
- Original-scope hiding retains one whole hidden row, its entire incidence
  family and admission witness. Per-port existential witnesses cannot replace
  it.

These are authenticated preservation constraints. They do not expose the
selected producer's exact constructor premises or establish a constructor
equation for the App descriptor write. In particular, they cannot establish
the App's same-solution assignment, its telescope extension, or the unchanged
local logical-admission premise by themselves.

## First blocker and authority required

The selected constructor owner is absent from the 15 frozen inputs. The lane
stopped before reading it, as required by the contract. Therefore this result
does **not** claim a missing equation in that owner's contents; it records an
unadmitted defining dependency. No counterexample or semantic impossibility
has been established.

Recommended next action: the primary sequentially admit
`notes/theory/2026-10-08-source-signature-incidence-construction.md` with its
exact current full digest (checking against the source's declared repaired
producer digest above), freeze the revised contract, and obtain fresh hash
acknowledgements before resuming the constructor-to-consumer derivation. No
new language decision is requested by this admission. Any additional reused
Call/source-interface owner discovered there must pass the same admission
boundary before content reads.

## Commands, coverage and resources

Commands: contract read; one Python strict row/digest validation; reads of
`rules/research-lab.md`, `rules/design-authority.md`, `rules/git-concurrency.md`
and the native formation definition; creation of this sole leased handoff.
All completed commands exited successfully. No experiments, tests, builds,
Lean/Lake commands, Rust reads, compiler edits, runtime execution, scratch,
cache/environment creation, or Git mutation occurred. No independent oracle
or executable theorem check was used; evidence is the authenticated defining
document's explicit owner reference and its own preservation clauses.

One source lane, under its 600-second budget; no heavy process or additional
worker. Peak RSS and exact aggregate CPU were not measured. All other source
cases and the complete parent obligation remain unverified by this lane.

## Commit packet

- Exact leased changed path:
  `tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md`.
- Baseline SHA: `b9d831177bb8a6d7fb95950f263781fbf851d342`.
- Dependency hashes changed: none; all 15 frozen digests matched at startup.
- Review status: frozen for primary disposition; no independent review yet.
- Checks already run: strict 15-row/full-digest authentication only.
- Proposed checkpoint message: `Record R180 native constructor owner admission blocker`.
- Shared-record delta left to primary: record PAUSED_ADDITIONAL_OWNER and
  decide sequential admission of the explicitly selected incidence owner.

Writing is stopped after this handoff; no shared scheduling/authority file was
changed.
