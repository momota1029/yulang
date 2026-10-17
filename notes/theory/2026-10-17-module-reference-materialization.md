# Module reference materialization: an explicit environment completion

Date: 2026-10-17  
Status: **UNADOPTED candidate completion; original owner premise OPEN**  
Revision: 2  
Author: `/root/module_reference_materialization_proof`; no descendants  
Sprint: `module-reference-materialization-20261017`, revision 1  
Contract SHA-256: `8e3d43ac44ece28e056a2c49bb72c4a2e8fcc9679246d25c346aa4005d81dcc7`  
Baseline supplied by Luna: `20821b42d`; no Git inspection  
Original conditions closed: **0**  
Implementation / production authority: none

## 1. Parent and result

The fixed source is `my id x = x; my answer = id 0`. Keep the original
`B,X,xi=(nu,K,D),Delta_c,d_id,u_id` of
[original-generation §7.2(2)](2026-10-17-ordinary-call-original-generation.md).
The original declaration publication is available. The inspected original
rules do not specify the typed module environment used to elaborate this
same occurrence `u_id`, or a rule connecting that environment to the installed
publication entry. Consequently they do not derive `HINTRO-OWNER-u_id`.

The new result is a precise, constructive completion at that owner:
`ModuleEnv-Expose*` below. It forms a component's typed module environment
from actual publication and registration outputs, with exact dependent
restriction, before using resolution to select an entry. Under this
**proposed** rule the fixed source obtains a Published handle and its whole
allocation map. This is a substantive new environment rule, not just retained
metadata, and is not asserted to be an original rule. Its acceptance can
change the available source derivations. Erasure to the original unannotated
module judgment, and equality of original source admission, are unproved.

No genuine source-qualified counterexample to the original theorem is given.
The ordinary source domain, all ambient assignments, joint strategies, guards,
client constraints `W`, and F1/FK1's independent quantifiers remain unchanged.
Full source `Sig`, native interpretation `Phi_u`, registered root, Call,
N-Transport, soundness, principality and termination stay separately OPEN.

## 2. Original owners inspected and the precise missing premise

The selected Source Generalize definition adopts SRC §§3–5. Its relevant
constructors have the following actual conclusions:

| Original owner | Available output and remaining limitation |
| --- | --- |
| SRC §§3.1,4; Parameter/Name/Result/Lambda | Complete open declaration program and its rule operands, at genuine local `Sig`; no successful solver or runtime premise is introduced. |
| SRC §§5,5.1,5.3 | FinalRoot, whole component closure and installation of `Published(p_id,G_id)` at the declaration boundary. |
| SRC §3.1 Name | Restriction of an **existing** joint certificate; explicitly no introduction classification. |
| SRC §3.3 | Published/Family instantiation, Mono/Established introduction, Alias and Live are distinct owning rules with their actual operands. |
| SRC §5.3 | Later external Names see Published or an actual Mono instance according to the rule that created their handle. It does not identify that rule for this occurrence. |
| SRC §3.4 and SRC-J/GC | The client includes source-directed handles. Inversion recovers those inputs; it does not manufacture them from a raw resolved graph. |
| Call semantic-input realization §4.1, Lemma W | Import and capture restrict already typed binding certificates; rebind requires actual returned membership at the original world. This transports existing contracts, without selecting polymorphic instantiation versus monomorphic installation. |
| Selected IF-Use | Retains an actual typed reference under its original scoped substitution. A typed reference is its input, not a consequence of an untyped target identity. |

The source-family proof §§2–3 supplies the following original formation
outputs at the actual immutable boundary, conditional only on the same genuine
local rule signatures already required by the parent:

```text
P_id = Build(Parameter / Name / Result / Lambda at L_id)
a_id = original inert closure anchor, with its actual empty capture
r_id = FinalRoot(P_id) = complete unannotated synthesis root
C_id = {d_id}
(K_id,Q_id,N_id) = FixRetain(p_id,C_id,T,P_id,r_id,a_id)
G_id = ScopedClosure(p_id,C_id,T,K_id,Q_id,N_id,r_id)
publication installs module_environment[d_id] = Published(p_id,G_id).
```

The graph has `Resolve(u_x,d_x)` inside `L_id`, and
`Resolve(u_id,d_id)` in `answer`. The only module dependency is
`d_answer -> d_id`; there is no return edge. Thus `C_id` and `C_answer`
are distinct, with `C_id` dependency-prior. This is a calculation on this
finite graph, not a theorem about every SCC plan. It excludes the registered
intra-`C_id` Live case at `u_id`; it does not exclude an owning Mono import
or rebind for this expression in some as-yet-unspecified source judgment.

The exact missing premise is:

```text
the actual source module elaboration exposes the previously installed typed
entry at d_id to answer's RHS, with its whole constructor and dependent
certificate preserved, and uses that entry to introduce the handle at u_id.
```

This is one owner application, not an assumed whole-program typing theorem.
The publication and resolution premises alone have no rule with this
conclusion in the selected inventory. The environment word in the publication
formula is insufficient: it does not establish what occurrence elaboration
does when it leaves the declaration owner. Conversely, Lemma W proves a valid
transport **after** the certificate and source telescope constructors exist.

These two methods leave the same premise untouched. The next sections change
method to a reviewable completion rather than restating the prior conditional
Published theorem. Searches of the selected IF and environment references did
not identify an applicable original module rule; this is a bounded inventory
statement, not a global nonexistence theorem.

The additional syntax references supplied by Luna do not fill this gap:
`syntax-reference/en/src/statements/mod-declaration.md` §1 excludes module
loading, namespaces, exports and lowering; `binding-use.md` Non-goals excludes
recursive scope, lexical import scope, module resolution and lowering. They
are negative scope checks only, not positive semantic authority for this
proposal. The HIR ModuleDef route below likewise cannot select a language
typing rule. Their exact hashes are recorded in the handoff.

## 3. UNADOPTED environment rule, with constructive inputs

### 3.1 Entries are original constructor outputs

Use a finite typed environment graph `Gamma`, keyed by original declaration
identity **and its binding occurrence/scope**, not spelling or provider value.
An entry retains its actual owning derivation and complete dependent operands:

```text
Pub(d,p,G,D_pub)       actual publication output, complete original derivation
Fam(d,d0,T0,R0,D_fam) independently typed Family and its original binder tree
Mon(d,h,Contract,D_m) actual Mono introduction and complete Established tuple
Ali(d,h,r,D_alias)    actual Alias/projection into an existing monomorphic tuple
Liv(d,C,r,D_reg)      actual registered live member and simultaneous relation.
```

These are presentations of the original different constructors, not a new
quotient on providers. A Pub contains its independent declaration derivation,
not only the computed closure; it therefore supplies the independent source
premise of SRC §3.4 when actually instantiated. Fam likewise retains its
independent derivation. Mon and Ali retain the existing full reference map and
binder incidence created by their owners. No constructor turns an ID into one
of these entries. Environment formation may reference unsatisfied open local
clauses; it cannot assert runtime membership from formation.

### 3.2 The proposed component exposure rule

`FormModuleEnv*` traverses the finite registered component dependency graph in
dependency order, processing each component's complete relation together. Its
inputs are the actual resolved source/binder graph, genuine local `Sig`,
original component registration and declaration/publication constructors, and
the original ambient indices. It takes no `H_u`, use certificate, `b_use`,
`mu_id`, satisfied program, successful Q, or chosen Call descriptor as input.
Its ambient environment is the parent's original formed telescope with its
open obligations, not an additional premise that every ambient assignment
already satisfies those obligations.

For a component `C` the proposed owner rule is:

```text
E0 : original typed ambient/import environment at C's binding scope
all required prior dependency publications have their actual D_pub
Reg(C) : original simultaneous component registration
I_C : actual resolved module-reference incidences in the component RHSs
theta_C : original dependency-preserving embedding/restriction of base scopes
---------------------------------------------------------------- ModuleEnv-Expose*
Gamma_C = dependency-closed restriction along I_C of
          (E0 plus prior publication entries), under theta_C,
          extended by C's registered Liv entries at its member bindings
```

The rule performs lookup on the original binding graph, retaining every
dependency of each referenced entry. `theta_C` must already be a lawful
source scope map: every free field remains available at its original scope;
no challenge, history, EventProof or arbitrary world is moved into an earlier
binder. If it is unavailable, this rule has no instance. It is not synthesized
from solved row levels. For the fixed witness its ambient part is the identity
on the common module telescope; the formal `d_x` stays bound inside `G_id`.

The **new selection** is that the component RHS uses this typed projection
of prior entries. This rule preserves a Pub entry because publication created
it and this rule expressly projects it unchanged. It does not prove that all
original source module elaborations already do so. No runtime initialization
order is inferred from this static dependency order.

At completion of `C`, its original publication operation installs its own Pub
outputs for later components. Previously formed internal references still
point to the original Liv tuple. Publication does not rewrite those references
or retroactively instantiate them. A required predecessor publication cannot
be guessed from a future source name; a cycle is processed as one registered
component, with its original simultaneous introduction obligations intact.

### 3.3 Transport and use are separate operations

An ordinary lexical restriction retains the selected binding occurrence and
all typed dependencies under the lawful source scope map. It preserves the
entry constructor. This proposed component exposure is restricted to that
transparent projection; it is not a universal law that every import or capture
preserves Pub. At an actual source import, capture, rebind, conversion or view,
use that operation's original constructor and its whole output:

| Actual edge/owner | Result available to later lookup |
| --- | --- |
| Dependency-closed transparent module/lexical restriction | Same typed entry, with its lawful scope map and all dependencies. |
| Import/capture explicitly retaining a closed Published/Family dependency | Same closed family and free anchors; no expression Instance yet. |
| Actual monomorphic import/capture or Value/Result/retained rebind | Its genuine Mon output; never recover Pub from earlier provider ancestry. |
| Alias or monomorphic projection | Its genuine Ali output and the antecedent's same full frame. |
| Actual conversion | Its original result binding and executed fields; no invented same-value coercion. |
| Same-value checking | Its original check grammar and same tuple; no fresh frame. |
| Later actual publication | Only that publication's own Pub output. |

An edge labelled only “capture” without an original typed owner is insufficient
to select either transparent family capture or monomorphic capture. This
proposal leaves such an edge unresolved. Arbitrary cross-module imports have
the same requirement. These limitations are absence of a derivation, not a new
policy rejecting the source.

Once `Gamma_C` and an actual occurrence are formed, dependent lookup follows
`Resolve(u,d)` to that exact binding occurrence. It returns the entry together
with its composed scope map, without changing its constructor. Expression use
then dispatches to the existing rule:

| Looked-up constructor | Handle introduction and map |
| --- | --- |
| Pub | Original Published Name/Instance at this expression occurrence; SRC §3.4 independent definition derivation and §5.2 whole-frame new allocation. |
| Fam | Original Family instantiation at this occurrence, with its independent `d0,T0,R0`; original bound parameters and free anchors retained. |
| Mon | Original monomorphic Name restriction; same complete reference map and certificate, composed with the lawful scope map. |
| Ali | Follow its existing alias incidence and original projection; same antecedent map restricted to the genuine referenced contract. No fresh frame. |
| Liv | Only at its registered member incidence in its validating component; same simultaneous monomorphic tuple and original internal reference map. |

The new owner is `ModuleEnv-Expose*` composed with this lookup and those
existing rules. If one of their genuine premises is missing, the composition
does not exist. Lookup does not repair it by switching branches.

**Formation/elimination within the proposal.** Induct over the finite
component formation order and the actual environment operations. Publication
and each import/rebind/registration owner introduce precisely their own entry.
Restriction maps its entire dependency-closed graph with the one lawful scope
map; lookup selects that exact node and therefore eliminates to its stored
owner and operands. No case relabels a constructor. Alias and recursive
incidences remain graph references with their original argument tuples, so
this induction does not recursively unfold a cyclic certificate. Applying
the corresponding original use constructor then yields the whole map in the
table. This proves introduction and inversion for the new explicit rules;
it does not prove the original module judgment contains those rules.

## 4. The fixed source under the proposal, and exact parent operands

First run the original declaration construction of §2. Its output installs
`Pub(d_id,p_id,G_id,D_pub)`. Forming `answer` uses its one required external
dependency `d_id`. In the proposed module environment rule, the source incidence
selects that installed binding; its dependency closure retains the entire
`G_id`, and the common module base scope map is identity. This yields

```text
Gamma_answer*(d_id) = Pub(d_id,p_id,G_id,D_pub).
```

This equality is a **conclusion of the proposed formation**, not a premise
inferred from `DefId` equality. The expression owner for `u_id` in that proposed
formation is its direct module lookup. The proposal inserts no monomorphic
capture/rebind between the installation and this lookup. That fact describes
the proposed derivation; it is not a proof that an original owner could never
insert such an introduction. No Lambdas/captures are inferred from the shape
of the returned value. `id`'s own formal is not the looked-up module binding.

The looked-up Pub now supplies the antecedent of the existing Published Name
rule. The real Instance **within this proposed source formation** has publication
owner `p_id`, static introduction origin `i_id*` tied to occurrence `u_id`, and
member `d_id`. The origin is fixed before assignments or histories. The original independent definition
derivation in D_pub and SRC §3.4 construct `new(p_id,i_id*,d_id)`; §5.2 constructs
the allocation, without asking whether the generated clauses are satisfiable:

```text
mu_id* = SRC-Allocate(G_id, new(p_id,i_id*,d_id), E_original)
b_use* = (d_id,u_id,Resolve(u_id,d_id),p_id,D_pub,ModuleEnv-Expose*,lookup,
          Instance(p_id,i_id*,d_id),a_id,G_id,mu_id*,mu_id*(r_id),
          complete original dependent rule/operand incidences).
```

`E_original` is the original finite local proof grammar, with all unsolved
clauses at their original binders; it is not a valid-client certificate supplied
to the constructor. The type of `mu_id*` includes the complete mapped graph,
not merely a root or row vector. Its action is exactly source-use-map §5:

| Whole field class | Image |
| --- | --- |
| Original occurrences, resolution, declaration/arm identities | Same identity and original incidence. |
| Raw provider, Intrinsic, Established, OneShot and their complete dependencies | Same fixed field or base binder. |
| Shared | One original base binder across the entire joint client. |
| Eligible own Desc | One `(i_id*,q)` at translated original scope and dependency telescope. |
| Fixed/ineligible Desc | Same fixed field; Internal reachability never reverses a fixed mark. |
| Internal | One whole component frame, including all members and background constraints. |
| ViewLogic | One binder per frame below its type dependencies and before its challenges. |
| Event/EventField | Original source event key and actual parent, with shared runtime operands. |
| EventProof | Original frame/event/proof-region key below that event and its dependencies. |
| Rigid opening, inference existential, Check/Specialize | Original kind, guard, scope and local premises. |
| Closed imported Pub/Family parameters | Original bound family; only actual free anchors are traversed. |
| Roots, witnesses, guards, alternatives and all reference operands | One simultaneous homomorphic map; no omitted conjunct or selected successful arm. |

Binder induction proves this is well scoped: fixed/base entries already have
their dependencies, each allocated declaration follows its mapped dependencies,
and event proof binders remain below their original event. Memoization by
declaration/frame/event class preserves repeated incidence. Registered cyclic
references use the mapped complete argument tuple, without unfolding or
changing recursive semantics. These are the existing allocation lemmas used
at their actual premises; no new F1 or FK1 result is asserted.

The literal substitution **in the proposed completion** into the first part
of original-generation §7.2(2) is

```text
Decl* := retained original (D_pub,P_id,r_id)
b_use* := the constructed record above
mu_id := mu_id*
source-reference leg := mu_id*(r_id)
R_f* := ModuleContractRoot*(Decl*,b_use*,mu_id*)  [STILL UNCONSTRUCTED]
```

The parent §7.2 is itself an unadopted constructor. This substitution fills
its proposed publication/use operands, not the original same-occurrence gate.
The registered-root expression remains a separate missing constructor, not a
cast of `mu_id*(r_id)`. No `q_f` at an authentic registered Application root,
`e_c`, original Gen-Call-0, or full Call theorem is thereby obtained. In the
original system, even the preceding use substitution remains unavailable
until `ModuleEnv-Expose*` is established as an existing rule or adopted after
review. All original indices stay literally `B,X,xi,Delta_c,d_id,u_id`; no
specialized `Int -> Int` or one selected ambient assignment is substituted.

For a different actual branch, substitute its existing whole reference map
or genuine Family allocation instead. The Pub map above cannot be reused for
Mon/Ali/Liv. Its equality with those maps is neither needed nor claimed.

## 5. What erases, what may change, and falsifiers

For an **already classified original derivation**, recording the environment
path and entry constructor is conservative metadata. Erasing only those
records returns that exact derivation. Induction on its actual rule nodes
preserves every operand, alternative, guard and scope. Hence for every original
ambient assignment, one joint scoped strategy, and arbitrary well-scoped W,
its complete constraint and designated observation fiber is unchanged. Empty
fibers and all independently admitted histories remain included. This reuses
the prior handle-introduction note's retention lemma at its stated premises.

That lemma cannot erase the new `ModuleEnv-Expose*` inference itself. Removing
its label leaves the previously missing occurrence-to-entry justification.
The proposal adds this rule to the original genuine rules, without replacing
their existing derivations. Thus it can embed those derivations unchanged,
but it additionally constructs the direct
module path above. No argument yet shows that every added derivation was
already licensed, or that admission/observation fibers of the complete raw
source are equal. No new executable operation is proposed; absence of runtime
code changes alone does not prove semantic conservativity.

The precise alternatives for Luna's adjudication are: establish that the
original module owner already performs this typed projection, making the rule
a derived presentation; or adopt the displayed environment completion as new
formation authority after independent review. Requiring a new Meta-typing or
whole-source safety predicate would only hide the same gap and is not a third
construction. Automatic Mono conversion is also not free: it needs its actual
instantiation/rebind owner and full existing tuple.

Concrete logical/source-structure falsifiers for review are:

1. **Recursion.** In `my f x = g; my g y = f`, both references lie in one
   registered component. Publishing `g` early just to serve `f` would replace
   its Live/Internal tuple with an independent frame. Expose* processes that
   component jointly and supplies Liv; it cannot make the premature Pub step.
   The original simultaneous introduction law is still required.
2. **Order.** A reference to a not-yet-published predecessor cannot use an
   entry absent from the actual formation prefix. Source textual order is not
   sufficient; the fixed witness's one dependency has an explicit two-node
   order. This proves no general runtime eager/lazy initialization theorem.
3. **Capture/rebind.** If a genuine capture produces `Mono(h,Contract_h)` from
   a previously published value, a later Name must reuse that `h`. A module
   target or equal raw provider cannot bypass the captured entry. If the
   capture rule is unspecified, Expose* does not classify that capture.
4. **Alias/shadowing.** Two resolved binding occurrences may denote one raw
   provider while having different owners; lookup keys include binding scope
   and incidence. Looking up by provider or printed name could select Pub
   through an actual Alias or select the module `id` through a shadowing local.
5. **Joint consistency.** Two frame-local description variables may satisfy
   `a_i=Int` and `a_j=String`, while one shared monomorphic `a` cannot. Likewise
   two ViewLogic witnesses can satisfy incompatible per-frame equations that
   one Shared witness cannot. These are logical separation examples for a
   guessed Pub/Mono conversion; they are not source-qualified counterexamples
   to this one-use program, and do not assert that all relevant source frames
   permit such assignments. They show why provider equality and erased code
   cannot prove equality of arbitrary-W fibers.
6. **Scope.** Any proposed restriction placing an event-dependent witness in
   the module base environment is ill scoped even if its endpoint looks equal.
   The full typed dependency closure, not a list of visible type variables,
   determines the admissible projection.

## 6. Source/native seam and minimal implementation request

At the frozen code, `candidate_source.rs`'s ModuleDef Name case constructs
`PendingDefinitionUse { parent,target,occurrence }` and `Action::Module`.
`execute_candidate_action` selects `route_candidate_open_use` for an active
internal use and `route_incoming` otherwise. `CandidateSourceCall` in
`candidate_call.rs` exposes `module_callee_target()` by matching the actual
ModuleDef source, while `PendingCallSupplier` separately names
`ModuleNameSourceTypingAndAdmission` and
`ModuleUseReceivingExportCorrespondence`. These are explicit structural
inputs and open source consumers, not an authentic typed environment rule.

The reviewed native retention result supplies the actual retained FreshUse
maps through their GraphState owner lifetime. It proves no classification of
these source fields and no original `theta_C`. Thus retaining another guessed
Published tag would not implement this proof. No safe semantic code slice is
authorized before the environment completion and its genuine data inputs are
accepted; this conclusion is based on the two inspected source and Call owners.

After that seam, the minimal TODO is a publication-owned typed entry reference,
its actual component-scope transport and occurrence lookup derivation, whose
elimination produces the whole branch-specific contract and map. The entry
must be formed when the source constructor knows its fields; no retrospective
interpretation from a Function shape, target DefId, successful Solve or native
route is allowed. A provisional representation would have to remain explicitly
provisional until the source `Sig`/field interpretation exists. Its falsifier
is any lookup whose claimed tag or dependency cannot be traced to its original
publication/import/rebind/registration owner, or any field whose source map
has no coherent retained native image. This is a request for a later exact
lease, not permission to edit either code owner.

## 7. Costs, parent disposition and freeze

The proposed metadata can use finite graphs and simple linear lookups. If n
counts all distinct registered environment/entry/binder/dependency records and
the explicitly retained output incidences, construction and validation by
repeated graph scans can be bounded by O(n^2) time and O(n) storage, with compact
node identifiers and shared derivation references. With k uses whose complete
frames are copied explicitly, include all copied frame incidences in n; the
single-frame input size alone is not a bound on aggregate output. This is a
possible implementation of the finite annotation, not a bound on semantic
proof search, constraint solving, all source elaboration or the current Rust
compiler. The user permits complexity changes; no optimized complexity claim
is needed to justify choosing this owner.

**Parent disposition:** `HINTRO-OWNER-u_id` remains OPEN, original conditions
closed 0. The useful constructor is applied to the proposed §7.2(2) operands
in §4; it is not filed as a new proved parent. The next single action is fresh
independent review and Luna adjudication of `ModuleEnv-Expose*` as the missing
typed module environment rule, including its exact admission boundary. If an
original owner is supplied instead, compare that owner's actual entry path
against §3 and use its branch without forcing Pub. Full root/Call and global
theorems remain subsequent independent work.

Prior work reused: source-family declaration publication, original SRC
allocation and whole-map scope lemmas, the retention lemma for already typed
derivations, Lemma W only for existing certificates, and native remap lifetime
only for native ownership. Rejected shortcuts: GC inversion from an untyped
client, same-provider/DefId classification, AST-absence exclusion of Mono,
native-route authentication, and substituting a final synthesis root for an
unconstructed registered contract root.

Only document/source inspection, SHA-256 validation and writing the two leased
research outputs occurred. No tests, code execution experiments, probes,
compiler edits, Git, extra/scratch files or descendants. A first hash command
using `python` was unavailable; it was rerun successfully with `python3`.
Requested role/model/effort: Astra core proof / `gpt-6-astra` / medium;
effective observed model/effort: UNKNOWN. The handoff pins all direct inputs,
records resources and carries the frozen artifact SHA-256. Writer STOPs after
that handoff; no claim of independent review or production authority is made.
