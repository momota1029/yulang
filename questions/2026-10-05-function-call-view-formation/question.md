# Formation of complete Function call views

Question ID: `function-call-view-formation`
Question revision: `q1`
Predecessor/history: follows `production-function-inlet-context-domain/q1`, `production-function-denotation/q1`, `production-function-bound-membership/q1`, `source-annotation-boundaries/q1`, and `callback-context-delivery.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `d90ba4425038cf86ff932ed42eb309931e143fd8`; governing callback/typed-core sources below are unchanged in the current worktree
Task/thread locator: unavailable: the active objective is to complete the Yulang inference theory and replace its inference implementation
Governing source/section: `notes/design/2026-10-03-callback-context-delivery.md` §§1–2; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6, 9; `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` §§2.1, 3; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.2, 3, 10

## Requested scoped decision

Select the source/elaboration rule that forms a complete instantiated
role-indexed callback interface and its original static slot/profile from
ordinary source declarations and uses. The rule must say how it forms the
known `F_cb`, static slot `beta`, `Slots(beta)`, typed paths/Flow, owner and
receiver relation, and their correlated constraints under one original
`(nu,K,D)` before the pending Function comparison `Q`.

This question is about the missing raw-source-to-decorated-context formation
boundary. It does not reopen callback role selection, callback-literal B,
preservation of an existing Pure value's actual role, annotation endpoint
export, Function denotation Option A, the broad independently typed inlet
domain, or production membership Option 2. It selects no solver algorithm or
compiler implementation by itself.

## Background and current premises

- Callback-delivery §2 assumes an already resolved and instantiated
  `F_cb`, static `beta`, and original `Slots(beta)`. It explicitly leaves
  completed-interface formation as an obligation. B is the normative
  callback-literal generation order once that context is known.
- Theorem C §§2.1, 3 takes decorated owner/view witnesses, a typed carrier,
  declared port/profile/path, compatible punctured context, and one original
  `(nu,K,D)` as inputs. It proves conditional independent admission; it does
  not derive the complete decoration from raw call syntax.
- Typed-boundary §6 can introduce a dynamic boundary from a supplied
  signature profile, derive conditional identity/prefix-removal correspondences,
  and transport existing evidence. Source elaboration must supply the profile
  and the paths. Receipt creates ownership of a use, not a profile or contract.
- The approved inlet-domain answer ranges over all independently typed
  compatible punctured contexts. The approved denotation answer retains the
  complete original `Rel_C` and independent admission predicates. The approved
  membership answer selects Option 2, allowing sound constrained production
  extras without making source-constructor witnesses mandatory; the exhaustive
  membership rule is still open.
- The approved annotation-boundary answer names binding, argument, and
  expression `as Type` boundaries and says successful boundaries export their
  target plus local evidence. It does not define complete Function slot/profile
  formation.
- Current production inspection is bounded: the ordinary `h 1` call remains
  a nonleaf HIR value and is rejected by the current simple-chain lowerer before
  solver collection. Type-arena Function views and store `AdmissionReceipt`s
  do not themselves contain the executing CallView/slot/profile/receiver
  certificate. This is a current implementation observation, not a permanent
  source-language rejection rule or a repository-wide absence claim.

## Options and consequences

### 1. Form callback views only from explicit source contracts

Require an explicit source declaration/annotation to determine the complete
role-indexed `F_cb`, its static slot identity and profile-position inventory.
Define how omitted/wildcard and explicit capture annotations determine
protection and concrete grants at applicable positions. Ordinary inferred
formals may use callback-context delivery only after such a contract is
available.

Consequence: the grammar/elaboration boundary must identify the annotation
form and its four-port/profile meaning. Unannotated higher-order uses without a
known contract cannot yet supply the callback-context premise; the supported
inference envelope must record that boundary.

### 2. Infer the complete callback contract from source declarations and uses

Define a source constraint-generation judgment that forms one shared,
role-indexed `F_cb`, static slot/profile inventory, typed paths, owner/receiver
incidences and joint `(nu,K,D)` constraints from the whole relevant declaration
or recursive component. Preserve callback-delivery B: deliver a resolved
expected context before elaborating any callback literal body, with any
constraint scheduling proven equivalent to B.

Consequence: prove that the completed interface/profile is uniquely or
principally determined to the extent required, that profile positions retain
source identity and scope, and that `Admit_F` remains independent of `Q`. The
source grammar need not expose new keywords, but its inference/elaboration rule
must be fully specified.

### 3. Keep source-generated views conditional and define production admission independently

Do not require every production observation to factor through a raw-source
constructor. Instead define the exhaustive production `Admit_F`/`Sat_F` rules
over the approved complete `Rel_C` and fixed `(nu,K,D)` basis, including
constrained Option 2 extras and the checked-containment proof. State which
source-derived views are still needed for source adequacy and which may be
admitted only by the independent production relation.

Consequence: this preserves the selected production-membership policy but
requires a complete, correlated membership grammar and `D_C ⊆ D_A`,
`P_A ⊆ P_C` proofs. It does not let endpoint shape alone invent source
receipts, profiles or paths.

An exact hybrid is welcome if it assigns each formation premise to one of
these sources without conflating source introduction, transport, production
extras, and comparison success.

## Affected work

Blocked scope: unconditional source generation of callback `F_cb`/slot/profile
contexts; complete Function admission and source adequacy for those contexts;
production conformance and inference replacement where those premises are
needed.

Independent authorized work: conditional theorems over already typed
decorated contexts, the existing pure structural/FMP lane, and effect,
residual, lifecycle, and State gates that do not assume this formation rule.

Required answer: select an option or state a precise hybrid; specify the
authoritative source from which each of `F_cb`, `beta`, `Slots(beta)`, typed
paths/Flow, owner/receiver incidences, and original `nu,K,D` constraints is
formed, and confirm admission remains independent of `Q`.

Pending publication: keep this entire question directory unstaged and
uncommitted until the questioning primary discovers and validates an explicitly
approved local answer and commits the matching question/draft/answer together.
The answering primary never mutates Git. Posting does not pause the goal;
dependent work waits while independent work continues.
