# Native PE interface equivariance: identity-observer falsification

Status: frozen research-only falsification report; unreviewed
Baseline: `2202317335e1cd7e224efe548c3b64f0de402098`
Branch: `research/simple-sub-intrusion`
Scope: selected PE-ID and finite-public-import PE-PICK; IFACE_EQUIV only
Authority: checker architecture direction only; no implementation or new meaning

## 1. Objective, method and result

Attempt to falsify actual native interface equivariance through an identity
observer already admitted by the pinned rules. The method is clause inversion
and minimized certificate/identity mutations, rather than another executable
transition model. No other producer's construction or verdict is an input.

No counterexample to a **complete coherent action fixing the original rigid
identities** was established. A smaller, positive result is the following
source-grounded rejection discriminator: an ordinary Value certificate at
decoded root `u` which instead names source root `r != u` must fail, even if
its displayed endpoint or complete descriptor equations otherwise agree.
This falsifies operand-insensitive transport or certificate reuse, not the
selected PE theorem. The exact outstanding premise is covariance/reflection
of each authentic independent local law and its identity observations; native
record equations alone do not establish that premise.

Claim classes:

- Established selected results used as inputs: PE-ID/PE-PICK in their pinned
  scope, ordinary native certificate recognition, original fresh/alias
  allocation and retained proof choices. This note does not independently
  re-certify those results.
- Documentary derivation: necessary identity preservation constraints and
  rejection witnesses for named incomplete-action mutations, below.
- Conditional theorem: finite record/term transport given the exact local-law
  covariance and identity inventory in §4.
- Conditional representation hazard: an additional identity-sensitive local
  law with no supplied covariance proof. It is not an actual native-source
  counterexample merely because the registry permits authentic local laws.

## 2. Pinned governing clauses and dependencies

The native projection selection §§2–4 fixes source formation before export,
the actual public object, fresh roots and aliases, and the finite import
boundary. The integrated construction §§3–4.3 fixes Omega, whole-frame decode
and retained fibers; §§6–8 fixes actual-operand checking, source-lawful clients
and actual monomorphic imports. Certificate constructors §§3–4 fix authentic
local-law operands, immutable world fields and current invocation removal.
The successor synthesis note §5.1 supplies the independent covariance and
rigid identity requirements. The DAG's IFACE_EQUIV declaration remains
OPEN-PROOF. The q1/d1 receipt selects architecture direction only.

SHA-256 of exact baseline bytes (all equaled working-tree bytes at initial
and final dependency checks):

```text
aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919  notes/design/2026-10-08-native-projection-public-export-definition.md
4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631  notes/theory/2026-10-08-projection-public-export-construction.md
04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8  notes/theory/2026-10-08-native-projection-certificate-constructors.md
e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f  notes/progress/2026-10-07-successor-recursive-synthesis.md
c9e6c87312e1ef98d1561c1c79df4bd95d08f41fd0c808a93f6040851f057c25  tools/research_successor_obligation_dag.py
4c10a288622aca39d040b1ecd0e52fa920156b50a4e07b3a53966d22b43f428a  questions/2026-10-08-native-direct-consumer/receipt.md
```

The rules/research-lab.md, rules/design-authority.md and
rules/git-concurrency.md were read in full. Startup task/index records were
read only as locators. They supply no alternative semantic interpretation.

## 3. Smallest admitted witness and identity mutations

### 3.1 Actual-root operand exactness: one use, one Value check

Hypotheses: select native `my id x=x`; one lawful `new(id,i)` decodes an
ordinary root `u_i`; choose the ordinary Any target `V` and the hereditary
Top proof available in integrated §6.2. The source root `r` and new ordinary
root `u_i` are distinct records (§4.2). The consumer retrieves actual submitted
roots and validates proof operands (§6.1 step 1).

```text
valid:   Direct(u_i,V; Value(Top with operands u_i,V))
mutant:  submit at (u_i,V), but certificate names (r,V)
result:  mutant rejected, by §6.1 step 1
```

No carrier, Return, Function-domain comparison or invocation history is
needed. Removing the single operand mismatch removes this discriminator;
removing the actual root check removes the specified rejection. Thus the
witness is minimal in ordinary client-use/check count. It addresses both
success and failure, rather than equating only successful proof fibers.

This is an admitted ordinary checking operation with an admitted target and
identity observer. It is a counterexample to a candidate **mutant** which
identifies source and public operands, compares only equal readouts, or keeps
an old root handle in a proof. It is not a counterexample to whole transport:
the required actual public operand is precisely what such transport retains
or translates. Equality of root descriptions does not license operand reuse.

### 3.2 Fresh versus alias: sharing is observed on the full frame

Two aliases of one real new refer to the same root/frame. Two distinct real
new events allocate distinct ordinary roots and their appropriate frame-owned
slots (integrated §4.2 and §7). Equality/sharing of these retained public fields
is a well-scoped W observer, as permitted by §7 and explicitly inventoried in
successor §5.1.

```text
new(id,i); alias(i,j):          root(i) = root(j)
new(id,i); new(id,j), i != j:   root(i) != root(j)
```

A transformation splitting the first root or merging the second pair changes
this observer. This proves the necessary sharing partition, not a right to
rename client-visible actual roots while W remains fixed. Internal labels can
move only with their complete references; a semantic identity is a different
coordinate from its presentation label. Shared, event-owned and frame-owned
proof slots must also retain their respective partitions. Their numerical
equality cannot reconstruct the original ownership classification.

### 3.3 Exact installed projection and evidence

Certificate §4.2 requires `ProjectIntro(b;omega,beta)` to use beta equal to
omega's retained environment field at that **registered b**, with its actual
slot/reference incidence. Supplying another field having the same endpoint
type fails the elementary record clause. It does not suffice to preserve
`Lookup`'s raw value alone: the complete field contains installed certificate,
contract, incidence and provider. Identity and Compose also remain distinct
proof records (certificate §3); any W comparing those tags is retained, so
normalizing Compose to Identity changes an allowed observation.

These are native record/evidence observers. They reject partial slot remaps
and proof canonicalization. They do not say that different complete L terms
cannot both be legal, nor that every proof-dependent predicate is a new
primitive needing a separate transition model.

### 3.4 Fixed pick import and actual provider

For native `my z=0; my pick y=z`, integrated §8 fixes J_0, its installed
monomorphic contract, same raw value/provider and full free dependency closure.
At completion the alias graph is `read=body=outward=z`, not `outward=argument`.
Changing the captured operand to the independently constructed literal J_1
changes the returned raw value while both displayed result types are Int.
Thus equal printed types cannot justify a Fixed(J_0)-to-Fixed(J_1) certificate.

The actual provider is separately a retained operand. A proposed map changing
that provider while fixing J_0 violates the Fixed/import and same-provider
clauses before any scalar result check can repair it. This is a necessary
equality constraint, not an assertion that two literal 0 initializers must
allocate distinct providers; that allocation policy is not needed or inferred.
Likewise, replacing the fixed contract by a fresh instance of its former
scheme violates the prescribed monomorphic installation. Finite public
projection/record imports remain inside the stated PE-PICK envelope; an
arbitrary hidden-source import does not become an admitted witness here.

## 4. Conditional transport and the precise unproved seam

Fix the original rigid fiber, finite use grammar, binder order and authentic
local catalogue. Let h be a total sort/scope-respecting bijection on presentation
names, preserving all ordered fields, source-slot incidences, current-event
references, ownership partitions and designated root correspondence. Fix each
actual source/binder/provider/capture/event/import identity, external input,
local-law declaration and proof-constructor tag that an operation reads as a
semantic constant. Transport every reference to movable names, including
root operands inside certificates, rather than only root equations.

Exact additional premise E: for every active independent local declaration,
ground/hereditary certificate action, compatibility/authority/world-history
action, inlet/input-image law, VP alternative/equation rule and Direct premise,
its truth and typed outputs transport and reflect under h at its complete
declared telescope. E must enumerate the operation's actual identity tests;
an observed fixed constant belongs to the rigid fiber. E is not inferred from
membership soundness, identical signatures, unchanged interpretations or
successful queries.

Conditional derivation: record projection and whole-record substitution commute
with a bijection. An equality guard reflects since `x=y iff h(x)=h(y)`; rigid
comparisons are covered because h fixes their constant. Install/Lookup's
explicit retained-field equations and pure Return's same-tuple fields commute
with the same complete action. ExitOwn_IF selects the same current occurrence
when its references and guards move coherently; correctness of the compatible
world action itself uses E. Induct on the finite local proof term, preserving
tags, ordered intermediate operands and telescope references. Primitive,
hereditary and registered-equation steps use E, rather than assuming their
law from the term tag. The inverse action gives reflection. Apply the same
action at each original finite event/use with its sharing partition unchanged.

This establishes transport of the specified record/proof skeleton **conditional
on E**. It does not enumerate every active authentic L law, prove their E laws,
settle recursive operator conjugacy outside the selected finite grammar or
certify an actual compiler/checker representation. The provider and root
countermutations demonstrate why those hypotheses cannot be dropped.

An open authentic local catalogue is admitted by certificate §3, but its
entries must have genuine independently typed local laws. A hypothetical
entry `accept iff internal label = c` defeats a renaming moving c when c is
treated as movable. Without an actual selected declaration and independent
local law this is only a conditional representation hazard. If such an
identity-sensitive constant really is read, successor §5.1 already requires
it to be rigid. Claiming this invented entry refutes PE-ID would confuse the
catalogue parameter with established native-source coverage.

The remaining work is therefore operation-specific identity inventory and E
evidence at authentic owners, particularly independent hereditary/history/
input-image/local primitive laws. Another checker imposing nominal transition
rules would leave this same premise untouched. No second or third equivalent
probe was attempted.

## 5. Checks, coverage, resource budget and omissions

Read-only commands: `git show 220231733:<path>` for pinned clauses, narrow
`sed -n`/`rg -n` reads, `git rev-parse 220231733`, `git branch --show-current`,
`git status --short`; Python hashlib plus git-show byte comparisons for the
six direct dependencies. The baseline resolved to the full SHA above; all
six dependencies matched. Final checks inspect only this note's UTF-8,
newline/whitespace/fences/local links, dependency byte equality and SHA-256.
These integrity checks are not executable semantic evidence or independent
review. The artifact digest is supplied in the submission packet to avoid
self-referential hashing.

Coverage is documentary and finite: one ordinary Value check, two sharing
patterns, native projection/proof-tag equality, literal fixed-import change,
and the stated conditional record induction. Seeds/ranges and execution
counts: none. No semantic oracle, executable probe, build, test, benchmark,
child, Git mutation, or generated scratch output was used. Single short
read/hash processes only; peak RSS and total CPU/wall time were not
instrumented. No numeric resource budget was assigned beyond no builds/tests/
benchmarks and at most one indispensable tiny probe; zero probes consumed.

Oracle independence: the discriminator is entailed directly by the selected
actual-operand consumer clause, rather than by two implementations sharing
transitions. It shares the reviewed native grammar and its independent local
law premises with PE. It supplies no independent validation of those laws.

Failure conditions: a non-total reference map, moved rigid constant, stale
certificate operand, split/merged alias partition, changed fixed import,
discarded proof witness, unenumerated observer, or local law without E defeats
the conditional certificate. An unknown law is unresolved, not semantic false
or an accepted source rejection.

Omitted: arbitrary foreign/open-registry semantics, unknown hidden-source
imports, general State/recursive constructors, exhaustive histories and all
authentic local declarations, search completeness, actual numeric-ID/cache/
rebuild lifecycle, current F5 and production correspondence. No aggregate
gate closure or semantic strengthening follows.

Recommended next action: obtain the selected native owners' exact local-law
identity inventories and covariance/reflection witnesses, beginning with
the root operands of Direct and inherited input/world certificate actions;
keep unknown declarations explicitly conditional.

## 6. Frozen commit packet

- Exact leased path: `notes/progress/2026-10-10-native-pe-interface-equivariance-falsification.md`.
- Baseline SHA: `2202317335e1cd7e224efe548c3b64f0de402098`.
- Changed dependency hashes: none; six baseline hashes retained in §2.
- Review status: unreviewed research-only artifact; no independent certification.
- Checks already run: pinned source inspection and six dependency byte/hash
  comparisons; final artifact integrity/hash results accompany submission.
- Proposed checkpoint message: `research: falsify incomplete native PE identity transport`.
- Shared-record deltas left to primary/curator: record the exact-operand
  rejection discriminator and conditional local-law seam under IFACE_EQUIV;
  retain OPEN-PROOF and every existing prerequisite; no PE theorem status or
  architecture/implementation authority change. No task/index/question writes.
- Writing stops at submission. Further edits require renewed lease/review scope.
