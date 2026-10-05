# Admission transport depends on live primitive operands

Date: 2026-10-05
Status: independently reviewed conditional derivation, extensional countermodel and bounded production correspondence
Assignment baseline: `0ab7620e167f190691a9ec50fde507d039265aa4`
Branch supplied by primary: `research/simple-sub-intrusion`
Implementation authority: none
Exclusive write lease: this note only
Supersedes: none

## 1. Result and recovered gate

The [conditional admission-retraction theorem](2026-10-05-residual-admission-retraction-proof.md)
already proves exact visible-query membership when its admission predicate is
effective, bisimulation-extensional and preserved by the canonical graft.
The [source-premise audit](2026-10-05-residual-admission-source-premise-audit.md)
leaves the primitive source operands and their comparison contexts open.
`tasks/current.md`, its residual-query entry, and
`notes/theory/inference-theory-map.md`, "Conditional closure — residual
query membership", still identify that gate. They were read for routing and
are not mathematical premises or leased outputs.

This note narrows that gate to an operand test. A finite positive formula
whose varying endpoint occurs only in visible structural upper tests and
rigid-support restrictions has the required one-way transport. In contrast,
a single regular-tree equality predicate on the varying endpoint and a fixed
original imported operand can fail transport, even with nonempty required
labels, decidable extensional admission, identical rigid support, and one
unchanged witness. Graph-presentation sensitivity is unnecessary for this
failure.

The obstruction is an abstract residual-predicate countermodel, not an
established Yulang source counterexample. Current production HIR and solver
term observation do not expose this mandatory-Record source fragment. A
store `AdmissionReceipt` cannot supply a source-admission proof. The useful
next step is therefore to identify an actual primitive source clause and
its complete ordered operands before trying to transport it.

## 2. Authority, questions and snapshot boundary

Read `rules/question-board.md`, `rules/research-lab.md`,
`rules/git-concurrency.md`, `rules/design-authority.md`, and
`rules/orchestration-budget.md` before deriving or writing this result.
This is one producer artifact, with no independent certification claimed;
review and shared integration remain the primary's responsibility.

The current board contains locally finalized answers for production inlet
context quantification, source annotation boundaries, and handler protection
release. The inlet-context directory has no receipt at inspection. No Git
operation was used to determine integration or exact committed equality.
Consequently this lane does not consume those local answers as new authority.
Its structural result is independent of their alternatives. Their presence
must not be mistaken for an adopted primitive admission clause or a proof of
production correspondence.

The assigned commit and branch are primary-supplied baseline metadata. The
direct inputs were inspected from the working tree and pinned by the SHA-256
table in §8; this worker does not claim to have verified their equality to
that commit. Rechecking the hashes before handoff protects this specific
read snapshot. Primary integration must still verify baseline/branch and any
affected dependency movement.

Governing mathematical inputs are
[residual factorization §§2–7](../design/2026-10-03-open-residual-factorization.md),
[structural projection §§2–6](../design/2026-10-03-scoped-structural-projection.md),
[scoped equality/permissions §§1–2](../design/2026-10-03-scoped-constraint-solving.md),
and the [multi-atomic structural image](2026-10-05-multi-atomic-record-projection-proof.md).
Their research status supplies no compiler implementation authority.

## 3. Explicit structural premises and a sufficient operand class

Fix precisely the conditional theorem's pure structural setting: finite
closed contractive regular graphs of identity-only atoms, contravariant/
covariant Functions and mandatory finite-label Records; one fixed visibility
classification; a finite required-label set `H`; hidden atoms `kappa_h`;
one descriptor-free class `X`; its upper bound

```text
X <= U_H = Record{h:kappa_h | h in H};
```

and any finitely many fixed closed visible upper queries `W_i`. There are
no other structural equations, lower bounds, effects, or interacting open
classes. This is the earlier theorem's domain, not a new source support
boundary. Original binder and request identities remain fixed.

For `T <= U_H`, define the metatheoretic map

```text
c_H(T) = G_H(A+(T)),
```

where `A+` is the signed greatest-fixed-point projection and `G_H` is the
closed-copy/fresh-root graft. The visible graph is copied whole; its internal
edges are not redirected to the fresh hidden-bearing root. This map is proof
notation for those existing constructions, not a new source primitive or
solver obligation kind.

The reviewed structural facts give

```text
c_H(T) <= U_H,
A+(c_H(T)) ~ A+(T),
T <= W iff c_H(T) <= W        for every fixed closed visible W,
Rigid(c_H(T)) subset Rigid(T).
```

The visible-upper equivalence follows by applying best-comparator
factorization to both roots and using the graft's projected bisimulation.
The support inclusion follows because projection introduces no rigid
identity and the graft restores only required atoms already reachable in T.
Therefore every fixed propagated allowed-name set remains satisfied at the
same witness coordinate. Constructor heads acquire no levels.

For a fixed `omega`, consider a supplied finite acyclic positive Boolean
formula whose leaves are only:

| Leaf | Premise | Transport |
| --- | --- | --- |
| `B(omega)` | Predicate of unchanged original operands only; no occurrence of the varying endpoint or a derived view of it | Same truth value |
| `T <= W(omega)` | `W(omega)` is fixed during transport, closed and visible in this structural relation | Same truth value by best-comparator factorization |
| `Rigid(T) subset P(omega)` | `P(omega)` is the same fixed propagated identity set | True remains true by support inclusion |

Finite conjunction and disjunction preserve the implication inductively.
Thus any such formula `F` satisfies

```text
F(T,omega) implies F(c_H(T),omega).
```

This is a sufficient operand criterion. It does not assert necessity. It
admits no arbitrary negation, equality with a hidden-bearing fixed operand,
provider-identity test, endpoint-sensitive scope certificate, dynamic
history primitive, quantifier movement or new recursive rule. A conjunct
may be placed in `B(omega)` only after proving it does not inspect the
changing endpoint through a dependent reference. A syntactically absent
`T` variable does not establish that independence.

If each unchanged leaf is total and extensional and its `W` and permission
data have the stated effective interpretations, the formula is total and
bisimulation-extensional on finite inputs: ordered-pair structural simulation
decides each upper test, rooted reachability decides support, and finite
Boolean evaluation terminates. Effective finite enumeration of `omega`
remains the separate premise in the earlier query-membership theorem. This
criterion supplies no production admission algorithm.

The criterion may be applied to `Guards and Phi` only after their actual
primitive interpretation has been decomposed accordingly. In particular,
an unguarded structural upper test is not the scope certificate admitting
that test. The mandatory root and every actually derived comparison still
re-enter the original guard in their original `(b,j)` context. Current
certificate validity is an additional obligation, not supplied by this table.

## 4. A nonempty-H extensional obstruction

Use one hidden rigid identity `kappa`, two distinct labels `h,g`,
`H={h}`, singleton `Omega={omega}`, all needed rigid permissions, and
the fixed visible upper query `W={}`. Let one fixed original imported
operand be

```text
C = Record{h:kappa, g:kappa}.
```

Define a supplied residual predicate using the existing regular-constructor
equality law:

```text
Guards(T,omega) = true,
Phi(T,omega) = (T ~ C),
A(T,omega) = Guards(T,omega) and Phi(T,omega).
```

Here `~` compares rooted regular unfoldings; it does not inspect pointer
sharing. Its finite graph bisimulation decision is total and extensional.
The fixed operand `C` is unchanged during transport. This is an instance
of the abstract predicate parameter, not an invented production meaning
for a source `Phi` clause. If instead `X=C` is an explicit input `Eq` sent
through the quotient, `X` becomes descriptor-determined and is outside the
descriptor-free hypothesis. Those two interfaces must not be conflated.

Take `T=C`. Then

```text
T <= {h:kappa},        T <= {},        A(T,omega) = true,
A+(T) = {},
c_H(T) = {h:kappa},
Rigid(T) = Rigid(c_H(T)) = {kappa}.
```

Both root fields of `T` disappear in positive projection because their
children are hidden. The graft restores the required `h` field only. Its
root has no `g` field, so it is not bisimilar to `C`, and

```text
A(c_H(T),omega) = false.
```

Thus same-witness retraction fails while structural upper tests and
permissions continue to hold. The admitted image is precisely the singleton
visible value `{}`: every admitted `T` is bisimilar to `C` and projects to
`{}`. The canonical-graft membership test at `{}` rejects because its sole
witness coordinate fails `Phi`. This does not refute the conditional
theorem, whose retraction hypothesis is absent.

Within this particular dropped-field equality pattern, a nonempty required
set needs one required field and one additional dropped field. Using the
same `kappa` for both shows the failure is about an original operand's
structure, not newly forbidden permissions or independent hidden witnesses.
No claim of minimality among all possible predicates is made.

Changing `C` too would repair this equality test by changing the problem:
the fixed original imported operand and its incidences would no longer be
retained. Choosing another `omega` would change the same-witness statement.
Neither operation is used here.

## 5. What actual source transport must account for

The [source-contract emission inventory §3.2](../design/2026-10-05-source-contracts-and-common-allowance.md)
retains a Name's original lexical/provider root, an immutable Record's full
field-provider tuple and sharing, a Call's whole carrier/receipt/entry/body/
consumer, and a Bind's shared result/rebind/state tuple. Its §3.3 checks
initial, response, raw-resumption and future-use admission independently of
the pending comparison. Section 3.4 requires certified legal transport with
fixed rigid imports and joint original `K,D` incidence.

The graft is a transformation of a structural value, not one of those source
admission constructors. It can remove original extra fields and their
subgraphs, apply opposite signed projections within Function arguments, and
create a fresh root whose recursive descendants still refer to a copied
visible root. Pure structural bisimulation tolerates this representation.
An original provider, invariant operand or typed path is a different live
incidence and needs its own certificate.

[Theorem C's lift §2.6](../design/2026-10-04-source-generated-callback-structural-theorems.md)
copies every old relation constructor with its entire old operand tuple and
adds total fresh derived coordinates at original scopes. Its proof therefore
transports the unchanged old tuple. It cannot be applied to replacing an old
operand `T` with `c_H(T)` without the primitive transport law at issue.
Source/runtime request substitution must also retain the same request map;
projection §5 establishes proof substitution, not commutation with a concrete
substitution that changes hidden-atom visibility.

The sound fallback stays exactly the original existential presentation:

```text
V is admitted iff exists T,omega:
    T <= U_H and all_i T <= W_i
    and Perm(T,omega) and Guards(T,omega) and Phi(T,omega)
    and A+(T) ~ V.
```

Deriving `V` as a view of the same assignment changes no old operand. This
formula claims exactness, not effective existential elimination. It needs
neither the false retraction above nor a new source rejection rule.

## 6. Bounded production correspondence

These inspected current owners delimit what can be claimed from actual
artifacts. Line numbers are locators for the hash-pinned files in §8.

| Owner | Inspected artifact | Consequence for this bridge |
| --- | --- | --- |
| `crates/yu-hir/src/module.rs:426`, `ResolvedExpr` | Exhaustive Lambda/Integer/Name/Error enum | No resolved Record, operation request, handler or ordinary Function-application node generates this residual source case |
| `crates/yu-solver/src/term.rs:170`, `TermView`; adjacent `TermNode` | Leaf/Component/LiveVariable, bounds and four-port polarized Functions | These current term owners expose no mandatory-Record node or structural graft on it |
| `crates/yu-solver/src/lib.rs:2894`, `SemanticFact` | Ordered original lower/upper term handles and fact ID | Potential source-to-operand anchors; not an interpretation of all residual `Phi` or source admission |
| `lib.rs:2881`, `ProvenanceEdge` | Cause-to-fact incidence | Retains provenance, but does not prove that changing an incident structural endpoint preserves the original primitive relation |
| `lib.rs:2858`, `AdmissionReceipt` | Store token/serial, constraint occurrence, cause, fact and accepted/duplicate delta | Certifies a store transaction; no received carrier, original runtime receiver, response or resumption tuple appears in this receipt |
| `lib.rs:10539`, `admit_lambda_fact` | Original parameter/result/body-effect incidence and negative argument-effect leaf; insertion followed by live constraint processing | Shows actual retained Function construction, not a query-independent caller admission or `K,D`-preserving graft certificate |

This table concerns these production owners only. It does not assert that
all legacy parser, inference, specialization or VM modules lack Records.
No runtime probe was performed. A parser Record spelling, term fact insertion
or store receipt cannot fill the missing source/runtime mapping by name alone.
Nor does lack of these constructors prove a successor source restriction or
a need for an additional runtime carrier.

## 7. Exact next gate and stop condition

Select one actual source-generated primitive clause incident to the varying
endpoint, and specify its complete ordered operands and immutable `(b,j)`
context. Identify which operands stay fixed, which are derived views, and
which retain original providers, binder/request identity, typed path and
joint `K,D` references. Then prove its same-witness truth transport and current
guard recertification under `c_H`, or give a source-derived violation.

The sufficient class in §3 closes this obligation only when the clause
actually has that operand form. The equality countermodel in §4 shows why
effectivity, extensionality, fixed permissions and retained metadata alone
cannot justify a generic proof. If an actual primitive requires the original
operand, retain the original existential witness rather than silently
rewriting the fixed import or granting a guard exception.

The worker stops at this frozen artifact. Unrestricted primitive generation,
all-context Function admission, Option 2 member interpretation, effectful
correspondence, source/runtime execution, complete residual decision and
principality remain open. No new language semantics, compiler work or shared
record promotion is authorized by this result.

## 8. Verification and checkpoint packet

Method: narrow source/design inspection, explicit operand-form induction,
and the two-field extensional countermodel. No tests, builds, executable
models, measurements, Git operations or delegation. Experiment processes and
measurement samples: 0. One output-only static whitespace/relative-link check
and a direct-input SHA-256 recheck are the verification budget. These checks
do not constitute independent review.

| Direct input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/design/2026-10-03-scoped-constraint-solving.md` | `a64ffaddf0f15b73e59b0eacb02d1e4c30331340ff55ed869e6112aa201633b4` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/progress/2026-10-05-residual-admission-retraction-proof.md` | `40929e3aa0509e357ec9c9f06db6e547362639eb945eb6e4058eb903060a54ef` |
| `notes/progress/2026-10-05-residual-admission-source-premise-audit.md` | `ac69d1696dbe023d0886d15c0bee0e5e21fca5a189ab89b9b79b3c96bc3587fd` |
| `notes/progress/2026-10-05-multi-atomic-record-projection-proof.md` | `28548a4f1702f997f625fd4bc8b5f0925247618155c731deecab2e8538613208` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `crates/yu-solver/src/term.rs` | `12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611` |

Proposed checkpoint message: `research: isolate residual admission operand transport`.
Exact output path: `notes/progress/2026-10-05-residual-admission-live-operand-transport.md`.
Claim/review class: conditional research and abstract extensional obstruction,
with bounded code correspondence; independently reviewed by
`compiler_referee` with no findings in the assigned scope. No source
counterexample or production gate closure is claimed.

Shared record changes to `tasks/current.md`, `tasks/research-lab.md`,
`notes/design/INDEX.md` and `notes/theory/` are deliberately deferred to the
primary/leased curator. Suggested delta after adjudication: distinguish the
proved operand-form sufficient criterion and the effective extensional
fixed-operand countermodel from the still-missing actual primitive
source-incidence/guard transport certificate.
