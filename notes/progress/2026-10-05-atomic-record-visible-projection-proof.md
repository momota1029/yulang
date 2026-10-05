# Visible image of one atomic open-Record residual

Date: 2026-10-05
Status: Unreviewed constructive research derivation; conditional scoped corollary
Baseline: `f65d68c5d43623f0d8a02194142828ec144755ab`
Implementation authority: none
Write scope: this note only

## Sources and exact claim class

The [open residual factorization record](../design/2026-10-03-open-residual-factorization.md)
§7.1 supplies the complete **unguarded** atomic-Record fiber and separately
conjoins original permissions, comparison guards and joint predicates on the
same witness. The [scoped structural projection record](../design/2026-10-03-scoped-structural-projection.md)
§§2–5 supplies the structural domain, signed greatest-fixed-point
availability, shared graph construction and opaque comparison theorem.
Neither source gives implementation authority.

The [finite residual playground](2026-10-05-residual-factorization-playground.md)
and [recursive residual playground](2026-10-05-regular-residual-factorization-playground.md)
check existential coordinate images over supplied finite assignments and
predicates. They do not implement `A+` or establish this set-image lemma.
The [guard-context playground](2026-10-05-residual-guard-context-playground.md)
tests synthetic contexts and failure ordering; it does not provide source
scope premises for this note. The pure structural FMP is already closed and
is not used or reproved here.

This note proves an exact structural image, including arbitrary regular
recursion in visible extra fields. The scoped conclusion is conditional on
explicit witness admission. No arbitrary guard, permission or `Phi` predicate
is eliminated by the structural result.

## Fixed domain and hypotheses

1. Work with finite contractive regular graphs of atoms, mandatory Records
   with finite unique-label field sets, and Functions. Functions have
   contravariant arguments and covariant results; Records have ordinary
   width and covariant depth. Atom comparison is identity only. Values are
   considered modulo rooted regular-tree bisimulation, as in the residual
   package. Graph sharing itself is not an observable equality constraint.
2. Fix one visibility frontier `H`, a hidden opaque rigid atom `kappa`, a
   visible primitive `Int`, and a Record label `a`. A visible graph contains
   no hidden atom. Additional atoms, if present, retain their fixed visibility
   and identity; the lemma also applies to the minimal alphabet `Int,kappa`.
   The label `a` is distinct from other root labels, by label uniqueness; it
   is not a type atom or a fresh label that must be absent at every depth.
3. The fixed successful quotient has one descriptor-free flexible root `X`,
   no lower bound, and exactly one supplied upper structural clause
   `X <: Record{a:kappa}`. There are no other structural bounds, alias
   constraints, effects or invariant constructors in this lemma. The
   original bound identity and immutable guard/evidence context are retained
   for the scoped corollary; their admission is a separate premise.
4. `A+` is exactly the signed construction of the projection source §3.
   Hidden atoms have neither sign available; visible atoms have both.
   Function availability requires its opposite-sign argument and same-sign
   result. Positive Records are always available and keep precisely the
   fields with available positive children. Negative Records require every
   negative child. Availability is the greatest Boolean fixed point, and
   projection connects one allocated node per available signed pair.

Under these hypotheses, define the unguarded fiber and candidate image:

```text
F = { T = Record(D,t) |
        D finite, a in D, t(a) = kappa,
        every other field is a contractive regular structural value }

R = { V | V is a visible finite-label contractive regular Record,
          a is absent from V's root labels }
```

Extra fields of `T` may share nodes, recurse mutually, or point back to its
root. These are assignments in the same closed regular graph domain, not
independently solved flexible fields. §7.1 gives exactly
`F = {T | T <: Record{a:kappa}}` before permissions and guards are conjoined.

**Bounded image lemma.** Modulo rooted bisimulation,

```text
{ A+(T) | T in F } = R.
```

The root is positive Record, so its projection is defined for every `T in F`.
This is a set-image theorem for this one residual fiber; it is not general
projection elimination or a complete principal inference theorem.

## First inclusion: every fiber witness projects into R

Take any `T = Record(D,t) in F`. At its positive root, availability is true
independently of its children. The required child is the hidden atom
`t(a)=kappa`, whose positive availability is false. Consequently the output
has a Record head and drops the root field `a`.

The construction retains a subset of finite `D` and follows only available
signed child states. Every atom reachable in that output is visible: a
hidden atom has no available signed state and therefore cannot be an output
node or the endpoint of an output edge. The cited shared construction yields
a finite contractive regular graph. Thus `A+(T) in R`.

This argument does not unfold recursion to a finite depth. In particular,
availability changes caused by a negative occurrence of the root, through a
Function argument, can remove extra fields; they do not restore `a` or
introduce a hidden leaf. Self-edges and mutually recursive extra fields are
handled by the same greatest-fixed-point construction.

## Visible graphs are fixed by either signed projection

Let `G` be any closed visible finite contractive regular graph. Assign true
to both signed states of every node of `G`. This assignment satisfies all
availability equations: every atom is visible, and every required child is
among those true signed states. Hence the greatest fixed point makes all
these states available, including states on arbitrary constructor cycles.

All Record fields are therefore retained at both signs. For each output
signed node `(n,p)`, relate it to the original node `n`. Heads, atom
identities, Record labels, Function argument edges and result edges match
under this relation; only the internal sign may change. This is a rooted
bisimulation. Thus `A+(G)` and `A-(G)` are each bisimilar to `G`, with no
acyclicity or depth bound.

## Second inclusion: graft a hidden field without redirecting old cycles

Take any `V in R`, represented by a finite closed visible graph `G` rooted
at a Record node `v`, with root labels `E` and field targets `v_f`.
Construct `Graft_a,kappa(V)` as follows:

1. Keep a closed copy of all nodes and edges of `G`. Sharing and every
   original back-edge remain inside this copy.
2. Add a fresh Record root `r`, distinct from every node of that copy, and a
   leaf with atom identity `kappa`.
3. Give `r` the fields `a:kappa` and, for each `f in E`, `f:v_f` into the
   retained copy. Do not redirect any old edge targeting `v` to `r`.

Call the rooted result `T_V`. It is finite and contractive: old constructor
cycles are unchanged, and the fresh root adds only constructor field edges.
Its labels are `E union {a}` and its `a` child is exactly `kappa`, so
`T_V in F`. The upper comparison asks only for `a` and then the atomic
identity `kappa <: kappa`; extra fields are unasked.

The copied graph is a closed visible subgraph with no edge into the fresh
root or hidden leaf. The availability equations on its signed nodes
therefore have the all-true solution just proved, also within the whole
grafted graph. More explicitly, making every copied signed state true,
`r+` true, `r-` false, and both hidden-leaf states false is a fixed point of
the whole availability equations. The greatest solution keeps all copied
signed states true; the hidden leaf is necessarily false and `r-` is
necessarily false because of its required hidden child.

Projection of `r+` drops `a`, keeps all fields `E`, and attaches each of them
to the corresponding positive projected target in the old copy. Relate
`r+` to `v`, and every copied projected signed node `(n,p)` to original
`n`. The root labels and each child edge match, and the copied-node relation
is the visible-graph bisimulation above. Thus `A+(T_V)` is bisimilar to `V`,
proving `R` is contained in the image.

For example, if `V = mu z.Record{b:z}`, use a copied root `v` with `b:v`
and a fresh `r` with `a:kappa,b:v`. The `b` edge of `v` still targets `v`.
The positive projected fresh root is bisimilar to `V`. Reusing `v` itself
as the new hidden-bearing root would change negative availability on paths
through Function arguments; the closed-copy construction avoids that
unneeded premise. Nested occurrences of label `a`, such as
`Record{b:Record{a:Int}}`, remain permitted and preserved.

## Permissions and guards conjoin on the original witness

Let `omega` retain the package's original symbolic/evidence coordinates and
let

```text
Adm(T,omega) = Perm_Q(T,omega) and Guards_j(T,omega).
```

`Guards_j` checks the original bound at its root and every comparison it
derives in the unchanged context `j`; here the structural upper rule derives
the required `a` child comparison `kappa <: kappa`. Being hidden at frontier
`H` does not assert permission or admission at `X`'s local checking scope.
Admissibility of a syntactic bound alone is not universal admission of its
regular assignments.

For arbitrary supplied permissions and guards, the exact filtered image is

```text
{ A+(T) | T in F, exists omega. Adm(T,omega) }
  = { V in R | exists T in F, omega.
                 A+(T) bisimilar to V and Adm(T,omega) }.
```

The structural lemma justifies restricting the right side to `R`. The
existential original-witness predicate is retained, not reconstructed from
projected coordinates. A further original `Phi_q(T,omega)` is conjoined
inside the same existential; it cannot use an independently chosen witness.
This equation is an exact characterization, not an effective elimination
of that existential predicate.

A sufficient **conditional scoped corollary** recovers the full set `R`:
for every `V in R`, the particular `T_V` constructed above has some
`omega_V` satisfying its original permissions and guards. Then both
structural inclusions apply to admitted witnesses, and the filtered image
equals `R`. Explicit sufficient conditions for that graft-admission premise
are:

- The permissions on `X` admit the rigid identity `kappa` and every visible
  rigid identity reachable in every admitted candidate `V`. To claim all of
  `R` when arbitrary visible rigid names are in its alphabet, those names
  must all be permitted; merely permitting `kappa` is insufficient.
- In the original bound's immutable context, the supplied guard admits the
  root comparison for every constructed `T_V` and the derived required
  `kappa <: kappa` comparison. This is an explicit assumption about those
  original witnesses, not a new guard exception or a claim that guards
  inspect only constructor heads.
- If `Phi_q` is included, the same `omega_V` must satisfy it jointly with
  permission and guard admission. No such total joint admission is proved
  by the structural construction.

Over the minimal alphabet `Int,kappa`, the graft has only the rigid atom
`kappa`; `Int` is primitive. Local permission for `kappa`, together with the
two original comparison admissions for each graft, suffices when there is
no other joint predicate. The visible projection does not expose `kappa` to
an outer endpoint. Projection §5's omission safety is distinct from
admission of the original residual comparison itself.

## Failure cases and omitted generalization

If `X` cannot contain `kappa`, every original witness is forbidden, even
though the unguarded image contains `{}`. A denied original root or required
child guard likewise invalidates that witness. Such failures retain their
permission or `GuardFailure` classification; they are not atomic mismatches.
A permission excluding a visible rigid atom can remove Records containing
that atom from the image. An arbitrary `Phi` can restrict the fiber or make
the joint image empty. Without admission premises, equality of the joint
image with all `R` would therefore be false.

If `kappa` becomes visible, `a` is retained and the asserted image changes.
Substituting `kappa := Int` is not an operation commuting with this frozen
opaque projection. Adding lower bounds can forbid the graft's labels or
types; adding alias/evidence constraints can prohibit the fresh-root
representation. Non-identity atoms, optional fields, lattice types, declared
hidden bounds, effectful contracts, interacting flexible roots, invariant
families and source-derived `K,D` require separate statements. Functions
inside closed extra fields are covered by the cited signed structural
construction, not by an effectful Function compatibility theorem.

There is no source-generation theorem, effective principal joint projection,
scheme syntax, solver strategy, production change, lifecycle result or
implementation approval in this note. Independent review remains required
before promoting the derivation's status.

## Verification and commit packet

Verification budget: output-only whitespace and local source-locator checks;
no tests, builds, executable checker, measurements or Git operations.
Result: the note has a final newline, no trailing spaces or tabs, and all
five relative Markdown source links resolve to existing files. The five
source dependency hashes were rechecked and remain equal to the table below.
The primary owns independent review, scope inspection and integration.

Exclusive path:
`notes/progress/2026-10-05-atomic-record-visible-projection-proof.md`.
Proposed commit message:
`research: derive visible image of atomic open-record fiber`.
Claim status: unreviewed exact structural derivation; scoped equality only
under explicit graft-admission premises; no implementation authority.

Read dependency SHA-256 values at construction:

| Dependency | SHA-256 |
|---|---|
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-residual-factorization-playground.md` | `cced08da09765c78f2be2d7e2a7484a3b2c0e0e3d3605c70b1f9a0dcf3b295cb` |
| `notes/progress/2026-10-05-regular-residual-factorization-playground.md` | `ca62d5f005808bcc8b570bb315eccb8121eea52858d20d056883469dcf2c3427` |
| `notes/progress/2026-10-05-residual-guard-context-playground.md` | `f68832f06682b54f8c26a256cc88f195c6001ba0a5395a4a443645631eee9f78` |

These are hashes of inspected source files, not a child certification that
the branch or its outbound history is unchanged. The primary rechecks them
against the integration baseline. Dirty shared coordination and exploratory
handler records do not govern the proof.

Shared record deltas deliberately deferred to the primary:
`tasks/current.md`, `notes/design/INDEX.md`, and any inference theory/status
map. Proposed delta: record the exact structural image as pending independent
review, distinguish its conditional guard/permission corollary from full
joint projection, and retain production and source-context gates as open.
