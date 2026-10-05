# Ordinary-value binding annotations: source-rule derivation and exact gap

Date: 2026-10-05
Status: unreviewed research; conditional source-judgment derivation and failed route
Baseline: `fd6a1e9b4a77f79df37af6b92d4fc4b79f2e40f7`
Lease: this file only; absent at initial inspection; no overlapping visible edit
Method: constructive derivation from selected boundary semantics and typed-core binding/name rules
Implementation authority: none

## Objective and governing sections

Derive the ordinary-value binding/lookup link needed by the
[annotation-sequence result](2026-10-05-approved-annotation-boundary-sequence.md).
Use the approved `source-annotation-boundaries/q1/d1` decision, concrete
compatibility §1, charter §§1–4, and typed-core §6's interface normalization,
structural local-binding/name rules and explicit annotation-open clauses.
Typed-core §§3–4 supply evidence-bearing descriptors and bind transport;
§7 supplies a sufficient representation-preserving checking fragment.

Source grammar is governed by the syntax architecture's Authoritative
“canonical `Statement`のbinding / use declaration拡張”, “canonical
`Pattern`のtrailing `TypeExpression` annotation wiring” (`PTA-G`), and
“standalone `TypeExpression`のnamed record type primary” sections. The syntax
reference and existing fixture are inspected correspondence evidence.

The selected decision fixes the current-endpoint query, target export and
retention of preceding/local realization evidence. It forbids intermediate
concrete adaptations without source boundaries. It does not infer `A <: C`
from concrete successes `A <: B` and `B <: C`. It explicitly does not change
the grammar to make `x as int as str` two boundaries. The pending Function
call-view question is neither read nor used here.

## Established inputs and reduced premise

Typed-core §6 supplies these rules relative to known lexical interfaces:

```text
Gamma(x) = Value(A)
  => synth(Name(x)) = (Value(A), name x, result(name x))

Result(I_r) = Comp(E_r,A_r)
Gamma' = Gamma[y : Value(A_r)]
synth_Gamma'(body) = (I_body,d_body,n_body)
  => local bind uses bind(y,n_r,n_body)
```

It follows that the binding/name link needs no new inequality: once the
annotation-bearing initializer has a valid result derivation at `B`, the
existing binding rule introduces `y : Value(B)`, and the next initializer
`Name(y)` synthesizes endpoint `B`. This removes the sequence theorem's
separate exact-forwarding premise for this ordinary binding route.

The remaining premise is **obtaining that annotated initializer derivation**.
A successful local query and a target name do not constitute a construction
of a typed data/computation descriptor in the displayed core. In particular,
§6 expressly leaves full annotation checking and admitted conversions open.
The approved export decision tells us the result of a successful source
boundary; it does not prove that every resolver evidence object supplies the
required typed initializer or its operational soundness.

## A sufficient rule using the existing checking fragment

Fix one well-formed source world `W` and assignment `nu`. Endpoints, profiles,
typed paths and any symbolic `K,D` remain jointly interpreted there. For a
simple nonrecursive local binder `y`, assume:

1. The source contains the actual admitted pattern annotation occurrence
   `b` in `my y: tau = r`; `tau` has an admitted **ordinary value target**
   interpretation `B` in its lexical scope. This assumption includes type-name
   resolution and target path/profile interpretation, not just parsing.
2. `r` already synthesizes `(Value(A),d_A,n_A)` with
   `n_A = result(d_A) : Comp(empty,A)` and retained evidence graph `R`.
3. The endpoint-dependent resolver at this occurrence returns admissible
   evidence `rho` for precisely `A <: B` in the actual context under `nu,W`.
4. At this occurrence that evidence certifies typed-core §7's proposition
   `VIncl(A,B)`: the **same decorated values** meet the target interface,
   retaining their original profiles, paths, lineage and joint constraints.
   This is an additional sufficient certificate property; it is not assumed
   of all successful concrete comparisons.
5. `y` is the lexical binding selected by the later name occurrence; no scheme
   instantiation, recursive publication, destructuring or intervening
   shadowing changes that lookup. The evidence graph links this name to the
   annotated initializer. It is not reconstructed from endpoint equality.

Hypotheses 1–3 admit the boundary and its selected query/export. Hypothesis 4
selects an already defined sufficient checking case. Hypothesis 5 is the
ordinary lexical/descriptor correspondence used by §6, scoped here to a
sequential nonrecursive binding. None chooses a whole-carrier conversion.

Use `check_b(d_A,rho)` as proof notation for §7's retained-value check label,
not a new surface expression, runtime primitive or compiler constructor.
The sufficient annotated-binding rule is:

```text
Gamma |- r => (Value(A), d_A, result(d_A)) ; R
Gamma |- tau => admitted ordinary value target B
Resolve_b(A <: B ; nu,W) = rho
rho certifies VIncl(A,B) at b
-------------------------------------------------------------------
initializer at b:
    d_B = check_b(d_A,rho) : Value(B)
    n_B = result(d_B)      : Comp(empty,B)
    R_B = R plus (b, A <: B, rho), linked to d_A

Gamma_B = Gamma[y : Value(B)] with initializer evidence reference R_B
Gamma_B |- body => (I_body,d_body,n_body) ; R_body
-------------------------------------------------------------------
my y: tau = r; body:
    I = Computation(E_bind,A_body)
    d = reify(bind(y,n_B,n_body))
    n = Normalize(I,d)
```

`A_body` is the result endpoint of `Result(I_body)`. `E_bind` remains governed
by the existing bind relation. This notation neither invents a row union nor
adds an effect-support interpretation. The complete derivation retains
`R_B` and the body's references to it. The annotation appears on the source
pattern; the proof label on the initializer result is its checking
elaboration at that binding, not a rewritten source program.

**Derivation.** Hypothesis 4 permits §7's check of `Value(A)` against
`Value(B)` without executing a conversion. The selected boundary rule
exports `B` and adds `rho` while retaining `R`. `Normalize(Value(B),d_B)`
is `result(d_B)`, hence its result endpoint is `B`. Applying §6's ordinary
binding rule therefore gives `Gamma_B(y)=Value(B)`. Applying the name row
under `Gamma_B` gives `(Value(B),name y,result(name y))`. §§3–4 retain the
initializer and original evidence through the descriptor/environment
correspondence and bind; name lookup does not delete that predecessor.
No inequality is generated by bind or lookup themselves.

This is a **conditional source derivation for the representation-preserving
checking subcase**, rather than the sequence theorem's arbitrary supplied
forwarding spine. It constructs the local-binding/name skeleton from
explicit source occurrences and §7's sufficient check. It remains relative
to admitted target interpretation and local inclusion evidence. The producer
does not claim independent review, complete annotation adequacy or production
adoption. §7's scoped erasure theorem applies only when its original-contract
and typed-transport premises also hold; it does not erase the source
annotation or its evidence.

## The two-boundary witness and what is still conditional

Use the established concrete comparison discriminator as endpoint notation:

```text
A = {foo?: string}   B = {}   C = {foo?: int}
A <: B succeeds     B <: C succeeds     A <: C fails
```

In a supplied sequential local scope with `Gamma(x)=Value(A)`, the source
shape is:

```text
my y: TB = x
my z: TC = y
z
```

`TB` and `TC` stand for admitted ordinary value target forms denoting `B`
and `C`. Identifier type syntax is admitted, but no declarations or type-name
interpretation establishing those particular denotations are supplied here.
This is a conditional source schema, not a claimed accepted raw program.

With the sufficient certificates above at both annotations, the first
initializer has result endpoint `B`, so its binder installs `Value(B)`.
Lexical lookup of `y` supplies `B` to the second query. Its initializer has
result endpoint `C`, so `z` installs `Value(C)` and the final lookup exports
`C`. The retained graph contains both actual occurrences and both queries,
with `rho2` linked to the earlier initializer through `y`. There is no
`A <: C` obligation. This derivation uses bind/name rules to discharge
forwarding, rather than positing forwarding separately.

The three recorded concrete outcomes do **not** prove either `VIncl`
certificate. Semantic inclusion of the same decorated values is a stronger
premise than the selected general endpoint-dependent query. Even if two
such inclusions were supplied, their semantic composition would not prove
that the resolver succeeds on `A <: C`; no completeness equivalence between
`VIncl` and this resolver is assumed. The optional-record witness therefore
remains conditional for this source rule. Its needed local realizations may
instead require an admitted conversion, whose construction is outside the
checking fragment.

There is a separate source-target limitation. The Authoritative named-record
grammar specifies `TypeRecordField := Identifier ... Colon ... TypeExpression`.
It admits empty `{}`, but supplies no optional-field punctuation between the
identifier and colon. The inspected direct parser likewise requests a colon
after the field identifier. Therefore `{foo?: int}` is not established as a
recovery-free optional-field target spelling by this grammar; parsing with
recovery would not establish that semantics. No grammar change or alias
interpretation is proposed. Type atoms and binding annotation syntax alone
do not discharge the semantic denotation premise for `TB/TC`.

## Smallest failed route and the exact general bridge

One annotated binding already exposes the omitted premise:

```text
Gamma(x)=Value(A), A != B
my y: TB = x
y
```

Without the local check/transfer derivation, §6 gives the initializer
`result(name x) : Comp(empty,A)`. Its ordinary bind therefore installs
`Value(A)`. Installing `Value(B)` while retaining that unmodified initializer
judgment is not an application of §6's rule. An endpoint relabel and stored
`rho` alone do not prove that the bound value meets `B`. This is a failed
proof construction, not an independently observed runtime counterexample.
It is minimal in annotation count: zero annotations have no target-transfer
obligation. Two annotations remain minimal for the nontransitivity
discriminator.

For general local concrete realizations, the precise missing premise is a
form-specific judgment at the actual binding occurrence:

> From the admitted RHS derivation, admitted ordinary target `B`, and the
> actual local resolution evidence `rho`, construct an annotation-bearing
> initializer result derivation `n_(b,rho) : Comp(F_b,B)` at its original
> scope/path/profile, retaining the predecessor and local evidence in the
> same `nu,W`.

`F_b` must be derived if realization executes a conversion; this note does
not assume that it is empty or that every adaptation is inert. Once this
premise is provided, ordinary bind and lexical name yield the exact endpoint
link above regardless of the supplied initializer effects. Operational
soundness additionally needs that local realization to preserve the selected
source observations and required future-use/resumption correspondence.
No adapter equation or typed runtime graph is constructed here.

The representation-preserving route discharges the result-derivation premise
using §7 when `rho` certifies `VIncl`. General `rho -> n_(b,rho)` construction
and exact source-target denotation remain open. This is a reduced proof
obligation, not evidence that the chosen semantics are inconsistent. No new
semantic question is needed for target export, evidence retention or ordinary
lookup: these are already selected. A question is warranted only if the next
source-target/realization investigation finds an actual unselected language
choice; lack of a construction alone is not such a choice.

## Evidence quality, failure conditions and omissions

This method is symbolic derivation and bounded source inspection. There is
no executable checker, independent Oracle experiment, random seed, input
enumeration or measured performance. The concrete outcomes are inherited
from the committed obstruction/sequence notes. The proof and §7 share their
given lexical interfaces, admitted targets, joint world and retained typed
evidence; they do not independently validate those source premises.

Symbolic failure mutations discriminate three shortcuts: preserving `A` in
`Gamma(y)` makes the second boundary query `A <: C`; removing predecessor
evidence violates retention; applying a bare bind at `B` while its RHS remains
typed at `A` violates the result-binding premise. These are inspected proof
failures, not executed mutation tests. No second equivalent toy probe is run.

The sufficient theorem does not apply to unadmitted targets, failing local
queries, evidence not certifying the claimed inclusion, inconsistent joint
assignments, altered source roles or an incorrectly resolved/shadowed name.
The general route remains open when local realization is missing even if
the local query succeeds. Pattern destructuring, recursive groups, schemes,
parameter entry, computation-target annotations, Function/callback/effect
conversion, imports/State, source-wide soundness/principality, compiler
acceptance and production inference are omitted. No production owner or
call-view result is inferred from this mathematical note.

Recommended next action: obtain one admitted source-target interpretation
and the occurrence-specific local initializer realization for the
optional-record discriminator, or identify a concrete already admitted
value-target discriminator. Review the sufficient bind/name derivation
separately from that missing general realization premise.

## Frozen dependencies and checks

All direct dependencies were read from the pinned baseline. Git blob IDs:

| Path | Baseline blob |
| --- | --- |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `1b87624d94d01aff386f31acb81cc40b2bb3b441` |
| `questions/2026-10-05-source-annotation-boundaries/receipt.md` | `54f566a38c5d1314b800824959e081ff663e2310` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `81e5fefa637b66f80999a4e3e4a0c84edae39171` |
| `notes/design/2026-09-09-successor-expression-structural-tails-draft.md` | `c036c38a959656e12326046a8da57309379e8fa3` |
| `notes/progress/2026-10-05-approved-annotation-boundary-sequence.md` | `cd25e064659de7446b4960ea71d3a4da65a64179` |
| `notes/progress/2026-10-05-source-adequacy-concrete-transitivity-obstruction.md` | `e82b4b24eb16440980d66ed95e89658f05d60a9c` |
| `syntax-reference/en/src/statements/binding-use.md` | `572fc3c817cc93530380427f11acc2168ca1054c` |
| `syntax-reference/en/src/patterns/type-annotation.md` | `88a9e51d2cda8c0d060d87804edca4e145e75c10` |
| `syntax-reference/en/src/types/named-record-type.md` | `1d00e2c7f47487494cfb0976d1df98011572b3a0` |
| `syntax-reference/en/src/types/type-expression-core.md` | `865ecb66d119458bbfc98b3ec12e9e48119fd1ac` |
| `crates/yu-syntax/src/declaration/binding.rs` | `165ad487cfebde8b40327a4144ac870782fc9acd` |
| `crates/yu-syntax/src/tests/declaration/binding.rs` | `aae68a8f9b141ceca2a562061acb0921df29192d` |
| `crates/yu-syntax/src/type_expr/record.rs` | `43b8e742eab56604030c44ecf4d5793c9f6d476e` |

Checks: initial `git rev-parse HEAD`, read-only branch/status and absence of
the leased path; bounded baseline `git show`, `rg` and `sed` inspection;
Python recomputation using `git hash-object --stdin` without `-w` for every
listed current dependency, all matching the baseline. Final dependency
revalidation and note whitespace inspection are recorded in the submission
packet. These establish snapshot/text integrity, not independent proof review.
No Git mutations, compiler edits, builds, tests, executable probes, formatting
or generated outputs. At most four lightweight command processes were launched
concurrently for independent reads. CPU time, peak RSS and exact wall time
were not measured; no heavyweight compute was used. Searches were bounded to
the listed forms and sources, not an exhaustive audit of all type encodings.

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-binding-annotation-rule-derivation.md`.
- Baseline SHA: `fd6a1e9b4a77f79df37af6b92d4fc4b79f2e40f7`.
- Changed dependency hashes: none observed; primary revalidates before integration.
- Claim/review status: conditional representation-preserving source rule;
  ordinary bind/name forwarding consequence; precise failed general route.
  Unreviewed research only; frozen on submission; no independent review claimed.
- Checks already run: bounded source/rule inspection and 16 direct dependency
  blob comparisons; no compiler checks requested or run.
- Artifact hash: reported externally in the submission packet to avoid a
  self-referential content hash.
- Proposed message: `research: derive ordinary binding annotation forwarding and delimit realization gap`.
- Shared-record deltas left for primary/curator: replace the separate ordinary
  bind/name forwarding hypothesis with its derived consequence once a valid
  target-result initializer is supplied; record §7's sufficient inclusion
  subcase; keep admitted target interpretation and general annotation-local
  realization open. Do not promote the optional-record schema to production
  source acceptance or close recursive-group/source-wide adequacy.
