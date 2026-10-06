# INIT_VALID: imported scalar root and retained aliases

Date: 2026-10-08
Pinned baseline: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`
Branch assigned: `research/simple-sub-intrusion`
Status: frozen research-only derivation; compiler-referee review passed after one premise-completeness repair
Claim class: bounded source-constructor characterization, conditional extension lemma and unproved punctured seed schema
Semantic / implementation authority: none
Exclusive lease: this note only

## Objective and result

Try to construct an actual initial imported environment, retaining an import
alias and a distinct source binding alias, before adding a punctured Call.
The method is a direct derivation from the fixed literal, Name, Normalize and
Bind constructors, followed by examination of the independent import/world
leaf. No executable checker, compiler test, build, Oracle or solver is used.

The derivation constructs a concrete supplier descriptor, the import syntax
record, and the exact shared alias graph. It does **not** construct an
`EnvStore`/`JointWF` witness: the first missing semantic inference is export
installation into the importing world under `Imp_Delta`. The inspected
source treats that predicate as a supplied independent leaf. Its required
world extension law is not derived by literal construction or Name transport.
This is an obstruction to this derivation from the named clauses, not a
source counterexample, impossibility theorem or choice of language meaning.
The later `ignore` Call is only a seed schema: its additional Literal,
Lambda, Bind and joint environment-extension premises remain unproved.

Unlike the earlier no-import nested and identity traces, this attempt has a
genuine cross-module root in a nonempty environment. The supplier is scalar,
so the first obstruction cannot be attributed to universal membership of an
imported Function. No complete member-environment premise is assumed.

## Exact governing sources and accepted decisions

All repository inputs were read from the pinned revision, not another
worker's unfinished files. Links below locate those files; claims use their
baseline contents.

| Source | Governing clause used |
| --- | --- |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.1–2.2,3.1–3.6 | Independent primitive/descriptor interpretation; same whole tuple; Name retains resolved roots; immutable aliases retain providers; uncertified opaque imports excluded from the source-base theorem; rigid imports fixed under use transport. |
| Same source §§6.1–6.3,7–9 | Independent allocation certificates retain every original import/declaration endpoint. They are premises of common-export factorization, not import-world constructors. Source labels do not determine exhaustive membership. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6,9 | Name copies the lexical interface; `Normalize(Value(A),d)=result(d)`; binding executes the RHS then rebinds its result. A Value parameter supplies the post-entry value interface, not the complete incoming carrier contract. |
| [Initial-context construction](2026-10-06-initial-context-source-construction.md) §§3,4.1–4.3,5–6 | One registered source graph and one X; semantic imports supply `Imp_Delta`; aliases retain the same provider reference; Lambda and Bind emit their body/image/state relations; PCInit-source requires every local relation and import/world leaf to hold. Hole-dependent source captures remain open. |
| [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) §8, named subsections “Rigid-hole proof schema”, “Conditional open-graph route”, “Step-indexed open-world candidate”, “Source-state realization boundary” | Structural sharing is insufficient for EnvStore; ordinary imports and hole-dependent values require separate independent justification; arbitrary graph-shaped worlds and closed-program reachability each fail to characterize the selected domain. No primitive heap is assumed. |
| [DAG](../theory/successor-proof-obligations.md), PCINIT, INIT-WORLD, SEM-JOINT, INLET-CARRIER, INIT-VALID | PCINIT closes only the conditional structural schema. INIT_WORLD specifies filling-independent import/world clauses; SEM_JOINT interprets their single semantic family; INIT_VALID constructs an actual base. The latter gates remain open at this baseline. |
| [Architecture](../../docs/yulang3-architecture.md) §§4.2.2,7.2 | Semantic imports enter Resolve/Lower separately from syntax planning; parser header facts are not final semantic dependency authority; source/module/definition identities are structural, not offsets or session arena indexes. |
| [Syntax authority](../design/2026-08-20-yu-syntax-chasa-architecture.md), “Complete `use` declaration grammar and projection”, “Structured Use AST”, “Group expansion to HeaderImport” | A Single target accepts zero or one explicit alias; one complete leaf projects one record. Its alias spelling is retained; path/alias syntax does not resolve a semantic provider. |
| [HIR module slice](../design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md), “Product and phase boundary”, “Admission, resolution, and identity” | Supplied file/module identity, separate binding DefIds, module-local resolution; imports/module graphs excluded and `SemanticImports` only constructible as empty in this approved slice. It supplies no cross-module realization theorem. |
| [F5](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md) §§4–5,9,12 | Module references and local parameters remain distinct; source roots are not type-variable IDs; fresh scheme coordinates do not clone runtime providers or erase definition-use provenance. |
| [Approved inlet-domain answer](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md), decisions 1–5; [integrated receipt](../../questions/2026-10-05-production-function-inlet-context-domain/receipt.md) | All independently compatible punctured contexts at fixed original xi, including other programs/future use; callable and entire carrier holes; all other environment values jointly valid; no Q-dependent admission; Option 2 permits production-only members. Concrete environment clauses are explicitly still open. |

The [earlier initial attempt](2026-10-06-independent-initial-admission-construction.md)
§§2–3 and [source-profile construction](2026-10-06-source-profile-admission-construction.md)
§§7–9 already stop at profile/inlet/world premises. Their returning traces
are not reused as a new validity proof. None of the conditional research
sources above is promoted into an Authoritative production interpretation.

## Small source and exact identities

Use two ordinary source roots supplied by the module owner:

```text
supplier seedlib:
    pub seed = 0

importer client:
    use seedlib::seed as imported
    my alias = imported
```

The labels `supplier seedlib` and `importer client` identify separate source
files; they are not Yulang syntax. The lines within each file are ordinary
binding/use forms. The `use` syntax derivation has Plain form, two identifier
segments joined by `::`, Single terminal, exactly one alias `imported`, and no
version/anchor/glob. This is the selected grammar's uncomplicated import
case. No parser execution or production semantic acceptance is claimed.

Let L be the supplied source-loader/resolution evidence that this path reaches
the supplier's public `seed`. L is an **explicit unsupplied interface-link
dependency**; a header record alone is not L. This note chooses no loader
policy. Even granting L to focus the semantic research question, the import
validity step below remains unresolved.

Retain:

```text
M_s, M_c                 distinct source module identities
b_s, e_0                 supplier seed declaration and literal occurrence
u_i                      importer Use declaration/alias occurrence
b_a, e_i                 distinct importer alias declaration and Name occurrence
rho_s                    the original exported supplier descriptor/root
I_s                      the supplier's original Value(A_0) interface
sigma_s, sigma_c          original supplier/importer binder scopes
xi = (nu,K,D)             one original joint assignment and predicates
X                        all the above, C_s,C_0, environments and local witnesses
```

`A_0` is the original integer literal endpoint, not a new globally equated
type variable. Its original constraints remain incident to `e_0,b_s,rho_s`.
No source root or endpoint is recreated from the spelling `0`. The importer
binding `b_a` remains a distinct DefId from `b_s`: provider sharing does not
merge declarations. The import alias is a source route to `rho_s`; it is not
a fresh provider. Imported coordinates remain fixed; no importer freshening
renames rigid supplier identities or independently chooses K/D.

This is minimal within the chosen inventory of one supplier literal binding,
one cross-module Single import with explicit alias, and one additional source
Name binding alias. Removing the supplier loses constructive supplier data;
removing the import loses the cross-module premise; removing `b_a` loses the
distinct binding alias case. No global source-size minimality is asserted.

## Derivation and first missing rule

1. **Supplier literal.** Typed-core §6 supplies
   `I_0=Value(A_0)`, `d_0=literal(0)`, `n_0=result(d_0)`.
   Source-contract §3.2 supplies its original primitive relation. The semantic
   descriptor-typing fact for this literal remains the independently interpreted
   local constructor lemma required by §2.2; arithmetic inference output is not
   a substitute. Denote that local fact by `Lit_0(X)`.

2. **Supplier binding.** Register `b_s` once, retain the original relation
   between its body and exported root, and use Bind/Return at the supplier
   source configuration. The source reduction returns `d_0` and binds the
   supplier root. This gives a source descriptor and result-binding record
   under `Lit_0` and the original local binding rules. Public syntax does not
   by itself prove validity of the imported interface/world.

3. **Import syntax and identity.** The fixed Use grammar constructs the record
   described above. Given L, all imported references point to the one `rho_s`.
   This is a source-identity/link record, not a semantic admission certificate.

4. **Required import leaf.** Initial-context §4.1 now requires

   ```text
   Imp_Delta({rho_s},C_ext;xi,w_imp)
   ```

   at the actual importing scope/world. Its operands must jointly certify the
   original descriptor, scope and K/D incidence, shared roots/continuations,
   current imported frame ownership and activation order, and absence of live
   incidences for expired activations. This scalar graph has no supplied
   operations, continuations, handlers or imported live frames. Its nonempty
   imported environment and shared xi still require an independently justified
   import/world installation step. Empty frame components do not make the
   complete predicate true by definition.

5. **Alias, only after step 4.** Name/Normalize give
   `I_i=I_s`, `d_i=name(rho_s)`, `n_i=result(name(rho_s))`. Bind rebinds `b_a`
   to the **same** returned supplier descriptor/root. The registered `b_a`
   source node and its original endpoint constraints remain present. No new
   receipt, activation, provider or independent semantic leaf is introduced
   by this alias. Any further Name alias simply adds another retained edge.

Step 4 is the first missing semantic rule **after granting L and the ordinary
scalar constructor lemmas**. The inspected sources do not provide the
inference from supplier literal/export validity to `Imp_Delta` in an actual
client world, or the EnvStore/JointWF extension that consumes that leaf.
The exact requested instance is:

```text
supplier local Literal/Bind witnesses at rho_s on X
the original public interface/link L, preserving sigma_s/sigma_c and xi
an independently justified compatible importer base configuration
---------------------------------------------------------------- [not supplied]
Imp_Delta({rho_s},C_ext;xi,w_imp)
and a jointly valid installed importer environment at C_0
```

This display names the missing proof instance; it does not select a new
inference rule or define `Imp_Delta` as source-solution existence. Supplier
source construction removes the need to guess a provider body, but does not
remove the independent import-world relation. INIT_WORLD/SEM_JOINT are the
upstream owners of that relation, as the pinned DAG explicitly records.

## Conditional extension and punctured initial seed

**Conditional lemma.** Fix one independently justified semantic family for
descriptor, carrier, EnvStore/JointWF and Init. Assume its original Literal,
Name and Bind typing/world preservation rules; actual supplier witnesses and
L; and the import-installation fact displayed above on the same X. Then the
source binding `my alias = imported` extends the installed environment with
one distinct binding root referencing `rho_s`, preserving joint validity and
all original dependencies.

**Derivation.** Apply Name at `rho_s`, normalize the Value interface to Result,
and apply Bind to its returned descriptor in the current configuration.
Conjoin its original scoped constraints on X and retain the importer binding
record. The semantic Name and Bind preservation hypotheses supply the
EnvStore/JointWF judgments for that exact extension. There is no choice of a
second supplier witness. This is a conditional derivation, not a construction
of its import-installation hypothesis.

To make this environment part of a punctured Call, extend only the proof
candidate with ordinary source

```text
my ignore x = 0
ignore alias
```

The local literal `0` in `ignore` has its own occurrence and endpoint; it is
not the supplier's root despite equal spelling. At the distinguished Call,
puncture the callable and whole argument as H_f/H_a, retaining the actual
argument source computation

```text
J_a = result(name(b_a))
t_a = Delay(J_a)
b_a's returned descriptor/root reference = rho_s
```

The argument is the rebound Name computation, not the supplier literal's
original `result(literal(0))`. Thus source alias provenance is retained through
the exact whole carrier. The import/root/alias environment remains present
in the seed graph. H_f keeps its hypothetical checked interface for open
typing, with no semantic checked membership of an actual filling.

This display is an **unproved punctured seed schema**, not an actual
PCInit-source seed. Initial-context construction §§4.2–4.3,5 requires the
remaining `ignore` source relations as well as the imported/alias environment,
profile/local Call typing and independent whole-inlet fact. Write
`IgnoreLocal(X)` for the following explicitly expanded premises, all at their
original source scopes in the same registered X and the same xi:

- The body's distinct literal occurrence satisfies its original primitive
  relation and local descriptor-typing fact; its Value interface, literal
  descriptor and result consumer retain its own endpoint.
- The Lambda's original role, parameter root/interface and entry skeleton,
  body relation, capture references and result consumer satisfy the local
  Lambda equations. Where a complete advertised descriptor is required,
  the generated received-carrier/entry/post-entry-body/return image and its
  semantic bound hold jointly under the independent descriptor/profile
  interpretation. A constant body does not prove that bound.
- The `ignore` declaration's Bind satisfies its original whole result,
  current-state and pending-suffix relation, registering its distinct binding
  root at the original source scope. These witnesses are shared with the
  Lambda and retained Call graph, not projected and chosen independently.
- The same resulting configuration has an EnvStore/JointWF extension witness
  for the retained import, `b_a` and `ignore` roots together, preserving their
  original scopes, dependencies and shared world witnesses. Validity of the
  imported/alias subenvironment alone does not supply this extension.

`IgnoreLocal(X)` abbreviates these local obligations; it is not a new semantic
rule, an opaque context certificate or completed Function membership of an
actual filling. No new X, xi or supplier witness is selected to satisfy them.
The displayed source code generates their schema but proves none of their
semantic satisfaction claims here. In particular, puncturing the callable
does not erase the retained declaration/body relations.

Only conditional on `IgnoreLocal(X)`, the conditional imported/alias
extension, the original profile/local Call typing, the independent whole-inlet
fact for `t_a`, and satisfaction of every other remaining source relation on
that same X can PCInit-source assemble a source-base seed. The complete
carrier/inlet fact remains a separate premise; Value entry and the scalar
return trace do not prove it. Relating such a seed to the complete independently
specified Init predicate also requires the original
INIT_WORLD/ADMISSION_CLAUSES/SEM_JOINT contract. Closure remains conditional;
this note supplies neither an actual seed witness nor complete production Init.

No receipt/entry execution is needed to expose the import blocker. The
constant-body Call is an extension of this imported environment, not another
identity-return experiment. This note claims neither that ignore has a
completed member contract nor that the complete original row is inhabited.

## Independence, discriminators and omitted cases

The reference is the independently stated source clauses, not a numerical
oracle. The derivation shares their local descriptor and world-preservation
hypotheses. A checker encoding these hypotheses would test the supplied
alias rules' consistency; it would not prove export installation or the
source interpretation of EnvStore/JointWF. Oracle independence therefore
means no Oracle execution or inferred Oracle policy, not independence from
the source-rule premises.

The following are logical premise mutations; none was executed:

| Shortcut | Failure condition |
| --- | --- |
| Treat a complete HeaderImport record as a semantic import witness | Architecture §4.2.2 separates syntax facts from semantic resolution/interface inputs. |
| Treat a successful supplier Return as client-world validity | The missing import-installation/world extension is left unproved. |
| Set `Imp_Delta=true` because imported frame sets are empty | Erases descriptor/scope/joint environment obligations of the nonempty import. |
| Rename supplier rho_s during importer instantiation | Violates rigid import preservation; fresh type coordinates do not create a new provider. |
| Merge b_a and b_s, or clone rho_s per alias | Loses distinct source declaration/Name constraints, or breaks shared provider identity. |
| Check imported/alias values at H_f's target Function before puncturing | Reintroduces membership under test into context admission. This scalar import needs no such Function premise. |
| Add an imported closure containing H_f as a closed independent leaf | Initial-context §4.1 excludes this shortcut; it requires open-substitution/world evidence for the dependent external value. |
| Admit only imports realized by this scalar supplier | Narrows the approved domain and loses independently valid Option 2 providers and external worlds. |
| Conclude whole carrier validity from `J_a` returning 0 | Confuses source construction with the independent complete carrier/inlet judgment. |
| Treat the `ignore` source display plus Call/inlet premises as a realized seed | Omits its literal, Lambda, Bind and joint EnvStore/JointWF premises required by PCInit-source. |

There are no seeds, numerical ranges, finite-state enumeration or executable
mutation results. Coverage is this fixed two-module, acyclic, immutable scalar
graph and its unproved punctured extension schema. No recursive imports, callbacks
inside an imported value, hole-dependent external aliases, State/general refs,
operation instances, active/imported handler frames, returned latent Function
handles, raw resumptions, arbitrary external-world coverage, principal solving,
production conformance or source execution acceptance is proved. In particular,
this graph establishes no theorem about all imported environments.

The search was bounded to the named sources, their index locators and the
syntax import projection. No exhaustive repository/code search was performed.
Large combined reads were truncated; the sections used in the derivation were
subsequently read in bounded slices. A missing instance here is not a claim
that every possible repository or future source law has been ruled out.

## Checks, resources and recommended next action

Checks: pinned `git show` reads and narrow section/locator searches; direct
identity, scope, one-X/xi, hypothetical-hole and whole-carrier audits; baseline
dependency hashes and note-local link/whitespace inspection. These are producer
checks and do not count as independent review. No compiler edits, tests,
builds, whole-workspace formatting, manifests/lockfiles, shared records,
question bundle edits, child processes for computation, Git mutations or
background work occurred. Each shell/read process ran serially. CPU/RAM peaks
and total wall time were not instrumented; no long-running computation was
started. The assigned limit was one serial lightweight process and 15 minutes.

Review repair: the accepted compiler-referee MAJOR identified the omitted
`ignore` local relations. This one batched note-only repair makes them explicit
and downgrades the punctured extension to an unproved schema. The producer
checked the repair against pinned initial-context §§4.2–4.3,5, reread the
repaired paragraphs, scanned note-local whitespace and rechecked all 14 pinned
direct dependency hashes against HEAD and the worktree. The note is untracked,
so `git diff --check -- <leased path>` inspected no content; the direct scan
supplies the whitespace check. Delta review remains pending; these checks do
not independently certify the repair.

Recommended next action: have the INIT_WORLD owner extract the independent
export-installation clause and EnvStore/JointWF extension law for **this same
scalar rho_s, client import alias and b_a**, with its semantic family supplied
by SEM_JOINT. This tests a smaller instance before Function imports or another
carrier probe. No language choice or new rejection policy follows.

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-init-valid-import-realization.md`.
- Baseline: `8a3f7ecbc0aef25fd448593fea1cf8fd5891ddf4`.
- Dependencies: pinned hashes below; no dependency was modified by this worker.
  Repair recheck at HEAD `b0feba34ce65f8347ad66b15e1ffb005bf3b4d8b` found all
  14 direct dependencies unchanged in HEAD and the worktree. The integrating
  primary must recheck if those inputs move before acceptance.
- Claim/review status: frozen research-only bounded characterization and
  conditional lemma, with an unproved punctured seed schema; accepted
  compiler-referee MAJOR repaired and focused delta review passed with no
  findings. INIT_VALID remains open.
- Checks already run: the pinned reads and producer audits above, followed by
  note-local whitespace/link checks and pinned dependency hashing.
- Proposed message: `research: expose ignore local premises in imported seed schema`.
- Shared-record deltas intentionally left for primary/curator: INIT_VALID can
  cite the imported scalar/alias graph as a reduced construction target;
  INIT_WORLD still owes export-installation and joint environment extension;
  SEM_JOINT, INLET_CARRIER and production admission remain open. No edits to
  task, theory, index or authority records are proposed as gate closure.
  The punctured `ignore` extension must be recorded only as a schema whose
  additional local/EnvStore/JointWF premises remain unproved.

### Pinned direct dependency SHA-256

| Dependency | SHA-256 at pinned baseline |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `docs/yulang3-architecture.md` | `76b59a473c84a0654a40b7598c9a2d4ce54eeb512c6aa3f5213e95aa8fab44a5` |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md` | `494a6973ced88a031688213990ea380e64cb74fea3bb1396236a8d1bb911f11a` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |
| `notes/progress/2026-10-06-independent-initial-admission-construction.md` | `4feb8131e9360ba8508b0eace82d882e446433d5b5f75beee402027e4986284f` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/design/INDEX.md` | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |
