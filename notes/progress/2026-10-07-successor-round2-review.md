# Successor round 2: independent review and integration

Date: 2026-10-07 (repository continuation date; session UTC 2026-10-06)
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Status: reviewed restricted research and default-off shadow implementation
Authority: no new language semantics or production inference authority

## Result and exact gate accounting

This continuation directly attacks the remaining original source kernel,
recursive descriptor introduction, and effective joint projection. It gives
explicit local constructions and falsifies specific shortcuts. Neither
independent reviewer found a correctness or conformance finding in the frozen
packet. **No unrestricted semantic DAG node is newly closed.** The ledger
retains the existing six CLOSED nodes and does not inflate its conditional
count with another name for an unresolved premise.

The constructive gains are:

1. [Whole-contract original lifting](2026-10-07-successor-original-kernel-construction-round2.md):
   construction before observation choice; original typed maps, whole Call
   image and all licensing witnesses retained. The explicit OC-Call-Intro
   candidate identifies original contribution-domain closure, static owner
   introduction and joint incidence coherence as the actual semantic cut.
2. [Recursive certificate construction](2026-10-07-successor-recursive-coinduction-round2.md):
   the actual two captured providers, exact pending suffix and one joint
   original witness form a direct certificate candidate. Unfolding plus
   postfixedness fails to prove absorption even for the two-member swap.
   A sound ordinary two-closure introduction is an alternative to the
   finite-failure-reflection route, not an additional mandatory gate.
3. [Finite incidence and scoped orbit projection](2026-10-07-successor-effective-projection-round2.md):
   finite relational context syntax constructs its own context carrier;
   equality-only hidden atoms admit exact projection at their original binder
   positions with whole-tuple correlation and witness strategies. An explicit
   decidable Record-chain primitive shows why pure FMP plus finite syntax and
   pointwise decidability cannot imply a computable complete joint bound.
4. [Structural alpha implementation](2026-10-07-shadow-interface-alpha-round2.md):
   the already closed CI_ALPHA construction now has a bounded default-off
   Rust implementation and a separately checked inverse certificate. Its
   caller-supplied graph is not asserted to be a complete semantic interface.

No countermodel in these packets is claimed to be an admitted Yulang source
or two complete competing Authority-consistent language meanings. No new
user-decision blocker is introduced. Current upper-output protection,
provider-owned marks, actual callable roles and Option A/2 remain unchanged.

## Independent initial reviews

The primary froze the ten files below before either verdict, checked 805
tracked rule/design/question/progress dependencies against the baseline Git
bytes, and submitted the same packet to two read-only reviewers. They
independently checked all ten SHA-256 values. Neither saw the other verdict
before returning its initial result. Producer explanations and passing tests
were not treated as authority. No reviewer ran Git, Cargo, builds or probes.

### Compiler-referee

Agent: `/root/round2_compiler_referee`; configured role model
`gpt-6.1-sol`, reasoning `medium`.

Verdict: **no BLOCKING, major or minor correctness findings within the
expressly restricted scope**. Review covered all three proof/checker pairs,
the alpha module, its tests, feature registration and progress record.

The review independently checked that parent contract construction precedes
the universal family observation; empty membership cannot create ownership;
licensing inversion retains the input license and needs exhaustive original
last-rule elimination. The stronger whole-carrier inlet is distinct from
the selected source argument diagonal. K-Owner, OC-Call-Intro and original
incidence are still unproved, rather than supplied by certificate syntax.

For recursion, the review checked the exact receipt/entry/rebind/Return suffix,
fixed admission, original shared witnesses and all C1–C5 responsibilities.
The union of postfixed certificates supplies a greatest certificate meaning,
not absorption into an arbitrary independently interpreted fixed point.
Source finite derivations remain a different judgment. The swap discriminator
is valid at its algebraic scope; no member-validation closure follows.

For projection, the finite context bound and update discipline were checked
separately. Equality orbits retain original quantifier order and earlier-only
witness strategies. Arbitrary non-name predicates and recursive operators
retain their independent obligations. The Record-chain halting obstruction
concerns a mathematical extension's decision/reflection property, not finite
residual syntax or Yulang undecidability.

For Rust, the review checked exhaustive sort-preserving enumeration, structural
encoding of all ordered fields, exact-budget versus incomplete search, both
inputs' validation before exhaustion, empty input, and inverse-map verification.
No incomplete minimum or semantic-equivalence result escapes. Graph byte size
and generic comparison cost remain outside the node/candidate resource bound.

### Spec-auditor

Agent: `/root/round2_spec_auditor`; configured role model
`gpt-6.1-sol`, reasoning `low`.

Verdict: **PASS, no BLOCKING, major or minor findings** in the same frozen
authority-conformance scope. It independently audited the governing exact
call-view, directional, nested-source, source-contract, Option A/2, inlet,
finite-context, pure-FMP and CI_ALPHA clauses and corresponding test contracts.

It confirmed no ID/Q/shape/Oracle substitution for source evidence; no
pointwise-to-uniform witness exchange; no replacement of the original kernel
by a selected assembly image; no provider backflow or role rewrite; no latent
return execution. Independent descriptor/admission, recursive absorption,
actual source context/observer coverage and complete interface formation
remain explicit. The alpha tests state only structural outcomes, with
research exhaustion distinguished from production rejection.

### Scope accepted by both reviews

Restricted mathematical results and supplied-record shadow correctness are
accepted. Original semantic premise derivability, actual initial-world
realization, source-wide observation coverage, Generalize eligibility,
all-view Direct success, production containment and rollout are not certified.
There is no accepted finding requiring repair. Primary verification below
is separate executable evidence, not an additional semantic reviewer.

## Frozen submitted fingerprints

Paths are repository relative. Status/link curation after review may change
the progress headers only; the submitted bodies are identified here.

| Artifact | SHA-256 |
| --- | --- |
| `notes/progress/2026-10-07-successor-original-kernel-construction-round2.md` | `9de5d108cd8684d6d67dc2ded6b6c0b289c869cc3e1d7cb4d8783addc0fce31d` |
| `notes/progress/2026-10-07-successor-recursive-coinduction-round2.md` | `dc57c2922a5d9b63e92b2c249ecf422e3c19ec2c6f8ac4468e882e1380c26eab` |
| `notes/progress/2026-10-07-successor-effective-projection-round2.md` | `f235d6d961111567008abc6530aa3717cb34ead2a1a91eb9c94fcdd92357cd38` |
| `notes/progress/2026-10-07-shadow-interface-alpha-round2.md` | `5249174cfb698e2d418a9a3357ae736c920dc60545bfda3550e6233622c8cf6f` |
| `crates/yu-core/src/lib.rs` | `5e0c954daea237da6d2ec73f5d37c55c08a3572fa5401bac853ea6c4f70ff79a` |
| `crates/yu-core/src/shadow_interface_alpha.rs` | `8e7a0333323bf7401120888768812f2b2fae5d98a71f82323ac8344cbac4c23c` |
| `crates/yu-core/tests/shadow_interface_alpha.rs` | `f79fd5693d4b3e7bf5600564bab3277d1dfb6d827a212ceb7d5e5c8ce0867587` |
| `tools/research_successor_original_kernel_round2.py` | `c79424528080abc0ac1580d64ea62222964dde6edee44b81bd28adcd459cb0f3` |
| `tools/research_successor_recursive_coinduction_round2.py` | `4e63d97a9ac8646659f3267e2f1cc031b07ecb05cd52a5c8e269c3c0a0b245c7` |
| `tools/research_successor_effective_projection_round2.py` | `21a0f5f911cdb4808c34c17257ccb1d21e6923a313359169cda53a37b4e95b69` |

## Executed checks at the first checkpoint

Each research producer ran its one assigned Python process under a 60-second
and 1-GiB envelope; every process exited 0. The original-kernel probe checked
64 whole-evidence unions, 64 whole-tuple conjunctions, eight bijections, two
directional cases, one nested capture record and twelve shortcut falsifiers.
The recursive probe checked all 256 two-element operators, their 36 monotone
members and 68 fixed-point pairs, four guard masks and sixteen witness
matrices. The projection probe checked 29,280 direct/orbit comparisons across
1,830 matrices, eight quantifier alternations and two public patterns. Their
notes record exact scope; these executions validate candidate finite models.

Primary toolchain: Rust/Cargo 1.90.0, installed in task scratch from official
manifest-hash-verified components. Extraction initially produced a truncated
LLVM file; reading the verified archive with Python and copying that member
at its full declared length repaired the toolchain before compilation. This
was a local setup failure, not a source/build/test failure.

The primary formatted only the new Rust files, then ran sequentially with
one build owner and `CARGO_BUILD_JOBS=2`:

```sh
timeout 120s cargo test -p yu-core --features shadow --test shadow_interface_alpha
timeout 60s cargo check -p yu-core --no-default-features --offline
```

Results: **6/6 focused tests passed**, no ignored or failed tests; compile/test
command completed in 29.47 seconds including dependency downloads/builds.
The default-feature-off core check passed in 0.03 seconds. No full workspace
suite, production inference switch or live Frozen Oracle run was performed.
The new module has no production inference caller. Further scoped orbit
implementation and final ledger/publication checks are recorded below when
complete; this checkpoint does not claim those later results.
