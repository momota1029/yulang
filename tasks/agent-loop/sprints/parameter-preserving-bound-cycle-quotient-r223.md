# Sprint R223 — parameter-preserving bound-cycle quotient

Status: **ADMISSION CANDIDATE pending exact-path and current-state update by
Luna**. User objective: prove Yulang's type-inference guarantees first; original
quantifiers, source domain, semantics, and all four parent roots stay fixed.

## Parent and measurable result

Original parents remain `InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` at
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. Parent delta starts
at 0; roots are 0/4 and packages 0/5.

R222's reviewed direct graph encoding is blocked on unguarded variable-bound
cycles. R223 targets a parameter-preserving normalization of finite
variable-to-variable bound SCCs. Its result is a checked Lean construction and
theorem that preserves **all-term substitution behavior**, free class
parameters, actual level/generalization information, and captured anchors.
This is an abstract constraint transformation, not a graph compiler, source
soundness theorem, principal scheme theorem, or semantic change.

## Fixed inputs and equations

- R222 contract SHA-256:
  `d493b155e00c67e472aa88aaed62068bb412dcd071b4e87acb51743b2454e73d`
- R222 equation artifact SHA-256:
  `8435d2610df65be3e547eaedeff8796228dec78628143b1ffe95d982b58e143a`
- R222 obstruction review SHA-256:
  `50365f2c23498acaad58b3409b416bece545d9dd2a3990090f4fed66a397c1d4`
- R212 core SHA-256:
  `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`
- Structural constraints SHA-256:
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- Reuse `Term.var`, `Term.rename`, `Term.subst`, `Sub`, `Store.Satisfied`,
  existing `Generalization.freshen` and the actual R212 CoreState row/birth/
  representative definitions. Recheck all pins before implementation.

Build the directed graph only from actual top-level bounds `.var i` after
kind-preserving representative resolution. Its SCC quotient `q` is
idempotent. Normalize every retained bound by `Term.rename q`; remove only
constraints whose mapped lower and upper terms are syntactically the same
variable. Preserve every non-variable structural bound and all four Function
ports, both effect ports, labels, optional bits, order and payloads. Do not
interpret variables as rigid atoms, and do not choose Top or Bottom for a free
class.

## Required theorem contract

Freeze definitions and theorem types before build. The constructive theorem must
establish, without a store/solution admitted as a definition of acceptance:

1. **Exact quotient**: the self-bound fixture and a two-row cycle quotient to
   a single free `Term.var` class; upper-only bounds and all external bounds
   survive. Every class retains every physical member row's bounds; duplicate
   representatives cannot silently drop a bound.
2. **Both solution directions**: every solution of the normalized store pulls
   back to the original store; for every original solution construct a
   normalized solution. Establish these using reflexivity, transitivity and
   substitution in the existing `Sub`, not by picking a distinguished type.
3. **Universal term factorization**: for every original term `t` (including
   later client terms and all structural constructors), its substitution under
   the original solution is mutually `Sub` with substitution of `rename q t`
   under the constructed normalized solution.
4. **Instantiation and generalization**: quotienting commutes with later
   substitution; derive class levels from all actual members, preserve any
   class containing a captured/below-boundary anchor, and prove factorization
   for separately freshened uses under one shared anchor valuation. A
   mixed-level SCC is mandatory; copies must not sever its captured member.
5. **Actual application**: apply the transformation to the exact R212
   self-upper output, a two-row cycle, an upper-only bound, recursive Function
   with all four ports, and a mixed Value/Effect case. State whether this
   removes the guardedness blocker or only supplies a prerequisite. It does
   not close an original root unless a checked theorem is applied to that root.

Mutual `Sub` does not establish `sameScoped` or the original `instanceOf` by
itself. Those bridges remain named open premises unless separately proved from
the existing definitions. Fig. 12 recursive-syntax equivalence also remains
open unless this packet proves it.

## Lanes and exact outputs

1. Fresh review of R222's already frozen obstruction is complete and recorded.
2. `lean_prover` owns only:
   - `notes/theory/lean/YulangClosure/AbstractBoundCycleNormalizationR223.lean`
   - `tasks/agent-loop/inbox/abstract-bound-cycle-normalization-r223-proof.md`
3. After the Lean handoff freezes, independent `researcher` owns only:
   - `tasks/agent-loop/inbox/abstract-bound-cycle-normalization-r223-falsifier.md`
4. After all inputs freeze, fresh `compiler_referee` owns the bounded review:
   - `tasks/agent-loop/inbox/abstract-bound-cycle-normalization-r223-review.md`
5. Luna owns contract/current state, source pins, existing-cache verification,
   checker/axiom audit, outcome, adjudication, explicit staging and Git.

The Lean writer may prove related lemmas within this fixed theorem target, but
cannot change the quotient, class-level rule, semantics, source domain or
parent statement. If universal factorization fails, freeze the smallest
counterexample; do not weaken it to mere satisfiability.

## Cache and execution limits

The user explicitly authorized Lean cache generation. Use only the existing
pinned project `notes/theory/lean` and its existing `.lake/build`; do not add a
worktree, environment, project copy, target directory, or scratch cache. Lean is
pinned at 4.35.0. Only Luna writes the cache, after the module freezes. Build
only `+YulangClosure.AbstractBoundCycleNormalizationR223:olean` and the focused
bundled declaration checker. One CPU, process cap 1 GiB, maximum aggregate
cache growth 64 MiB, no cleanup, default build, Rust, Cargo, or tests. Stop if
any whitelisted output exists at intake or if Lake requires any additional
output path.

The exact eight R223 module outputs under `.lake/build/lib/lean` and
`.lake/build/ir` were all absent at contract preparation. The complete path list
must be copied unchanged into the Luna intake receipt before cache execution.

Aggregate assignment budget is 3600 seconds. No Astra or nested CLI. One heavy
Lean process and one cache writer at a time.

## Success, blocker, and stop boundary

Success requires checked constructive theorems for both solution directions,
all-term factorization, the shared-anchor/generalization discriminator,
application to the frozen R212 states, complete axiom audit, independent
falsifier, fresh review PASS, and an evidenced reduction of the R212 readout
blocker. Report original roots/packages as 0/4 and 0/5 unless an unchanged
parent is actually discharged.

Stop at the smallest missing quotient, substitution, class-level, anchor, or
source correspondence premise. Do not declare that solution-set equivalence
alone proves principality. Next dispatcher consultation: a failed factorization
or mixed-level counterexample, authority/dependency/resource change, or sprint
closeout.
