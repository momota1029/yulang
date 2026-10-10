# Root computation effect annotations (2026-10-10)

## Result

The private live candidate now checks an explicit root covariant effect row
against the actual initializer computation effect for whole-definition and
whole-local annotations. This closes the private candidate's former preflight
gap under the existing covariant `[E]` policy; it does not introduce a new
language rule.

The check uses the annotation's negative allowance with the same effect-variable
and view maps as value checking/exposure. The actual computation effect remains
on its existing one-shot evaluation edge. The allowance does not contribute an
effect, and local schemes still publish only their value interface. An omitted
root row preserves prior behavior. Closed listed rows accept matching concrete
effects; closed empty or unlisted rows reject them with annotation-position
provenance.

For a root row with no concrete members and exactly one symbolic tail, the
computation check now uses the scoped effect variable directly. Wrapping that
case in an empty `Allowance` failed to retain an incoming dependency reachable
from the exposed Function port before a future lower arrived. An actual local
future-lower fixture reproduced the lost effect; the direct row relation fixes
it through ordinary capture/extrusion/freshening. Closed `[]` and concrete
plus-tail rows retain their allowance behavior, so an explicitly listed
concrete member stays local instead of entering the shared tail.

## Review and verification

Independent compiler review found no blocking, major or minor finding. It
checked both action owners, composed annotation context, allowance direction,
one-shot flow, absence of manufactured support, counters, provenance and
transactional rollback/retry. The symbolic-tail repair also received an
independent no-finding review of its direct-row condition, concrete-plus-tail
boundary, ownership and rollback. A third focused review confirmed that
Function-valued initializers keep their root evaluation row separate from the
returned Function effect port. Full Call, public/default inference and full
effect hygiene remain uncertified.

Focused checks after the repair:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation -- --test-threads=1` — 15 passed, including definition correlation, a later actual-argument lower through a local shared tail, and Function-valued initializer/root-port separation.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::root_computation_annotation -- --test-threads=1` — 2 passed, including storage/scratch rollback and retry.
- Scoped `git diff --check` passed.

No broad suite or performance measurement ran. Rows with both concrete members
and a symbolic tail retain the existing per-member allowance consumer; general
contextual residual identity and contravariant concrete subtraction remain
open. General function/effect shapes, complete Call, full hygiene,
soundness/principality and public/default F5
cutover remain open. The pending contextual residual-owner question continues
to block only dependent work.
