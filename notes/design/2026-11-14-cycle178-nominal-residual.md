# Cycle 178: same-model nominal residual, exact G boundary

Baseline: integration/m1-final d636750ce44de9271ebf328a5ab27ad4955cb845.
I30 assigns only G.EvidenceNode to dot. The unrestricted field remains OPEN.

## Plan before implementation

Extend cycle 177's scalar/nonpoint fragment toward one finite nominal head with
linear type binders and terminal emission. Inspect both lower and upper nominal
argument lists. Derive projection compatibility from the nominal endpoint
subtyping checks and the existing source model. Keep fresh capture-merge
equations as a separate same-assignment premise, rather than confusing a
candidate's existential branch model with the arbitrary model in EvidenceNode.

Then connect the resulting exact residual to current Candidate/Instance/Evidence
consumers without journal or packet installation assumptions. If feasible,
record a small failure of an overstrong merge inference; that would not by
itself refute the full reachable/stable G field.

No semantic rule changes, full-language completeness claims, or changes to the
other three B4 owner fields. Existing runtime X13/X15 tests cover finite
interval lifting approximations, not arbitrary internal lower/upper states;
no new Yulang2 runtime behavior is asserted.

## Validation

Focused dependency-cache build, separate small trust-zero audit, raw logs and
source hashes. No local full build. Exact source checkpoint and full CI status
will be recorded separately. End this cycle within 55 minutes.
