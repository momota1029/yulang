# Handler-protection release: finite local characterization

Date: 2026-10-05
Status: research-only characterization; no semantic, grammar, solver, or implementation authority
Governing decision: `'e?` removes only handler protection from a qualifying `'e`-derived contribution emitted from the marked slot. Provenance, event identity/lineage, row membership, and typed paths are preserved frame invariants, not the marker's meaning.
Probe: [`research_handler_protection_release.py`](../../tools/research_handler_protection_release.py)

The probe keeps five supplied coordinates separate: dynamic event identity,
source component, effect family, lineage/typed path, and the existing
protection witness `(event, boundary, slot)`. Its finite eligibility query
assumes the contribution is emitted from the marked slot and attributed to the
marked source component; the association between that premise and the
protection witness is only a toy input representation. It does not derive
emission, attribution, or protection from source, `Rel_C`, `K,D`,
occurrence/incidence, or typed-path rules. It does not rewrite the contribution
or evidence tuple. Identity, lineage, and path are frame coordinates here,
not the meaning of `?`; the probe models only a post-attribution,
post-emission protection-release check, not release lifetime or nested
protection composition.

The bounded check covers four combinations of selected versus unrelated source
component and active versus inactive receiver handler. A same-family local
event remains protected, and the event frame preserves its family, lineage,
typed path, and identity. A second event can share source component/family/path
while retaining a distinct resumed dynamic identity. The family-wide release
mutant makes the local event visible; the sticky-protection mutant keeps the
qualifying input event invisible. Both are rejected.

This is deliberately smaller than the requested lifetime investigation. It
uses one protection witness per event and does not model simultaneous nested or
shallow/deep boundaries, actual continuation transitions, higher-order latent
invocation, source attribution, or ordinary production handler search. In
particular, it does not show whether existing typed-boundary `χ`, `Path`,
`Inc_C`, and `Visible` can express a release while retaining their selected
transport behavior. That is the next evidence-based question: compare the
marked output-slot release with the existing rule that matching result-path
profiles remain live while their receiver activation remains active, keeping
provenance transport and handler protection as separate observations.

Verification:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_handler_protection_release.py
  pass: 4 local combinations; frame and same-family checks; family-wide and sticky-protection mutants rejected
python3 -m py_compile tools/research_handler_protection_release.py
  pass
git diff --check
  pass
```
