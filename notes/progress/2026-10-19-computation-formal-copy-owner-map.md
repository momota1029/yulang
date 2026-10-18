# R51 Luna source-owner map: Computation formal copy and FreshUse

Date: 2026-10-19. Status: read-only source map; no implementation slice authorized or established.
Sprint: `computation-formal-copy-bridge-20261019-r51`, revision 2, baseline
`a191b5ccdd2a41bf6c74687d8552e9fb0a6eb9fa`.
Parent: unchanged full inference/evaluator theorem and Simple-sub A/B, OPEN
0→0. This map supplies no semantic choice or production premise.

## Existing source path

1. `candidate_source.rs:866–883,904–932` creates a formal registration from
   the original Lambda/formal, retains its source owner and parameter recipe,
   classifies an annotated effect formal as Computation, and registers each
   resolved parameter Name against that same registration. Source Name
   endpoints are the original Parameter endpoint, not a reconstructed alias.
2. For Computation Name occurrences, `candidate_source.rs:1224–1234`
   schedules `FormalNameEffect`; `execute_candidate_action` routes it through
   `candidate_formal_effect_equal`. This establishes the native formal-entry
   equality owner for those Names. Other Name routes distinguish ModuleDef,
   Parameter/CatchBinder and published Local (`:1235–1258`). A Local initializer
   Name gets `Action::Local`; an active initializer Name gets `Action::Link`.
3. Apply collection retains its original callee and argument expressions,
   endpoints, effects, result, level and occurrence in `ApplySourceInput`
   (`candidate_source.rs:1320–1359`). Its `formal_name` is taken from the
   *callee* expression's `formal_names` slot. It therefore identifies a formal
   used as callee where the later consumer validates it; it is not an
   argument-Name/use transport certificate. `candidate_call.rs:207–239`
   exposes the existing borrowed Computation source plan: original owner,
   Lambda, formal, annotation, outer row, concrete/symbolic row members,
   retained Parameter root and entry row. Its explicit contract says this
   observation does not authenticate Lambda AE/RE, copied ports, Name/Delay/
   argument transport or actual receivers.
4. Published local uses follow `Action::Local` and the scheme route. The local
   route captures the current root at its boundary, constructs one fresh-use
   mapping and restores captured bounds before linking/publishing the use
   (`candidate_scheme.rs:2032–2044,2086–2105,2165–2200`). `begin_candidate_fresh_bound`
   (`:1860–1905`) builds restoration from the captured bound and actual fresh
   maps. Repeated route stages are stateful; a static source Name or matching
   term alone is not evidence of a particular use map.
5. Signed copying is owned by `candidate_extrusion.rs::candidate_extrude`
   (`candidate_extrusion.rs:21–379`). It keeps operation-local signed row and
   structural maps, copies selected bounds and records source links. The
   parent/copy records and output groups are retained by
   `candidate_intrusion.rs::retain_extrusion_parent` and
   `finish_candidate_extrusion` (`:305–393`); qualified intrusion/settlement
   and canonicalization are further consumers there. Capture reads the live
   graph and its current bounds; FreshUse then maps captured representatives
   canonically, restoring each retained bound before root return/publication
   (`candidate_scheme.rs:1216–1380,1475–1545,1555–1860`).

## Owner conclusion

The current observational source-plan path is already reviewed and bounded; it
is not an implementation gap to fill with another report field. It explicitly
stops before original formal -> actual argument Name -> receiving Function
ports and copied/merged provider lineage. `ApplySourceInput.formal_name` cannot
fill that gap because it indexes a callee formal. Existing copy, intrusion,
capture and FreshUse owners contain candidate evidence, but the current map
alone does not prove that the same original formal/Name/provider/use association
survives arbitrary shared or merged representatives and later recapture.

NO_SAFE_CODE_SLICE at this stage. No code edit, test, runtime output, new
registry, observational field or expected-output change is justified by this
map. The productive implementation lane stays read-only pending the proof
lane's source-qualified result and independent review. If the proof identifies
an exact absent constructor/consumer input, Luna can issue a new exact code
contract; existing facts and this map do not authorize that change.

## Review seam and falsifiers

The proof review must try to separate or mismatch (a) original formal and
parameter Name, (b) the specific argument Name/use, (c) positive/negative
Function ports, (d) each signed parent/copy operation and bound provenance,
(e) merge/canonical representative transitions, and (f) later capture/FreshUse
maps. A proof fails if it substitutes a callee formal for argument provenance,
renames rows globally without a retained transport edge, loses a bound's source
cause, splices unrelated uses/providers, or invokes solver success as evidence.

This is a source-owner map only. It does not establish arbitrary reachability,
complete replay, dynamic receiver/receipt/Force behavior, whole-language
soundness, principality, evaluator behavior or closure of the original bridge.

Dependency pins are maintained in `tasks/agent-loop/current.json` under R51;
all exact bytes must remain unchanged for proof review.
