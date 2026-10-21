# R266 — direct-root use CSTs retain source-bound routes

The exact 40-file standard-library bundle was rechecked against every
embedded Git blob ID. The temporary probe rewrote only the eleven line-leading
Y2 `--` comment markers to equal-length `//` markers, parsed all projected
files with the current Y3 parser, and verified lossless round-trip.

Across 27 files it found 112 direct-root `UseDeclaration` nodes. Every node
had at least one descendant `UsePath`, no descendant `Missing` or `Error`,
and a source range whose CST text exactly matched the projected input slice.
The probe emitted each node's route nodes and original declaration text. This
shows that the current parser can locate the direct use syntax present in the
pinned corpus after the narrow comment projection. It does not show Y2
resolution semantics or that names are module paths: grouped uses contain
module and selected-item paths, and local routes such as `clock::*` also occur.

This supplies a possible source-bound route extractor for the next step and
explains R265's 45-versus-112 scanner gap: root uses after other declarations
are absent from `HeaderInfo::imports()`. It still does not establish the
source-local operator environment, module/re-export graph, DefId identity,
runtime publication or any R149 output. The temporary probe was removed; no
retained code/tests changed. See R266 contract.
