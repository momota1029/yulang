# Cycle 12: finite structural source positions

Status: Draft (proof scope, not a new language-semantics decision)

Unary settled Ty already supplies `nodes` and finite graph slots. This module relates the cycle11 executable `atDepth` selector to that finite bound and composes selectors through actual producer capture and template substitution. Regular loops remain opaque, exactly as in the existing selector; this is not arbitrary graph unfolding.

Data: source positions are natural depths bounded by `Ty.nodes`; `SourcePosition t n payload` independently follows zero or successor wrapper edges. Executable: existing `atDepth`. Targets: `atDepth n t = some payload ↔ SourcePosition t n payload`; `∃ payload, SourcePosition t n payload ↔ n < t.nodes`; and for every successful actual production, capture depth h, variable-bearing requirement depth v and suffix k, the child endpoint selector at v+k equals the parent selector at h+k (both bounds separately). No lower=upper assumption.

This is an auxiliary bridge for B4 A: all copied descendants, not just the captured root, inherit parent structural positions. It does NOT generate global source IDs, identify equal-shaped but distinct source nodes, allocate dynamic requests, prove saturation, or prove four-way B4. Remaining bridge groups are source identity/allocation, finite dynamic domain, saturation/termination, final classification/dictionaries and outer-entry conformance (5 groups, not five trivial lemmas). No additional language decision is made.

Yulang2: integrated `notes/audit/x-oracle.md` was read; X1 and X2 are only behavior context, not evidence for this internal position theorem. Fresh audit branch fetch was rejected by auto-review as outside stopped audit scope; no workaround attempted. New source position model is not runtime-tested against Yulang2.
