# Cycle245 plan: actual used reads and old-model readback

I47 remains the target. The core244 table is not a full SourceBoundary. Its current CrossRead checker examines unused old entries and is strictly sufficient, not exact. It must not become a new language rejection condition.

First split TyTerm typed-variable reads from row-only reads. Actual owner substitution changes only types and leaves rows unchanged. Prove an exact occurrence characterization for the transformed type, then an exact used-lookup External condition for each retained block. Include unused-old-entry and row-only regressions. Do not silently strengthen this to future checker closure.

Second, prove that External+Coherent old entries produce a readback assignment satisfying their actual two-inequality block. Combine with the existing actual owner-table models_exact to obtain old full Models from new Models and equality of every unowned public assignment coordinate. This is one direction of projected source-model preservation, not equality of old/new public solution sets or existence of fresh models.

Current/historical inspector/cache metadata, fresh-block producers, actual solver scheduling and full EvidenceNode remain open. No language meaning changed. Six recovered large-import drafts remain outside imports. Only the available small Presence/core cache is used; full journal rebuild and whole repository gate stay with supervisor.
