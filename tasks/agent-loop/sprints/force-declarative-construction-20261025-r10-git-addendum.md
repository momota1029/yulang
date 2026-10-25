# r10 Git integration addendum

This addendum changes only primary Git integration permission; it does not
change the frozen r10 source/proof leases, inputs, meanings, or worker
prohibitions.

## User direction

On 2026-10-25 the user explicitly directed Luna to use commits and pushes as
appropriate. This supersedes the r10 contract's temporary “no Git operations”
sentence for the primary only. Subagents retain no Git authority.

## Integration rule

Luna may checkpoint frozen r10 artifacts when they meet the repository's
research-only `commit-ready` criteria. Accepted theorem/implementation
milestones receive compact state and outcome synchronization before
integration. Every commit stages only named paths, inspects the full staged
diff and complete outbound range, excludes pending question bundles and
unrelated workspace changes, and pushes only an intended coherent range.
Never force-push or overwrite a moved remote HEAD. A blocked push leaves a
coherent local checkpoint and records the concrete blocker.

The r10 base contract remains pinned at SHA-256
`ddcfe7b8ff5065ab76dae1c753ad43a33b0f7ef38682ff4829dd218c2094e521`.
