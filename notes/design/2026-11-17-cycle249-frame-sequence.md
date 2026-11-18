# Finite fixed-metadata owner-frame sequences

For the actual finite rebase function, a second rewrite through a target domain
contained in the original old domain leaves metadata and consumer syntax
literally unchanged. Extend this to any supplied finite block list: after the
first rebase, stored metadata/consumers equal their first rewritten values; only
the last supplied definition block remains. Old SafeOrder and target inclusion
suffice for this syntax statement. Per-step model correctness separately needs
safe fresh blocks, protected new reads and both public domains. No theorem here
bounds changing RHS bodies, new packet insertion or the number of source steps.
