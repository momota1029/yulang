# Complete static diff outputs

Read each numbered series in lexical order. Each command is the diff-only
phase of `tools/verify-lean.sh`, and exited 0.

- `precycle-*`: clean local tree `dbd8a6d97`, against the pre-C304 merge `7aac280c7`.
- `integration-*`: same clean local tree, against current integration `e2ad1d61f`.
- `published-*`: exact pinned GitHub tree `d158a6ac1024211bfa6e488c6073937ef0dcd6f2`, against the published C303 handoff `79755b7a1f3c197987540fadf259566d84d94d75`.

These do not report a full Lake build or CI pass.
