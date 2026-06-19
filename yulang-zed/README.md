# Yulang for Zed

Yulang language support for Zed.

This extension provides syntax highlighting through the `tree-sitter-yulang`
grammar and starts `yulang server` when the `yulang` binary is available
locally.

## Language Server

The language server ships inside the main `yulang` binary. Install a release
binary first:

```sh
curl -fsSL https://raw.githubusercontent.com/momota1029/yulang/main/scripts/install.sh | sh -s -- --version v0.1.0-alpha.1
```

The extension searches for the `yulang` binary in the current worktree
environment, `~/.yulang/bin`, and `~/.cargo/bin`, then invokes it as
`yulang server`. It does not bundle a language server binary yet.
