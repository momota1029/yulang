# Yulang for Zed

Yulang language support for Zed.

This extension provides syntax highlighting through the `tree-sitter-yulang`
grammar and starts `yulang server` when the `yulang` binary is available
locally.

## Language Server

The language server ships inside the main `yulang` binary. Install it with:

```sh
cargo install yulang
```

The extension searches for the `yulang` binary in the current worktree
environment and then in `~/.cargo/bin`, and invokes it as `yulang server`. It
does not bundle a language server binary yet.
