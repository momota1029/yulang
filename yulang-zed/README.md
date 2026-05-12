# Yulang for Zed

Yulang language support for Zed.

This extension provides syntax highlighting through the `tree-sitter-yulang`
grammar and starts `yulang-ls` when it is available locally.

## Language Server

Install the language server separately:

```sh
cargo install yulang-ls
```

The extension searches for `yulang-ls` in the current worktree environment and
then in `~/.cargo/bin`. It does not bundle a language server binary yet.
