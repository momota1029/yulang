# Yulang for Zed

Yulang language support for Zed.

This extension provides syntax highlighting through the `tree-sitter-yulang`
grammar and starts `yulang server` when the `yulang` binary is available
locally.

## Language Server

The language server ships inside the main `yulang` binary. Install a release
binary first:

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.1
```

On Windows PowerShell:

```powershell
irm https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.1
```

The extension searches for the `yulang` binary in the current worktree
environment, `~/.yulang/bin`, and `~/.cargo/bin`, then invokes it as
`yulang server`. It does not bundle a language server binary yet.

## Semantic Highlighting

Zed keeps tree-sitter highlighting and language-server semantic highlighting
as separate settings. Enable semantic tokens for Yulang in `settings.json`:

```json
{
  "languages": {
    "Yulang": {
      "semantic_tokens": "full"
    }
  }
}
```

Use `"combined"` instead of `"full"` to layer semantic tokens on top of the
tree-sitter highlights.
