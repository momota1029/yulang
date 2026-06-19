# Yulang for Zed

Yulang language support for Zed.

This extension provides syntax highlighting through the `tree-sitter-yulang`
grammar and starts the Yulang language server from the active Zed worktree
environment.

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

The extension first searches for `yulang-lsp`, then falls back to `yulang`
and invokes it as `yulang server`. It searches the active worktree environment,
`~/.yulang/bin`, and `~/.cargo/bin`. It does not bundle a language server
binary yet.

You can override the command from Zed settings:

```json
{
  "lsp": {
    "yulang-lsp": {
      "binary": {
        "path": "/home/me/.yulang/bin/yulang",
        "arguments": ["server"]
      }
    }
  }
}
```

For WSL, open the project through Zed Remote instead of launching `wsl.exe`
from the extension. The language server will then run inside the WSL worktree
and use the WSL-side `PATH`. Put binary path overrides in the remote server
settings or the project `.zed/settings.json`.

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
