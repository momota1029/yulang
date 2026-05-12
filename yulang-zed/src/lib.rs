use zed_extension_api::{self as zed, LanguageServerId, Result, Worktree};

struct YulangExtension;

impl zed::Extension for YulangExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<zed::Command> {
        // Prefer PATH lookup (works after `cargo install yulang-ls`).
        let binary = worktree
            .which("yulang-ls")
            .unwrap_or_else(|| "/home/momota1029/.cargo/bin/yulang-ls".into());

        let env = if worktree.read_text_file("lib/std/prelude.yu").is_ok() {
            vec![("YULANG_STD".into(), format!("{}/lib/std", worktree.root_path()))]
        } else {
            Vec::new()
        };

        Ok(zed::Command {
            command: binary,
            args: vec![],
            env,
        })
    }
}

zed::register_extension!(YulangExtension);
