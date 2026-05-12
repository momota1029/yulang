use zed_extension_api::{self as zed, LanguageServerId, Result, Worktree};

const LANGUAGE_SERVER_BINARY: &str = "yulang-ls";

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
        let binary = worktree
            .which(LANGUAGE_SERVER_BINARY)
            .or_else(default_cargo_language_server)
            .unwrap_or_else(|| LANGUAGE_SERVER_BINARY.into());

        let env = if worktree.read_text_file("lib/std/prelude.yu").is_ok() {
            vec![(
                "YULANG_STD".into(),
                format!("{}/lib/std", worktree.root_path()),
            )]
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

fn default_cargo_language_server() -> Option<String> {
    let home = std::env::var("HOME").ok()?;
    let path = format!("{home}/.cargo/bin/{LANGUAGE_SERVER_BINARY}");
    std::path::Path::new(&path).is_file().then_some(path)
}

zed::register_extension!(YulangExtension);
