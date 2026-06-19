use zed_extension_api::{self as zed, LanguageServerId, Result, Worktree};

const LANGUAGE_SERVER_BINARY: &str = "yulang";
const LANGUAGE_SERVER_SUBCOMMAND: &str = "server";

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
            .or_else(default_user_language_server)
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
            args: vec![LANGUAGE_SERVER_SUBCOMMAND.into()],
            env,
        })
    }
}

fn default_user_language_server() -> Option<String> {
    let home = home_dir()?;
    [
        format!("{home}/.yulang/bin/{LANGUAGE_SERVER_BINARY}"),
        format!("{home}/.yulang/bin/{LANGUAGE_SERVER_BINARY}.exe"),
    ]
    .into_iter()
    .find(|path| std::path::Path::new(path).is_file())
}

fn default_cargo_language_server() -> Option<String> {
    let home = home_dir()?;
    let path = format!("{home}/.cargo/bin/{LANGUAGE_SERVER_BINARY}");
    std::path::Path::new(&path).is_file().then_some(path)
}

fn home_dir() -> Option<String> {
    std::env::var("HOME")
        .ok()
        .or_else(|| std::env::var("USERPROFILE").ok())
}

zed::register_extension!(YulangExtension);
