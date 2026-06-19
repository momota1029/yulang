use zed_extension_api::{
    self as zed, current_platform,
    settings::{CommandSettings, LspSettings},
    LanguageServerId, Os, Result, Worktree,
};

const LANGUAGE_SERVER_ID: &str = "yulang-lsp";
const LANGUAGE_SERVER_BINARY: &str = "yulang-lsp";
const YULANG_BINARY: &str = "yulang";
const LANGUAGE_SERVER_SUBCOMMAND: &str = "server";

struct YulangExtension;

impl zed::Extension for YulangExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<zed::Command> {
        if language_server_id.as_ref() != LANGUAGE_SERVER_ID {
            return Err(format!("unknown language server: {language_server_id}"));
        }

        let settings = LspSettings::for_worktree(LANGUAGE_SERVER_ID, worktree).unwrap_or_default();
        let binary_settings = settings.binary.as_ref();
        let (os, _) = current_platform();
        let command = if let Some(path) = binary_settings.and_then(|binary| binary.path.as_deref())
        {
            resolve_configured_command(worktree, path, os)?
        } else {
            default_language_server(worktree, os).ok_or_else(missing_language_server_message)?
        };

        let args = binary_settings
            .and_then(|binary| binary.arguments.clone())
            .unwrap_or_else(|| default_arguments_for_command(&command));
        let env = command_environment(worktree, binary_settings);

        Ok(zed::Command { command, args, env })
    }
}

fn resolve_configured_command(worktree: &Worktree, path: &str, os: Os) -> Result<String> {
    let command = worktree
        .which(path)
        .filter(|resolved| command_path_is_usable(resolved, os))
        .unwrap_or_else(|| path.into());
    if command_path_is_usable(&command, os) {
        Ok(command)
    } else {
        Err(format!(
            "`{path}` is not a spawnable path on Windows. Open the project through Zed Remote for WSL paths, or point lsp.{LANGUAGE_SERVER_ID}.binary.path at a Windows executable."
        ))
    }
}

fn default_language_server(worktree: &Worktree, os: Os) -> Option<String> {
    if os == Os::Windows {
        find_binary(worktree, YULANG_BINARY, os)
            .or_else(|| find_binary(worktree, LANGUAGE_SERVER_BINARY, os))
    } else {
        find_binary(worktree, LANGUAGE_SERVER_BINARY, os)
            .or_else(|| find_binary(worktree, YULANG_BINARY, os))
    }
}

fn find_binary(worktree: &Worktree, binary: &str, os: Os) -> Option<String> {
    worktree
        .which(binary)
        .filter(|path| command_path_is_usable(path, os))
        .or_else(|| default_user_binary(binary, os))
        .or_else(|| default_cargo_binary(binary, os))
}

fn default_arguments_for_command(command: &str) -> Vec<String> {
    if command_basename(command) == LANGUAGE_SERVER_BINARY {
        Vec::new()
    } else {
        vec![LANGUAGE_SERVER_SUBCOMMAND.into()]
    }
}

fn command_basename(command: &str) -> &str {
    let basename = command.rsplit(['/', '\\']).next().unwrap_or(command);
    basename.strip_suffix(".exe").unwrap_or(basename)
}

fn command_environment(
    worktree: &Worktree,
    binary_settings: Option<&CommandSettings>,
) -> Vec<(String, String)> {
    let mut env = default_environment(worktree);
    if let Some(settings_env) = binary_settings.and_then(|binary| binary.env.as_ref()) {
        for (key, value) in settings_env {
            upsert_env(&mut env, key.clone(), value.clone());
        }
    }
    env
}

fn default_environment(worktree: &Worktree) -> Vec<(String, String)> {
    if worktree.read_text_file("lib/std/prelude.yu").is_ok() {
        vec![(
            "YULANG_STD".into(),
            format!("{}/lib/std", worktree.root_path()),
        )]
    } else {
        Vec::new()
    }
}

fn upsert_env(env: &mut Vec<(String, String)>, key: String, value: String) {
    if let Some((_, existing)) = env
        .iter_mut()
        .find(|(existing_key, _)| existing_key == &key)
    {
        *existing = value;
    } else {
        env.push((key, value));
    }
}

fn missing_language_server_message() -> String {
    format!(
        "`{LANGUAGE_SERVER_BINARY}` or `{YULANG_BINARY}` was not found. Install Yulang in the current environment or set lsp.{LANGUAGE_SERVER_ID}.binary.path."
    )
}

fn default_user_binary(binary: &str, os: Os) -> Option<String> {
    let home = home_dir(os)?;
    binary_candidates(&home, ".yulang/bin", binary, os)
        .into_iter()
        .find(|path| std::path::Path::new(path).is_file() && command_path_is_usable(path, os))
}

fn default_cargo_binary(binary: &str, os: Os) -> Option<String> {
    let home = home_dir(os)?;
    binary_candidates(&home, ".cargo/bin", binary, os)
        .into_iter()
        .find(|path| std::path::Path::new(path).is_file() && command_path_is_usable(path, os))
}

fn binary_candidates(home: &str, dir: &str, binary: &str, os: Os) -> Vec<String> {
    let base = format!("{home}/{dir}/{binary}");
    if os == Os::Windows {
        vec![format!("{base}.exe"), base]
    } else {
        vec![base]
    }
}

fn home_dir(os: Os) -> Option<String> {
    if os == Os::Windows {
        std::env::var("USERPROFILE")
            .ok()
            .filter(|path| windows_path_is_usable(path))
            .or_else(|| {
                std::env::var("HOME")
                    .ok()
                    .filter(|path| windows_path_is_usable(path))
            })
    } else {
        std::env::var("HOME").ok()
    }
}

fn command_path_is_usable(path: &str, os: Os) -> bool {
    os != Os::Windows || windows_path_is_usable(path) || !path.contains(['/', '\\'])
}

fn windows_path_is_usable(path: &str) -> bool {
    path.starts_with("\\\\")
        || path.as_bytes().get(1).is_some_and(|byte| *byte == b':')
        || !path.starts_with('/')
}

zed::register_extension!(YulangExtension);
