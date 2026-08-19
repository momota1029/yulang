use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::path::Path;
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, bail};
use serde_json::Value;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("xtask: {error:#}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<()> {
    let mut arguments = env::args().skip(1);
    let Some(command) = arguments.next() else {
        bail!("expected a subcommand; available subcommands: check-graph");
    };

    if arguments.next().is_some() {
        bail!("{command} does not accept arguments");
    }

    match command.as_str() {
        "check-graph" => check_workspace_graph(),
        _ => bail!("unknown subcommand `{command}`; available subcommands: check-graph"),
    }
}

fn check_workspace_graph() -> Result<()> {
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("tools/xtask has a workspace-root grandparent");
    let output = Command::new("cargo")
        .args(["metadata", "--format-version", "1", "--no-deps"])
        .current_dir(workspace_root)
        .output()
        .context("failed to run cargo metadata")?;

    if !output.status.success() {
        bail!(
            "cargo metadata failed:\n{}",
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }

    let graph = WorkspaceGraph::from_metadata(&output.stdout)?;
    let violations = graph.violations();
    if violations.is_empty() {
        println!("dependency graph check passed");
        return Ok(());
    }

    eprintln!("dependency graph check failed:");
    for violation in violations {
        eprintln!("  - {violation}");
    }
    bail!("{} dependency graph violation(s)", graph.violations().len())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DependencyKind {
    Normal,
    Build,
    Development,
}

impl DependencyKind {
    fn from_metadata(value: Option<&str>) -> Self {
        match value {
            Some("build") => Self::Build,
            Some("dev") => Self::Development,
            _ => Self::Normal,
        }
    }

    fn is_production(self) -> bool {
        self != Self::Development
    }
}

impl std::fmt::Display for DependencyKind {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::Normal => "dependency",
            Self::Build => "build-dependency",
            Self::Development => "dev-dependency",
        };
        formatter.write_str(name)
    }
}

#[derive(Debug, Clone)]
struct Dependency {
    package: String,
    kind: DependencyKind,
}

#[derive(Debug, Clone)]
struct WorkspaceGraph {
    dependencies: BTreeMap<String, Vec<Dependency>>,
}

impl WorkspaceGraph {
    fn from_metadata(metadata: &[u8]) -> Result<Self> {
        let metadata: Value =
            serde_json::from_slice(metadata).context("invalid cargo metadata JSON")?;
        let workspace_members = metadata["workspace_members"]
            .as_array()
            .context("cargo metadata did not include workspace_members")?;
        let member_ids: BTreeSet<&str> =
            workspace_members.iter().filter_map(Value::as_str).collect();
        let packages = metadata["packages"]
            .as_array()
            .context("cargo metadata did not include packages")?;

        let package_names: BTreeMap<&str, &str> = packages
            .iter()
            .filter_map(|package| Some((package["id"].as_str()?, package["name"].as_str()?)))
            .collect();

        let mut dependencies = BTreeMap::new();
        for package in packages {
            let package_id = package["id"].as_str().context("package without an id")?;
            if !member_ids.contains(package_id) {
                continue;
            }

            let package_name = package["name"].as_str().context("package without a name")?;
            let package_dependencies = package["dependencies"]
                .as_array()
                .context("package without dependencies")?;
            let dependencies_for_package = package_dependencies
                .iter()
                .filter_map(|dependency| {
                    let dependency_name = dependency["name"].as_str()?;
                    let package = package_names
                        .values()
                        .find(|package_name| **package_name == dependency_name)?;
                    Some(Dependency {
                        package: (*package).to_owned(),
                        kind: DependencyKind::from_metadata(dependency["kind"].as_str()),
                    })
                })
                .collect();
            dependencies.insert(package_name.to_owned(), dependencies_for_package);
        }

        Ok(Self { dependencies })
    }

    fn violations(&self) -> Vec<String> {
        let mut violations = Vec::new();

        for (source, dependencies) in &self.dependencies {
            for dependency in dependencies {
                if is_core_crate(source) && is_application_crate(&dependency.package) {
                    violations.push(format!(
                        "core crate `{source}` has a {} on application crate `{}`",
                        dependency.kind, dependency.package
                    ));
                }

                if dependency.package == "yu-test-support" && dependency.kind.is_production() {
                    violations.push(format!(
                        "`{source}` has a production {} on `yu-test-support`",
                        dependency.kind
                    ));
                }

                if source == "yulang-wasm" && dependency.package == "yulang" {
                    violations.push(format!(
                        "`yulang-wasm` must not have a {} on CLI crate `yulang`",
                        dependency.kind
                    ));
                }

                if let (Some(source_rank), Some(dependency_rank)) =
                    (crate_rank(source), crate_rank(&dependency.package))
                {
                    if dependency_rank >= source_rank {
                        violations.push(format!(
                            "{} `{source}` points downstream to `{}`",
                            dependency.kind, dependency.package
                        ));
                    }
                }
            }
        }

        if let Some(cycle) = self.find_cycle() {
            violations.push(format!(
                "workspace dependency cycle: {}",
                cycle.join(" -> ")
            ));
        }

        violations
    }

    fn find_cycle(&self) -> Option<Vec<String>> {
        let mut completed = BTreeSet::new();
        let mut active = Vec::new();
        for package in self.dependencies.keys() {
            if let Some(cycle) = self.find_cycle_from(package, &mut completed, &mut active) {
                return Some(cycle);
            }
        }
        None
    }

    fn find_cycle_from(
        &self,
        package: &str,
        completed: &mut BTreeSet<String>,
        active: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        if let Some(position) = active
            .iter()
            .position(|active_package| active_package == package)
        {
            let mut cycle = active[position..].to_vec();
            cycle.push(package.to_owned());
            return Some(cycle);
        }
        if !completed.insert(package.to_owned()) {
            return None;
        }

        active.push(package.to_owned());
        for dependency in self.dependencies.get(package).into_iter().flatten() {
            if self.dependencies.contains_key(&dependency.package)
                && let Some(cycle) = self.find_cycle_from(&dependency.package, completed, active)
            {
                return Some(cycle);
            }
        }
        active.pop();
        None
    }
}

fn crate_rank(crate_name: &str) -> Option<u8> {
    match crate_name {
        "yu-syntax" => Some(0),
        "yu-hir" => Some(1),
        "yu-types" => Some(2),
        "yu-solver" => Some(3),
        "yu-core" => Some(4),
        "yu-backend-vm" | "yu-backend-native" => Some(5),
        "yu-compiler" => Some(6),
        "yulang" | "yulang-lsp" | "yulang-wasm" => Some(7),
        _ => None,
    }
}

fn is_core_crate(crate_name: &str) -> bool {
    crate_rank(crate_name).is_some_and(|rank| rank < 7)
}

fn is_application_crate(crate_name: &str) -> bool {
    crate_rank(crate_name) == Some(7)
}

#[cfg(test)]
mod tests {
    use super::{Dependency, DependencyKind, WorkspaceGraph};
    use std::collections::BTreeMap;

    fn graph(entries: &[(&str, &[(&str, DependencyKind)])]) -> WorkspaceGraph {
        WorkspaceGraph {
            dependencies: entries
                .iter()
                .map(|(package, dependencies)| {
                    (
                        (*package).to_owned(),
                        dependencies
                            .iter()
                            .map(|(package, kind)| Dependency {
                                package: (*package).to_owned(),
                                kind: *kind,
                            })
                            .collect(),
                    )
                })
                .collect::<BTreeMap<_, _>>(),
        }
    }

    #[test]
    fn accepts_the_planned_core_direction() {
        let graph = graph(&[
            ("yu-syntax", &[]),
            ("yu-hir", &[("yu-syntax", DependencyKind::Normal)]),
            ("yu-types", &[("yu-hir", DependencyKind::Normal)]),
            (
                "yu-solver",
                &[
                    ("yu-hir", DependencyKind::Normal),
                    ("yu-types", DependencyKind::Normal),
                ],
            ),
            ("yu-core", &[("yu-solver", DependencyKind::Normal)]),
            ("yu-backend-vm", &[("yu-core", DependencyKind::Normal)]),
            ("yu-backend-native", &[("yu-core", DependencyKind::Normal)]),
        ]);

        assert!(graph.violations().is_empty());
    }

    #[test]
    fn rejects_a_core_dependency_on_a_backend() {
        let graph = graph(&[
            ("yu-core", &[("yu-backend-vm", DependencyKind::Normal)]),
            ("yu-backend-vm", &[]),
        ]);

        assert!(
            graph
                .violations()
                .iter()
                .any(|violation| violation.contains("`yu-core` points downstream"))
        );
    }

    #[test]
    fn rejects_backend_peer_dependencies_and_cycles() {
        let graph = graph(&[
            (
                "yu-backend-vm",
                &[("yu-backend-native", DependencyKind::Normal)],
            ),
            (
                "yu-backend-native",
                &[("yu-backend-vm", DependencyKind::Normal)],
            ),
        ]);

        let violations = graph.violations();
        assert!(
            violations
                .iter()
                .any(|violation| violation.contains("points downstream"))
        );
        assert!(
            violations
                .iter()
                .any(|violation| violation.contains("workspace dependency cycle"))
        );
    }
}
