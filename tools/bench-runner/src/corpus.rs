use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail, ensure};
use serde::{Deserialize, Serialize};

use crate::digest::{Sha256, sha256_file};

#[derive(Debug)]
pub struct Corpus {
    pub root: PathBuf,
    pub manifest: CorpusManifest,
    pub sha256: String,
    pub workloads: Vec<Workload>,
}

impl Corpus {
    pub fn load(path: &Path, only: &[String]) -> Result<Self> {
        let root = path
            .canonicalize()
            .with_context(|| format!("failed to resolve corpus directory {}", path.display()))?;
        ensure!(
            root.is_dir(),
            "corpus path is not a directory: {}",
            root.display()
        );

        let manifest_path = root.join("corpus.toml");
        let manifest_text = fs::read_to_string(&manifest_path)
            .with_context(|| format!("failed to read {}", manifest_path.display()))?;
        let manifest: CorpusManifest = toml::from_str(&manifest_text)
            .with_context(|| format!("failed to parse {}", manifest_path.display()))?;
        manifest.validate()?;

        let mut case_paths = Vec::new();
        collect_case_manifests(&root, &mut case_paths)?;
        case_paths.sort();

        let mut workloads = Vec::with_capacity(case_paths.len());
        let mut corpus_files = vec![manifest_path];
        let mut ids = BTreeSet::new();
        for case_path in case_paths {
            let directory = case_path
                .parent()
                .context("case.toml has no parent directory")?;
            let source_path = directory.join("main.yu");
            ensure!(
                source_path.is_file(),
                "workload manifest has no main.yu: {}",
                case_path.display()
            );

            let case_text = fs::read_to_string(&case_path)
                .with_context(|| format!("failed to read {}", case_path.display()))?;
            let case: WorkloadCase = toml::from_str(&case_text)
                .with_context(|| format!("failed to parse {}", case_path.display()))?;
            case.validate()?;

            let relative_directory = directory
                .strip_prefix(&root)
                .context("workload escaped the corpus directory")?;
            let directory_id = slash_path(relative_directory);
            ensure!(
                case.workload_id == directory_id,
                "workload_id {:?} does not match directory {:?}",
                case.workload_id,
                directory_id
            );
            ensure!(
                ids.insert(case.workload_id.clone()),
                "duplicate workload_id {:?}",
                case.workload_id
            );

            let source_sha256 = sha256_file(&source_path)?;
            let expected_sha256 =
                manifest
                    .source_sha256
                    .get(&case.workload_id)
                    .with_context(|| {
                        format!("corpus.toml has no source hash for {}", case.workload_id)
                    })?;
            ensure!(
                &source_sha256 == expected_sha256,
                "source hash mismatch for {}: expected {}, got {}",
                case.workload_id,
                expected_sha256,
                source_sha256
            );

            corpus_files.push(case_path.clone());
            corpus_files.push(source_path.clone());
            workloads.push(Workload {
                source_path,
                source_sha256,
                case,
            });
        }

        validate_catalog(&manifest, &workloads)?;
        let sha256 = hash_corpus_files(&root, &mut corpus_files)?;

        if !only.is_empty() {
            let requested: BTreeSet<_> = only.iter().cloned().collect();
            let missing: Vec<_> = requested.difference(&ids).cloned().collect();
            if !missing.is_empty() {
                bail!("unknown --only workload id(s): {}", missing.join(", "));
            }
            workloads.retain(|workload| requested.contains(&workload.case.workload_id));
        }

        Ok(Self {
            root,
            manifest,
            sha256,
            workloads,
        })
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct CorpusManifest {
    pub schema_version: u32,
    pub benchmark: String,
    pub benchmark_version: u32,
    pub corpus_revision: u32,
    pub frozen_at: String,
    pub workload_count: usize,
    pub categories: BTreeMap<String, usize>,
    pub subsets: BTreeMap<String, usize>,
    pub source_sha256: BTreeMap<String, String>,
    pub oracle: OracleIdentity,
}

impl CorpusManifest {
    fn validate(&self) -> Result<()> {
        ensure!(
            self.schema_version == 1,
            "unsupported corpus schema_version {}",
            self.schema_version
        );
        ensure!(
            self.benchmark == "runtime",
            "unsupported benchmark {:?}",
            self.benchmark
        );
        ensure!(
            self.benchmark_version == 0,
            "unsupported benchmark_version {}",
            self.benchmark_version
        );
        ensure!(
            self.workload_count > 0,
            "corpus workload_count must be greater than zero"
        );
        ensure!(
            self.oracle.tag == "yulang2-oracle",
            "unexpected oracle tag {:?}",
            self.oracle.tag
        );
        validate_git_oid("oracle.tag_object", &self.oracle.tag_object)?;
        validate_git_oid("oracle.commit", &self.oracle.commit)?;
        for (workload_id, hash) in &self.source_sha256 {
            validate_sha256(&format!("source_sha256.{workload_id}"), hash)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct OracleIdentity {
    pub tag: String,
    pub tag_object: String,
    pub commit: String,
}

#[derive(Debug)]
pub struct Workload {
    pub source_path: PathBuf,
    pub source_sha256: String,
    pub case: WorkloadCase,
}

#[derive(Debug, Clone, Deserialize)]
pub struct WorkloadCase {
    pub workload_id: String,
    pub category: String,
    pub subsets: Vec<String>,
    pub std: StdMode,
    pub expected_root: String,
    #[serde(default)]
    pub parameters: BTreeMap<String, toml::Value>,
}

impl WorkloadCase {
    fn validate(&self) -> Result<()> {
        ensure!(
            !self.workload_id.is_empty(),
            "workload_id must not be empty"
        );
        ensure!(
            !self.category.is_empty(),
            "category must not be empty for {}",
            self.workload_id
        );
        ensure!(
            !self.subsets.is_empty(),
            "subsets must not be empty for {}",
            self.workload_id
        );
        ensure!(
            !self.expected_root.is_empty(),
            "expected_root must not be empty for {}",
            self.workload_id
        );
        let unique: BTreeSet<_> = self.subsets.iter().collect();
        ensure!(
            unique.len() == self.subsets.len(),
            "duplicate subset for {}",
            self.workload_id
        );
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum StdMode {
    None,
    Repo,
}

fn collect_case_manifests(directory: &Path, output: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(directory)
        .with_context(|| format!("failed to scan {}", directory.display()))?
    {
        let entry = entry.with_context(|| format!("failed to scan {}", directory.display()))?;
        let file_type = entry
            .file_type()
            .with_context(|| format!("failed to inspect {}", entry.path().display()))?;
        if file_type.is_symlink() {
            bail!(
                "symlinks are not allowed in the frozen corpus: {}",
                entry.path().display()
            );
        }
        if file_type.is_dir() {
            collect_case_manifests(&entry.path(), output)?;
        } else if file_type.is_file() && entry.file_name() == "case.toml" {
            output.push(entry.path());
        }
    }
    Ok(())
}

fn validate_catalog(manifest: &CorpusManifest, workloads: &[Workload]) -> Result<()> {
    ensure!(
        workloads.len() == manifest.workload_count,
        "corpus declares {} workloads but contains {}",
        manifest.workload_count,
        workloads.len()
    );
    ensure!(
        manifest.source_sha256.len() == workloads.len(),
        "corpus declares {} source hashes for {} workloads",
        manifest.source_sha256.len(),
        workloads.len()
    );

    let mut categories = BTreeMap::new();
    let mut subsets = BTreeMap::new();
    for workload in workloads {
        *categories
            .entry(workload.case.category.clone())
            .or_insert(0) += 1;
        for subset in &workload.case.subsets {
            *subsets.entry(subset.clone()).or_insert(0) += 1;
        }
    }
    ensure!(
        categories == manifest.categories,
        "corpus category counts do not match corpus.toml"
    );
    ensure!(
        subsets == manifest.subsets,
        "corpus subset counts do not match corpus.toml"
    );
    Ok(())
}

fn hash_corpus_files(root: &Path, files: &mut [PathBuf]) -> Result<String> {
    files.sort();
    let mut hasher = Sha256::new();
    for path in files.iter() {
        let relative = path
            .strip_prefix(root)
            .context("corpus file escaped corpus root")?;
        let relative = slash_path(relative);
        let bytes = fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
        hasher.update(&(relative.len() as u64).to_le_bytes());
        hasher.update(relative.as_bytes());
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    Ok(hasher.finish())
}

fn validate_sha256(field: &str, value: &str) -> Result<()> {
    ensure!(
        value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "{field} is not a SHA-256/SHA object hex string: {value:?}"
    );
    Ok(())
}

fn validate_git_oid(field: &str, value: &str) -> Result<()> {
    ensure!(
        matches!(value.len(), 40 | 64) && value.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "{field} is not a Git object id: {value:?}"
    );
    Ok(())
}

fn slash_path(path: &Path) -> String {
    path.iter()
        .map(|component| component.to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

#[cfg(test)]
mod tests {
    use super::Corpus;

    #[test]
    fn frozen_runtime_corpus_is_self_consistent() {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/perf/runtime/v0");
        let corpus = Corpus::load(&root, &[]).expect("load frozen corpus");
        assert_eq!(corpus.workloads.len(), 10);
    }
}
