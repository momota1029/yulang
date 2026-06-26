use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
struct SourceOwner {
    module_path: Path,
    band_path: Path,
}

pub(super) struct Collector {
    seen_files: HashMap<PathBuf, SourceOwner>,
    module_files: HashMap<Path, PathBuf>,
    files: Vec<CollectedSource>,
}

impl Collector {
    pub(super) fn new() -> Self {
        Self {
            seen_files: HashMap::new(),
            module_files: HashMap::new(),
            files: Vec::new(),
        }
    }

    pub(super) fn collect_std_root(&mut self, std_root: &FsPath) -> Result<(), RouteError> {
        self.collect_module_tree_with_source_overrides(
            std_root.join("std.yu"),
            Path {
                segments: vec![Name("std".to_string())],
            },
            Path {
                segments: vec![Name("std".to_string())],
            },
            &mut HashMap::new(),
        )
    }

    pub(super) fn collect_std_root_with_source_override(
        &mut self,
        std_root: &FsPath,
        override_path: &FsPath,
        source: String,
    ) -> Result<(), RouteError> {
        let mut source_overrides =
            HashMap::from([(canonicalize_for_dedupe(override_path), source)]);
        self.collect_module_tree_with_source_overrides(
            std_root.join("std.yu"),
            Path {
                segments: vec![Name("std".to_string())],
            },
            Path {
                segments: vec![Name("std".to_string())],
            },
            &mut source_overrides,
        )
    }

    pub(super) fn finish(mut self) -> Vec<CollectedSource> {
        std::mem::take(&mut self.files)
    }

    pub(super) fn collect_entry(
        mut self,
        entry: &FsPath,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        self.collect_entry_inner(entry, None, implicit_prelude)
    }

    pub(super) fn collect_entry_source(
        mut self,
        entry: &FsPath,
        source: String,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        self.collect_entry_inner(entry, Some(source), implicit_prelude)
    }

    fn collect_entry_inner(
        &mut self,
        entry: &FsPath,
        source: Option<String>,
        implicit_prelude: bool,
    ) -> Result<Vec<CollectedSource>, RouteError> {
        let realm_root = sources::local_realm_root(entry);
        let root_band = Path::default();
        let mut queue = VecDeque::from([(entry.to_path_buf(), Path::default(), root_band, source)]);
        while let Some((path, module_path, band_path, source_override)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.record_seen_file(&module_path, &band_path, &canonical)? {
                continue;
            }

            let mut source = match source_override {
                Some(source) => source,
                None => fs::read_to_string(&path).map_err(|error| RouteError::Io {
                    path: path.clone(),
                    error,
                })?,
            };
            if implicit_prelude && module_path.segments.is_empty() {
                source = source_with_implicit_std_prelude(source);
            }

            let requests = discover_module_loads(&module_path, &source);
            let current_realm_bands = discover_current_realm_band_loads(&source);
            self.files.push(CollectedSource {
                path: path.clone(),
                module_path: module_path.clone(),
                source,
            });

            for request in requests {
                let requested_module = request.module_path();
                if self.module_files.contains_key(&requested_module) {
                    continue;
                }
                let child_path = resolve_module_file(&path, &module_path, &request)?;
                queue.push_back((child_path, requested_module, band_path.clone(), None));
            }

            for band in current_realm_bands {
                if self.module_files.contains_key(&band) {
                    continue;
                }
                let band_path = resolve_realm_band_file(&realm_root, &band)?;
                queue.push_back((band_path, band.clone(), band, None));
            }
        }
        Ok(std::mem::take(&mut self.files))
    }

    fn collect_module_tree_with_source_overrides(
        &mut self,
        entry: PathBuf,
        entry_module_path: Path,
        entry_band_path: Path,
        source_overrides: &mut HashMap<PathBuf, String>,
    ) -> Result<(), RouteError> {
        let mut queue = VecDeque::from([(entry, entry_module_path, entry_band_path)]);
        while let Some((path, module_path, band_path)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.record_seen_file(&module_path, &band_path, &canonical)? {
                continue;
            }

            let source = match source_overrides.remove(&canonical) {
                Some(source) => source,
                None => fs::read_to_string(&path).map_err(|error| RouteError::Io {
                    path: path.clone(),
                    error,
                })?,
            };
            let requests = discover_module_loads(&module_path, &source);
            self.files.push(CollectedSource {
                path: path.clone(),
                module_path: module_path.clone(),
                source,
            });

            for request in requests {
                let requested_module = request.module_path();
                if self.module_files.contains_key(&requested_module) {
                    continue;
                }
                let child_path = resolve_module_file(&path, &module_path, &request)?;
                queue.push_back((child_path, requested_module, band_path.clone()));
            }
        }
        Ok(())
    }

    fn record_module_file(&mut self, module: &Path, file: &FsPath) -> Result<(), RouteError> {
        let Some(first) = self.module_files.get(module) else {
            self.module_files.insert(module.clone(), file.to_path_buf());
            return Ok(());
        };
        if first == file {
            return Ok(());
        }
        Err(RouteError::DuplicateModulePath {
            module: module.clone(),
            first: first.clone(),
            second: file.to_path_buf(),
        })
    }

    fn record_seen_file(
        &mut self,
        module: &Path,
        band: &Path,
        file: &FsPath,
    ) -> Result<bool, RouteError> {
        let owner = SourceOwner {
            module_path: module.clone(),
            band_path: band.clone(),
        };
        let Some(first_owner) = self.seen_files.get(file) else {
            self.seen_files.insert(file.to_path_buf(), owner);
            return Ok(true);
        };
        if first_owner == &owner {
            return Ok(false);
        }
        Err(RouteError::DuplicateModuleFile {
            file: file.to_path_buf(),
            first_module: first_owner.module_path.clone(),
            second_module: module.clone(),
        })
    }
}
