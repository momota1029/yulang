use super::*;

pub(super) struct Collector {
    seen_files: HashSet<PathBuf>,
    module_files: HashMap<Path, PathBuf>,
    files: Vec<CollectedSource>,
}

impl Collector {
    pub(super) fn new() -> Self {
        Self {
            seen_files: HashSet::new(),
            module_files: HashMap::new(),
            files: Vec::new(),
        }
    }

    pub(super) fn collect_std_root(&mut self, std_root: &FsPath) -> Result<(), RouteError> {
        self.collect_module_tree(
            std_root.join("std.yu"),
            Path {
                segments: vec![Name("std".to_string())],
            },
        )
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
        let mut queue = VecDeque::from([(entry.to_path_buf(), Path::default(), source)]);
        while let Some((path, module_path, source_override)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.seen_files.insert(canonical) {
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
                queue.push_back((child_path, requested_module, None));
            }
        }
        Ok(std::mem::take(&mut self.files))
    }

    fn collect_module_tree(
        &mut self,
        entry: PathBuf,
        entry_module_path: Path,
    ) -> Result<(), RouteError> {
        let mut queue = VecDeque::from([(entry, entry_module_path)]);
        while let Some((path, module_path)) = queue.pop_front() {
            let canonical = canonicalize_for_dedupe(&path);
            self.record_module_file(&module_path, &canonical)?;
            if !self.seen_files.insert(canonical) {
                continue;
            }

            let source = fs::read_to_string(&path).map_err(|error| RouteError::Io {
                path: path.clone(),
                error,
            })?;
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
                queue.push_back((child_path, requested_module));
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
}
