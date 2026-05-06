use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};

use rowan::{NodeOrToken, SyntaxNode};
use serde::{Deserialize, Serialize};
use yulang_core_ir::{Name, Path as ModulePath};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::{BpVec, OpDef, OpTable, standard_op_table};
use yulang_parser::parse_module_to_green;
use yulang_parser::sink::YulangLanguage;

pub fn parse_source_meta(source: &str) -> SourceMeta {
    let root = SyntaxNode::<YulangLanguage>::new_root(parse_module_to_green(source));
    let mut meta = SourceMeta::default();
    collect_leading_meta_items(&root, &mut meta);
    meta
}

pub fn collect_source_files(entry: impl AsRef<FsPath>) -> Result<SourceSet, SourceLoadError> {
    collect_source_files_with_options(entry, SourceOptions::default())
}

pub fn collect_virtual_source_files_with_options(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
) -> Result<SourceSet, SourceLoadError> {
    let mut loader = SourceLoader::new(options);
    loader.load_virtual_entry(source, base_dir.as_deref())?;
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    Ok(SourceSet {
        files: loader.files,
    })
}

pub fn collect_inline_source_files_with_options(
    source: &str,
    inline_sources: impl IntoIterator<Item = InlineSource>,
    options: SourceOptions,
) -> SourceSet {
    let mut loader = InlineSourceLoader::new(inline_sources, options);
    loader.load_entry(source);
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    SourceSet {
        files: loader.files,
    }
}

pub fn collect_source_files_with_options(
    entry: impl AsRef<FsPath>,
    options: SourceOptions,
) -> Result<SourceSet, SourceLoadError> {
    let mut loader = SourceLoader::new(options);
    loader.load_entry(entry.as_ref())?;
    sort_files_topologically(&mut loader.files);
    build_syntax_tables(&mut loader.files);
    Ok(SourceSet {
        files: loader.files,
    })
}

pub const COMPILED_UNIT_ARTIFACT_FORMAT_VERSION: u32 = 1;
pub const COMPILED_UNIT_PARSER_FORMAT_VERSION: u32 = 1;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceOptions {
    pub std_root: Option<PathBuf>,
    pub implicit_prelude: bool,
    pub search_paths: Vec<PathBuf>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceMeta {
    pub module_files: Vec<ModuleFileDecl>,
    pub uses: Vec<UseDeclMeta>,
    pub syntax_exports: Vec<SyntaxExport>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleFileDecl {
    pub visibility: Visibility,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDeclMeta {
    pub visibility: Visibility,
    pub import: UseImport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseImport {
    Alias {
        name: Name,
        path: ModulePath,
    },
    Glob {
        prefix: ModulePath,
        excluded: Vec<Name>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: OpDef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone)]
pub struct SourceSet {
    pub files: Vec<SourceFile>,
}

impl SourceSet {
    pub fn files_with_origin(&self, origin: SourceOrigin) -> impl Iterator<Item = &SourceFile> {
        self.files.iter().filter(move |file| file.origin == origin)
    }

    pub fn std_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::Std)
    }

    pub fn entry_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::Entry)
    }

    pub fn user_files(&self) -> impl Iterator<Item = &SourceFile> {
        self.files_with_origin(SourceOrigin::User)
    }

    pub fn compilation_units(&self) -> SourceCompilationUnits {
        SourceCompilationUnits::from_source_set(self)
    }

    pub fn compiled_unit_syntax_artifacts(&self) -> Vec<CompiledUnitSyntaxArtifact> {
        let units = self.compilation_units();
        units.syntax_artifacts(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnits {
    pub units: Vec<SourceCompilationUnit>,
    pub file_to_unit: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompilationUnit {
    pub files: Vec<usize>,
    pub dependencies: Vec<usize>,
    pub origin: SourceCompilationUnitOrigin,
    pub syntax_exports: Vec<SyntaxExport>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SourceCompilationUnitOrigin {
    Entry,
    Std,
    User,
    Mixed,
}

impl SourceCompilationUnits {
    fn from_source_set(source_set: &SourceSet) -> Self {
        let module_paths = source_set
            .files
            .iter()
            .map(|file| file.module_path.clone())
            .collect::<Vec<_>>();
        let dependencies = source_set
            .files
            .iter()
            .map(|file| source_dependencies(file, &module_paths))
            .collect::<Vec<_>>();
        let components = source_sccs(&dependencies);
        let mut file_to_unit = vec![0; source_set.files.len()];
        for (unit_idx, files) in components.iter().enumerate() {
            for &file_idx in files {
                file_to_unit[file_idx] = unit_idx;
            }
        }

        let units = components
            .iter()
            .map(|files| {
                let mut unit_deps = Vec::new();
                for &file_idx in files {
                    for &dep in &dependencies[file_idx] {
                        let dep_unit = file_to_unit[dep];
                        if dep_unit != file_to_unit[file_idx] {
                            unit_deps.push(dep_unit);
                        }
                    }
                }
                unit_deps.sort_unstable();
                unit_deps.dedup();

                SourceCompilationUnit {
                    files: files.clone(),
                    dependencies: unit_deps,
                    origin: source_unit_origin(files, &source_set.files),
                    syntax_exports: source_unit_syntax_exports(files, &source_set.files),
                }
            })
            .collect();

        Self {
            units,
            file_to_unit,
        }
    }

    pub fn syntax_artifacts(&self, source_set: &SourceSet) -> Vec<CompiledUnitSyntaxArtifact> {
        let public_exports = source_public_syntax_exports(&source_set.files);
        let unit_hashes = self
            .units
            .iter()
            .enumerate()
            .map(|(unit_idx, unit)| {
                compiled_unit_source_hash(unit_idx, unit, &source_set.files, &public_exports)
            })
            .collect::<Vec<_>>();

        self.units
            .iter()
            .enumerate()
            .map(|(unit_idx, unit)| {
                let syntax = compiled_syntax_surface(unit, &source_set.files, &public_exports);
                let manifest =
                    compiled_unit_manifest(unit_idx, unit, source_set, &unit_hashes, &syntax);
                CompiledUnitSyntaxArtifact { manifest, syntax }
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitSyntaxArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: CompiledSyntaxSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitManifest {
    pub artifact_format_version: u32,
    pub parser_format_version: u32,
    pub unit_index: usize,
    pub origin: SourceCompilationUnitOrigin,
    pub files: Vec<CompiledSourceFileIdentity>,
    pub dependencies: Vec<CompiledUnitDependency>,
    pub source_hash: u64,
    pub syntax_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSourceFileIdentity {
    pub path: String,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub source_len: usize,
    pub source_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledUnitDependency {
    pub unit_index: usize,
    pub source_hash: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxSurface {
    pub direct_exports: Vec<CompiledSyntaxExport>,
    pub public_exports: Vec<CompiledSyntaxExport>,
}

impl CompiledSyntaxSurface {
    pub fn public_op_table_contribution(&self) -> OpTable {
        compiled_exports_op_table(self.public_exports.iter())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: CompiledOperatorSyntax,
}

impl CompiledSyntaxExport {
    pub fn to_syntax_export(&self) -> SyntaxExport {
        SyntaxExport {
            visibility: self.visibility,
            name: self.name.clone(),
            op: self.op.to_op_def(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledOperatorSyntax {
    pub prefix: Option<Vec<i8>>,
    pub infix: Option<(Vec<i8>, Vec<i8>)>,
    pub suffix: Option<Vec<i8>>,
    pub nullfix: bool,
}

impl CompiledOperatorSyntax {
    pub fn from_op_def(op: &OpDef) -> Self {
        Self {
            prefix: op.prefix.as_ref().map(compiled_bp_vec),
            infix: op
                .infix
                .as_ref()
                .map(|(left, right)| (compiled_bp_vec(left), compiled_bp_vec(right))),
            suffix: op.suffix.as_ref().map(compiled_bp_vec),
            nullfix: op.nullfix,
        }
    }

    pub fn to_op_def(&self) -> OpDef {
        OpDef {
            prefix: self.prefix.as_ref().map(|bp| runtime_bp_vec(bp)),
            infix: self
                .infix
                .as_ref()
                .map(|(left, right)| (runtime_bp_vec(left), runtime_bp_vec(right))),
            suffix: self.suffix.as_ref().map(|bp| runtime_bp_vec(bp)),
            nullfix: self.nullfix,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SourceOrigin {
    Entry,
    Std,
    User,
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub op_table: OpTable,
    pub source: String,
    pub meta: SourceMeta,
}

#[derive(Debug, Clone)]
pub struct InlineSource {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub origin: SourceOrigin,
    pub source: String,
    pub meta: Option<SourceMeta>,
}

#[derive(Debug)]
pub enum SourceLoadError {
    Io { path: PathBuf, error: io::Error },
    ModuleNotFound { parent: PathBuf, name: Name },
}

impl fmt::Display for SourceLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceLoadError::Io { path, error } => {
                write!(f, "failed to read {}: {error}", path.display())
            }
            SourceLoadError::ModuleNotFound { parent, name } => {
                write!(
                    f,
                    "module file for `{}` not found next to {}",
                    name.0,
                    parent.display()
                )
            }
        }
    }
}

impl std::error::Error for SourceLoadError {}

struct SourceLoader {
    options: SourceOptions,
    seen: HashSet<PathBuf>,
    files: Vec<SourceFile>,
}

struct InlineSourceLoader {
    options: SourceOptions,
    sources: HashMap<ModulePath, InlineSource>,
    seen: HashSet<ModulePath>,
    files: Vec<SourceFile>,
}

impl InlineSourceLoader {
    fn new(inline_sources: impl IntoIterator<Item = InlineSource>, options: SourceOptions) -> Self {
        Self {
            options,
            sources: inline_sources
                .into_iter()
                .map(|source| (source.module_path.clone(), source))
                .collect(),
            seen: HashSet::new(),
            files: Vec::new(),
        }
    }

    fn load_entry(&mut self, source: &str) {
        let source_prefix = if self.options.implicit_prelude {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_source(
            PathBuf::from("<virtual-entry>"),
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            source,
            source_prefix,
            None,
        );
    }

    fn load_module_path(&mut self, module_path: &ModulePath) {
        if module_path.segments.is_empty() || self.seen.contains(module_path) {
            return;
        }
        let Some(source) = self.sources.get(module_path).cloned() else {
            return;
        };
        let InlineSource {
            path,
            module_path,
            origin,
            source,
            meta,
        } = source;
        self.load_source(path, module_path, origin, &source, "", meta);
    }

    fn load_source(
        &mut self,
        path: PathBuf,
        module_path: ModulePath,
        origin: SourceOrigin,
        source: &str,
        source_prefix: &str,
        cached_meta: Option<SourceMeta>,
    ) {
        if !self.seen.insert(module_path.clone()) {
            return;
        }

        let mut source = source.to_string();
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = cached_meta.unwrap_or_else(|| parse_source_meta(&source));
        let dependencies = inline_dependencies(&module_path, &meta);
        self.files.push(SourceFile {
            path,
            module_path,
            origin,
            op_table: standard_op_table(),
            source,
            meta,
        });
        for dependency in dependencies {
            self.load_module_path(&dependency);
        }
    }
}

impl SourceLoader {
    fn new(options: SourceOptions) -> Self {
        Self {
            options,
            seen: HashSet::new(),
            files: Vec::new(),
        }
    }

    fn load_entry(&mut self, path: &FsPath) -> Result<(), SourceLoadError> {
        let source_prefix = if self.options.implicit_prelude && self.options.std_root.is_some() {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_module_with_prefix(
            path,
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            source_prefix,
        )
    }

    fn load_virtual_entry(
        &mut self,
        source: &str,
        base_dir: Option<&FsPath>,
    ) -> Result<(), SourceLoadError> {
        let source_prefix = if self.options.implicit_prelude && self.options.std_root.is_some() {
            "use std::prelude::*\n"
        } else {
            ""
        };
        self.load_virtual_module_with_prefix(
            source,
            ModulePath { segments: vec![] },
            SourceOrigin::Entry,
            source_prefix,
            base_dir,
        )
    }

    fn load_module(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
        origin: SourceOrigin,
    ) -> Result<(), SourceLoadError> {
        self.load_module_with_prefix(path, module_path, origin, "")
    }

    fn load_module_with_prefix(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
        origin: SourceOrigin,
        source_prefix: &str,
    ) -> Result<(), SourceLoadError> {
        let canonical = canonicalize_for_dedupe(path);
        if !self.seen.insert(canonical) {
            return Ok(());
        }

        let mut source = fs::read_to_string(path).map_err(|error| SourceLoadError::Io {
            path: path.to_path_buf(),
            error,
        })?;
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = parse_source_meta(&source);
        let parent = path.parent().unwrap_or_else(|| FsPath::new("."));
        let module_paths = meta
            .module_files
            .iter()
            .map(|decl| {
                let mut child_module = module_path.segments.clone();
                child_module.push(decl.name.clone());
                resolve_module_file(parent, &decl.name).map(|path| {
                    (
                        path,
                        ModulePath {
                            segments: child_module,
                        },
                        child_origin(origin),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let imported_paths = meta
            .uses
            .iter()
            .filter_map(|use_| import_module_path(&use_.import))
            .filter_map(|module_path| {
                self.resolve_import_module_file(&module_path)
                    .map(|path| (path, module_path.clone(), import_origin(&module_path)))
            })
            .collect::<Vec<_>>();

        self.files.push(SourceFile {
            path: path.to_path_buf(),
            module_path,
            origin,
            op_table: standard_op_table(),
            source,
            meta,
        });

        for (path, module_path, origin) in module_paths {
            self.load_module(&path, module_path, origin)?;
        }
        for (path, module_path, origin) in imported_paths {
            self.load_module(&path, module_path, origin)?;
        }
        Ok(())
    }

    fn load_virtual_module_with_prefix(
        &mut self,
        source: &str,
        module_path: ModulePath,
        origin: SourceOrigin,
        source_prefix: &str,
        base_dir: Option<&FsPath>,
    ) -> Result<(), SourceLoadError> {
        let synthetic_path = base_dir
            .map(|dir| dir.join("<virtual-entry>"))
            .unwrap_or_else(|| PathBuf::from("<virtual-entry>"));
        let canonical = canonicalize_for_dedupe(&synthetic_path);
        if !self.seen.insert(canonical) {
            return Ok(());
        }

        let mut source = source.to_string();
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = parse_source_meta(&source);
        let parent = base_dir.unwrap_or_else(|| FsPath::new("."));
        let module_paths = meta
            .module_files
            .iter()
            .map(|decl| {
                let mut child_module = module_path.segments.clone();
                child_module.push(decl.name.clone());
                resolve_module_file(parent, &decl.name).map(|path| {
                    (
                        path,
                        ModulePath {
                            segments: child_module,
                        },
                        child_origin(origin),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let imported_paths = meta
            .uses
            .iter()
            .filter_map(|use_| import_module_path(&use_.import))
            .filter_map(|module_path| {
                self.resolve_import_module_file(&module_path)
                    .map(|path| (path, module_path.clone(), import_origin(&module_path)))
            })
            .collect::<Vec<_>>();

        self.files.push(SourceFile {
            path: synthetic_path,
            module_path,
            origin,
            op_table: standard_op_table(),
            source,
            meta,
        });

        for (path, module_path, origin) in module_paths {
            self.load_module(&path, module_path, origin)?;
        }
        for (path, module_path, origin) in imported_paths {
            self.load_module(&path, module_path, origin)?;
        }
        Ok(())
    }

    fn resolve_import_module_file(&self, module_path: &ModulePath) -> Option<PathBuf> {
        if module_path.segments.is_empty() {
            return None;
        }

        if module_path
            .segments
            .first()
            .is_some_and(|name| name.0 == "std")
        {
            let std_root = self.options.std_root.as_ref()?;
            return resolve_module_path_under_root(std_root, &module_path.segments[1..]);
        }

        self.options
            .search_paths
            .iter()
            .find_map(|root| resolve_module_path_under_root(root, &module_path.segments))
    }
}

fn child_origin(parent: SourceOrigin) -> SourceOrigin {
    match parent {
        SourceOrigin::Std => SourceOrigin::Std,
        SourceOrigin::Entry | SourceOrigin::User => SourceOrigin::User,
    }
}

fn import_origin(module_path: &ModulePath) -> SourceOrigin {
    if module_path
        .segments
        .first()
        .is_some_and(|name| name.0 == "std")
    {
        SourceOrigin::Std
    } else {
        SourceOrigin::User
    }
}

fn collect_leading_meta_items(root: &SyntaxNode<YulangLanguage>, meta: &mut SourceMeta) {
    for node in root.children() {
        if node.kind() == SyntaxKind::IndentBlock {
            collect_leading_meta_items(&node, meta);
            return;
        }

        if node.kind() == SyntaxKind::DocCommentDecl {
            continue;
        }

        if let Some(decl) = module_file_decl(&node) {
            meta.module_files.push(decl);
            continue;
        }

        if node.kind() == SyntaxKind::UseDecl {
            let visibility = lower_visibility(&node);
            meta.uses.extend(
                use_decl_imports(&node)
                    .into_iter()
                    .map(|import| UseDeclMeta { visibility, import }),
            );
            continue;
        }

        if let Some(export) = syntax_export(&node) {
            meta.syntax_exports.push(export);
            continue;
        }

        break;
    }
}

fn sort_files_topologically(files: &mut Vec<SourceFile>) {
    let module_paths = files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();
    let dependencies = files
        .iter()
        .map(|file| source_dependencies(file, &module_paths))
        .collect::<Vec<_>>();
    let mut marks = vec![VisitMark::Unvisited; files.len()];
    let mut order = Vec::new();

    for idx in 0..files.len() {
        visit_source_file(idx, &dependencies, &mut marks, &mut order);
    }

    let mut old = std::mem::take(files)
        .into_iter()
        .map(Some)
        .collect::<Vec<_>>();
    *files = order
        .into_iter()
        .filter_map(|idx| old[idx].take())
        .collect();
}

fn source_dependencies(file: &SourceFile, module_paths: &[ModulePath]) -> Vec<usize> {
    let mut deps = Vec::new();

    for decl in &file.meta.module_files {
        let mut child = file.module_path.segments.clone();
        child.push(decl.name.clone());
        push_module_dependency(&child, &file.module_path, module_paths, &mut deps);
    }

    for use_ in &file.meta.uses {
        match &use_.import {
            UseImport::Alias { path, .. } => {
                push_best_module_dependency(path, &file.module_path, module_paths, &mut deps);
            }
            UseImport::Glob { prefix, .. } => {
                push_best_module_dependency(prefix, &file.module_path, module_paths, &mut deps);
            }
        }
    }

    deps.sort_unstable();
    deps.dedup();
    deps
}

fn source_sccs(dependencies: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut ctx = SourceSccContext {
        dependencies,
        index: 0,
        stack: Vec::new(),
        on_stack: vec![false; dependencies.len()],
        indices: vec![None; dependencies.len()],
        lowlink: vec![0; dependencies.len()],
        components: Vec::new(),
    };
    for file in 0..dependencies.len() {
        if ctx.indices[file].is_none() {
            source_scc_connect(file, &mut ctx);
        }
    }
    ctx.components.reverse();
    ctx.components
}

struct SourceSccContext<'a> {
    dependencies: &'a [Vec<usize>],
    index: usize,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    indices: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    components: Vec<Vec<usize>>,
}

fn source_scc_connect(file: usize, ctx: &mut SourceSccContext<'_>) {
    ctx.indices[file] = Some(ctx.index);
    ctx.lowlink[file] = ctx.index;
    ctx.index += 1;
    ctx.stack.push(file);
    ctx.on_stack[file] = true;

    for &dep in &ctx.dependencies[file] {
        if ctx.indices[dep].is_none() {
            source_scc_connect(dep, ctx);
            ctx.lowlink[file] = ctx.lowlink[file].min(ctx.lowlink[dep]);
        } else if ctx.on_stack[dep] {
            ctx.lowlink[file] = ctx.lowlink[file].min(ctx.indices[dep].unwrap());
        }
    }

    if ctx.lowlink[file] == ctx.indices[file].unwrap() {
        let mut component = Vec::new();
        while let Some(member) = ctx.stack.pop() {
            ctx.on_stack[member] = false;
            component.push(member);
            if member == file {
                break;
            }
        }
        component.sort_unstable();
        ctx.components.push(component);
    }
}

fn source_unit_origin(files: &[usize], source_files: &[SourceFile]) -> SourceCompilationUnitOrigin {
    let mut origin = None;
    for &file in files {
        match origin {
            None => origin = Some(source_files[file].origin),
            Some(existing) if existing == source_files[file].origin => {}
            Some(_) => return SourceCompilationUnitOrigin::Mixed,
        }
    }
    match origin.unwrap_or(SourceOrigin::User) {
        SourceOrigin::Entry => SourceCompilationUnitOrigin::Entry,
        SourceOrigin::Std => SourceCompilationUnitOrigin::Std,
        SourceOrigin::User => SourceCompilationUnitOrigin::User,
    }
}

fn source_unit_syntax_exports(files: &[usize], source_files: &[SourceFile]) -> Vec<SyntaxExport> {
    let mut exports = Vec::new();
    for &file in files {
        exports.extend(source_files[file].meta.syntax_exports.iter().cloned());
    }
    exports.sort_by(|left, right| left.name.0.cmp(&right.name.0));
    exports
}

fn source_public_syntax_exports(source_files: &[SourceFile]) -> Vec<HashMap<Name, OpDef>> {
    let module_paths = source_files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();
    let mut public_exports = source_files
        .iter()
        .map(|file| local_public_syntax_exports(&file.meta))
        .collect::<Vec<_>>();

    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..source_files.len() {
            for use_ in &source_files[idx].meta.uses {
                if use_.visibility == Visibility::My {
                    continue;
                }
                let imported =
                    imported_syntax_exports(&use_.import, &module_paths, &public_exports);
                for (name, op) in imported {
                    changed |= insert_export_op_def(&mut public_exports[idx], name, op);
                }
            }
        }
    }

    public_exports
}

fn compiled_unit_manifest(
    unit_idx: usize,
    unit: &SourceCompilationUnit,
    source_set: &SourceSet,
    unit_hashes: &[u64],
    syntax: &CompiledSyntaxSurface,
) -> CompiledUnitManifest {
    let files = unit
        .files
        .iter()
        .map(|&file_idx| {
            let file = &source_set.files[file_idx];
            CompiledSourceFileIdentity {
                path: file.path.to_string_lossy().to_string(),
                module_path: file.module_path.clone(),
                origin: file.origin,
                source_len: file.source.len(),
                source_hash: stable_hash_bytes(file.source.as_bytes()),
            }
        })
        .collect::<Vec<_>>();
    let dependencies = unit
        .dependencies
        .iter()
        .map(|&dep| CompiledUnitDependency {
            unit_index: dep,
            source_hash: unit_hashes[dep],
        })
        .collect::<Vec<_>>();
    let source_hash = unit_hashes[unit_idx];
    let syntax_hash = stable_hash_compiled_exports(&syntax.public_exports);

    CompiledUnitManifest {
        artifact_format_version: COMPILED_UNIT_ARTIFACT_FORMAT_VERSION,
        parser_format_version: COMPILED_UNIT_PARSER_FORMAT_VERSION,
        unit_index: unit_idx,
        origin: unit.origin,
        files,
        dependencies,
        source_hash,
        syntax_hash,
    }
}

fn compiled_syntax_surface(
    unit: &SourceCompilationUnit,
    source_files: &[SourceFile],
    public_exports: &[HashMap<Name, OpDef>],
) -> CompiledSyntaxSurface {
    let mut direct_exports = Vec::new();
    for &file_idx in &unit.files {
        direct_exports.extend(
            source_files[file_idx]
                .meta
                .syntax_exports
                .iter()
                .map(compiled_syntax_export),
        );
    }
    sort_compiled_exports(&mut direct_exports);

    let mut public_unit_table = HashMap::new();
    for &file_idx in &unit.files {
        for (name, op) in &public_exports[file_idx] {
            insert_export_op_def(&mut public_unit_table, name.clone(), op.clone());
        }
    }
    let mut public_unit_exports = public_unit_table
        .into_iter()
        .map(|(name, op)| CompiledSyntaxExport {
            visibility: Visibility::Pub,
            name,
            op: CompiledOperatorSyntax::from_op_def(&op),
        })
        .collect::<Vec<_>>();
    sort_compiled_exports(&mut public_unit_exports);

    CompiledSyntaxSurface {
        direct_exports,
        public_exports: public_unit_exports,
    }
}

fn compiled_syntax_export(export: &SyntaxExport) -> CompiledSyntaxExport {
    CompiledSyntaxExport {
        visibility: export.visibility,
        name: export.name.clone(),
        op: CompiledOperatorSyntax::from_op_def(&export.op),
    }
}

fn sort_compiled_exports(exports: &mut [CompiledSyntaxExport]) {
    exports.sort_by(|left, right| {
        left.name.cmp(&right.name).then_with(|| {
            compiled_operator_sort_key(&left.op).cmp(&compiled_operator_sort_key(&right.op))
        })
    });
}

fn compiled_exports_op_table<'a>(
    exports: impl IntoIterator<Item = &'a CompiledSyntaxExport>,
) -> OpTable {
    let mut table = OpTable::new();
    for export in exports {
        insert_table_op_def(&mut table.0, export.name.clone(), export.op.to_op_def());
    }
    table
}

fn compiled_bp_vec(bp: &BpVec) -> Vec<i8> {
    bp.0.iter().copied().collect()
}

fn runtime_bp_vec(bp: &[i8]) -> BpVec {
    BpVec::new(bp.to_vec())
}

fn compiled_unit_source_hash(
    unit_idx: usize,
    unit: &SourceCompilationUnit,
    source_files: &[SourceFile],
    public_exports: &[HashMap<Name, OpDef>],
) -> u64 {
    let mut hash = StableHash::new();
    hash.write_u64(unit_idx as u64);
    hash.write_str(source_unit_origin_tag(unit.origin));
    for &file_idx in &unit.files {
        let file = &source_files[file_idx];
        hash.write_str(&file.path.to_string_lossy());
        hash.write_path(&file.module_path);
        hash.write_str(source_origin_tag(file.origin));
        hash.write_u64(file.source.len() as u64);
        hash.write_u64(stable_hash_bytes(file.source.as_bytes()));
    }
    for export in &compiled_syntax_surface(unit, source_files, public_exports).public_exports {
        hash.write_compiled_export(export);
    }
    hash.finish()
}

fn stable_hash_bytes(bytes: &[u8]) -> u64 {
    let mut hash = StableHash::new();
    hash.write_bytes(bytes);
    hash.finish()
}

fn stable_hash_compiled_exports(exports: &[CompiledSyntaxExport]) -> u64 {
    let mut hash = StableHash::new();
    for export in exports {
        hash.write_compiled_export(export);
    }
    hash.finish()
}

fn compiled_operator_sort_key(op: &CompiledOperatorSyntax) -> String {
    format!(
        "p={:?};i={:?};s={:?};n={}",
        op.prefix, op.infix, op.suffix, op.nullfix
    )
}

fn source_origin_tag(origin: SourceOrigin) -> &'static str {
    match origin {
        SourceOrigin::Entry => "entry",
        SourceOrigin::Std => "std",
        SourceOrigin::User => "user",
    }
}

fn source_unit_origin_tag(origin: SourceCompilationUnitOrigin) -> &'static str {
    match origin {
        SourceCompilationUnitOrigin::Entry => "entry",
        SourceCompilationUnitOrigin::Std => "std",
        SourceCompilationUnitOrigin::User => "user",
        SourceCompilationUnitOrigin::Mixed => "mixed",
    }
}

struct StableHash {
    value: u64,
}

impl StableHash {
    fn new() -> Self {
        Self {
            value: 0xcbf29ce484222325,
        }
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.write_u64(bytes.len() as u64);
        self.write_raw_bytes(bytes);
    }

    fn write_raw_bytes(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.value ^= u64::from(*byte);
            self.value = self.value.wrapping_mul(0x100000001b3);
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.write_raw_bytes(&value.to_le_bytes());
    }

    fn write_str(&mut self, value: &str) {
        self.write_bytes(value.as_bytes());
    }

    fn write_path(&mut self, path: &ModulePath) {
        self.write_u64(path.segments.len() as u64);
        for segment in &path.segments {
            self.write_str(&segment.0);
        }
    }

    fn write_compiled_export(&mut self, export: &CompiledSyntaxExport) {
        self.write_str(visibility_tag(export.visibility));
        self.write_str(&export.name.0);
        self.write_operator(&export.op);
    }

    fn write_operator(&mut self, op: &CompiledOperatorSyntax) {
        self.write_optional_bp(op.prefix.as_deref());
        if let Some((left, right)) = &op.infix {
            self.write_str("some-infix");
            self.write_bp(left);
            self.write_bp(right);
        } else {
            self.write_str("none-infix");
        }
        self.write_optional_bp(op.suffix.as_deref());
        self.write_str(if op.nullfix { "nullfix" } else { "no-nullfix" });
    }

    fn write_optional_bp(&mut self, bp: Option<&[i8]>) {
        if let Some(bp) = bp {
            self.write_str("some-bp");
            self.write_bp(bp);
        } else {
            self.write_str("none-bp");
        }
    }

    fn write_bp(&mut self, bp: &[i8]) {
        self.write_u64(bp.len() as u64);
        for value in bp {
            self.write_bytes(&value.to_le_bytes());
        }
    }

    fn finish(self) -> u64 {
        self.value
    }
}

fn visibility_tag(visibility: Visibility) -> &'static str {
    match visibility {
        Visibility::Pub => "pub",
        Visibility::Our => "our",
        Visibility::My => "my",
    }
}

fn import_module_path(import: &UseImport) -> Option<ModulePath> {
    match import {
        UseImport::Alias { path, .. } => {
            let (_, prefix) = path.segments.split_last()?;
            if prefix.is_empty() {
                None
            } else {
                Some(ModulePath {
                    segments: prefix.to_vec(),
                })
            }
        }
        UseImport::Glob { prefix, .. } if prefix.segments.is_empty() => None,
        UseImport::Glob { prefix, .. } => Some(prefix.clone()),
    }
}

fn inline_dependencies(module_path: &ModulePath, meta: &SourceMeta) -> Vec<ModulePath> {
    let mut deps = meta
        .module_files
        .iter()
        .map(|decl| {
            let mut child = module_path.segments.clone();
            child.push(decl.name.clone());
            ModulePath { segments: child }
        })
        .chain(
            meta.uses
                .iter()
                .filter_map(|use_| import_module_path(&use_.import)),
        )
        .collect::<Vec<_>>();
    deps.sort_by(|left, right| left.segments.cmp(&right.segments));
    deps.dedup();
    deps
}

fn push_best_module_dependency(
    path: &ModulePath,
    current: &ModulePath,
    module_paths: &[ModulePath],
    deps: &mut Vec<usize>,
) {
    let Some((idx, _)) = module_paths
        .iter()
        .enumerate()
        .filter(|(_, candidate)| {
            !candidate.segments.is_empty()
                && *candidate != current
                && is_prefix(&candidate.segments, &path.segments)
        })
        .max_by_key(|(_, candidate)| candidate.segments.len())
    else {
        return;
    };
    deps.push(idx);
}

fn push_module_dependency(
    path: &[Name],
    current: &ModulePath,
    module_paths: &[ModulePath],
    deps: &mut Vec<usize>,
) {
    if let Some((idx, _)) = module_paths
        .iter()
        .enumerate()
        .find(|(_, candidate)| candidate.segments == path && *candidate != current)
    {
        deps.push(idx);
    }
}

fn is_prefix(prefix: &[Name], path: &[Name]) -> bool {
    prefix.len() <= path.len() && prefix.iter().zip(path).all(|(a, b)| a == b)
}

fn visit_source_file(
    idx: usize,
    dependencies: &[Vec<usize>],
    marks: &mut [VisitMark],
    order: &mut Vec<usize>,
) {
    match marks[idx] {
        VisitMark::Done => return,
        VisitMark::Visiting => return,
        VisitMark::Unvisited => {}
    }
    marks[idx] = VisitMark::Visiting;
    for &dep in &dependencies[idx] {
        visit_source_file(dep, dependencies, marks, order);
    }
    marks[idx] = VisitMark::Done;
    order.push(idx);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitMark {
    Unvisited,
    Visiting,
    Done,
}

fn build_syntax_tables(files: &mut [SourceFile]) {
    let module_paths = files
        .iter()
        .map(|file| file.module_path.clone())
        .collect::<Vec<_>>();
    let public_exports = source_public_syntax_exports(files);

    for idx in 0..files.len() {
        let mut table = standard_op_table();
        for export in &files[idx].meta.syntax_exports {
            insert_table_op_def(&mut table.0, export.name.clone(), export.op.clone());
        }
        for use_ in &files[idx].meta.uses {
            let imported = imported_syntax_exports(&use_.import, &module_paths, &public_exports);
            for (name, op) in imported {
                insert_table_op_def(&mut table.0, name, op);
            }
        }
        files[idx].op_table = table;
    }
}

fn local_public_syntax_exports(meta: &SourceMeta) -> HashMap<Name, OpDef> {
    let mut exports = HashMap::new();
    for export in &meta.syntax_exports {
        if export.visibility != Visibility::My {
            insert_export_op_def(&mut exports, export.name.clone(), export.op.clone());
        }
    }
    exports
}

fn imported_syntax_exports(
    import: &UseImport,
    module_paths: &[ModulePath],
    public_exports: &[HashMap<Name, OpDef>],
) -> Vec<(Name, OpDef)> {
    match import {
        UseImport::Alias { name, path } => {
            let Some((module_path, imported_name)) =
                path.segments.split_last().map(|(last, prefix)| {
                    (
                        ModulePath {
                            segments: prefix.to_vec(),
                        },
                        last.clone(),
                    )
                })
            else {
                return Vec::new();
            };
            let Some(idx) = module_index(&module_path, module_paths) else {
                return Vec::new();
            };
            public_exports[idx]
                .get(&imported_name)
                .cloned()
                .map(|op| vec![(name.clone(), op)])
                .unwrap_or_default()
        }
        UseImport::Glob { prefix, excluded } => {
            let Some(idx) = module_index(prefix, module_paths) else {
                return Vec::new();
            };
            public_exports[idx]
                .iter()
                .filter(|(name, _)| !excluded.contains(name))
                .map(|(name, op)| (name.clone(), op.clone()))
                .collect()
        }
    }
}

fn module_index(path: &ModulePath, module_paths: &[ModulePath]) -> Option<usize> {
    module_paths.iter().position(|candidate| candidate == path)
}

fn insert_export_op_def(table: &mut HashMap<Name, OpDef>, name: Name, op: OpDef) -> bool {
    match table.get(&name) {
        Some(existing) => {
            let merged = merge_op_defs(existing.clone(), op);
            if existing == &merged {
                false
            } else {
                table.insert(name, merged);
                true
            }
        }
        None => {
            table.insert(name, op);
            true
        }
    }
}

fn insert_table_op_def(table: &mut yulang_parser::op::trie::Trie<OpDef>, name: Name, op: OpDef) {
    let key = name.0;
    let merged = table
        .get(key.as_bytes())
        .cloned()
        .map(|existing| merge_op_defs(existing, op.clone()))
        .unwrap_or(op);
    table.insert(key.into(), merged);
}

fn merge_op_defs(mut lhs: OpDef, rhs: OpDef) -> OpDef {
    lhs.prefix = rhs.prefix.or(lhs.prefix);
    lhs.infix = rhs.infix.or(lhs.infix);
    lhs.suffix = rhs.suffix.or(lhs.suffix);
    lhs.nullfix = lhs.nullfix || rhs.nullfix;
    lhs
}

fn module_file_decl(node: &SyntaxNode<YulangLanguage>) -> Option<ModuleFileDecl> {
    if node.kind() != SyntaxKind::ModDecl || !has_direct_token(node, SyntaxKind::Semicolon) {
        return None;
    }
    let name = direct_token_text(node, SyntaxKind::Ident).map(Name)?;
    Some(ModuleFileDecl {
        visibility: lower_visibility(node),
        name,
    })
}

fn syntax_export(node: &SyntaxNode<YulangLanguage>) -> Option<SyntaxExport> {
    if node.kind() != SyntaxKind::OpDef {
        return None;
    }
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::OpDefHeader)?;
    let name = direct_token_text(&header, SyntaxKind::OpName).map(Name)?;
    let fixity = header.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok)
            if matches!(
                tok.kind(),
                SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix
            ) =>
        {
            Some(tok.kind())
        }
        _ => None,
    })?;
    let bps = header
        .children_with_tokens()
        .filter_map(|item| match item {
            NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Number => BpVec::parse(tok.text()),
            _ => None,
        })
        .collect::<Vec<_>>();
    Some(SyntaxExport {
        visibility: lower_visibility(node),
        name,
        op: op_def_from_header(fixity, &bps),
    })
}

fn op_def_from_header(fixity: SyntaxKind, bps: &[BpVec]) -> OpDef {
    match fixity {
        SyntaxKind::Prefix => OpDef {
            prefix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Infix => OpDef {
            infix: bps.first().cloned().zip(bps.get(1).cloned()),
            ..OpDef::default()
        },
        SyntaxKind::Suffix => OpDef {
            suffix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Nullfix => OpDef {
            nullfix: true,
            ..OpDef::default()
        },
        _ => OpDef::default(),
    }
}

fn use_decl_imports(node: &SyntaxNode<YulangLanguage>) -> Vec<UseImport> {
    let mut path = Vec::new();
    let mut after_as = false;
    let mut alias = None;
    let mut imports = Vec::new();
    let mut excluding_glob = None;

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Pub | SyntaxKind::Our | SyntaxKind::My | SyntaxKind::Use => {}
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: ModulePath {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                    });
                    path.clear();
                    alias = None;
                    after_as = false;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, &mut imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, &mut imports);
                    path.clear();
                    alias = None;
                    after_as = false;
                }
            }
            _ => {}
        }
    }

    push_use_alias_import(path, alias, &mut imports);
    imports
}

fn collect_use_group_imports(
    node: &SyntaxNode<YulangLanguage>,
    base: &[Name],
    imports: &mut Vec<UseImport>,
) {
    let mut path = base.to_vec();
    let mut alias = None;
    let mut after_as = false;
    let mut consumed_nested = false;
    let mut excluding_glob = None;

    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::BraceL => {}
                SyntaxKind::BraceR => {
                    if !consumed_nested {
                        push_use_alias_import(path, alias.take(), imports);
                    }
                    return;
                }
                SyntaxKind::Comma => {
                    if !consumed_nested {
                        push_use_alias_import(path, alias.take(), imports);
                    }
                    path = base.to_vec();
                    after_as = false;
                    consumed_nested = false;
                }
                SyntaxKind::ColonColon | SyntaxKind::Slash => {}
                SyntaxKind::Ident if tok.text() == "without" => {
                    excluding_glob = imports.len().checked_sub(1);
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                }
                SyntaxKind::Ident if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::Ident if after_as => {
                    alias = Some(Name(tok.text().to_string()));
                    after_as = false;
                }
                SyntaxKind::Ident => path.push(Name(tok.text().to_string())),
                SyntaxKind::As => after_as = true,
                SyntaxKind::OpName if tok.text() == "*" => {
                    imports.push(UseImport::Glob {
                        prefix: ModulePath {
                            segments: path.clone(),
                        },
                        excluded: Vec::new(),
                    });
                    path = base.to_vec();
                    alias = None;
                    after_as = false;
                    consumed_nested = true;
                }
                SyntaxKind::OpName if excluding_glob.is_some() => {
                    push_use_glob_exclusion(
                        &mut *imports,
                        excluding_glob,
                        Name(tok.text().to_string()),
                    );
                    consumed_nested = true;
                }
                SyntaxKind::OpName => path.push(Name(tok.text().to_string())),
                SyntaxKind::ParenL | SyntaxKind::ParenR => {}
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                if excluding_glob.is_some() {
                    collect_use_glob_exclusions(&child, imports, excluding_glob);
                } else {
                    collect_use_group_imports(&child, &path, imports);
                }
                path = base.to_vec();
                alias = None;
                after_as = false;
                consumed_nested = true;
            }
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::Separator => {
                if !consumed_nested {
                    push_use_alias_import(path, alias.take(), imports);
                }
                path = base.to_vec();
                after_as = false;
                consumed_nested = false;
            }
            _ => {}
        }
    }

    if !consumed_nested {
        push_use_alias_import(path, alias, imports);
    }
}

fn collect_use_glob_exclusions(
    node: &SyntaxNode<YulangLanguage>,
    imports: &mut Vec<UseImport>,
    glob_idx: Option<usize>,
) {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Ident => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                SyntaxKind::OpName if tok.text() != "*" => {
                    push_use_glob_exclusion(imports, glob_idx, Name(tok.text().to_string()));
                }
                _ => {}
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::BraceGroup => {
                collect_use_glob_exclusions(&child, imports, glob_idx);
            }
            _ => {}
        }
    }
}

fn push_use_glob_exclusion(imports: &mut [UseImport], glob_idx: Option<usize>, name: Name) {
    let Some(idx) = glob_idx else {
        return;
    };
    let Some(UseImport::Glob { excluded, .. }) = imports.get_mut(idx) else {
        return;
    };
    if !excluded.contains(&name) {
        excluded.push(name);
    }
}

fn push_use_alias_import(path: Vec<Name>, alias: Option<Name>, imports: &mut Vec<UseImport>) {
    if path.is_empty() {
        return;
    }
    let Some(name) = alias.or_else(|| path.last().cloned()) else {
        return;
    };
    imports.push(UseImport::Alias {
        name,
        path: ModulePath { segments: path },
    });
}

fn lower_visibility(node: &SyntaxNode<YulangLanguage>) -> Visibility {
    if let Some(visibility) = direct_visibility(node) {
        return visibility;
    }
    if matches!(node.kind(), SyntaxKind::OpDef) {
        for child in node.children() {
            if child.kind() == SyntaxKind::OpDefHeader {
                if let Some(visibility) = direct_visibility(&child) {
                    return visibility;
                }
            }
        }
    }
    Visibility::My
}

fn direct_visibility(node: &SyntaxNode<YulangLanguage>) -> Option<Visibility> {
    for item in node.children_with_tokens() {
        if let NodeOrToken::Token(tok) = item {
            match tok.kind() {
                SyntaxKind::Pub => return Some(Visibility::Pub),
                SyntaxKind::Our => return Some(Visibility::Our),
                SyntaxKind::My => return Some(Visibility::My),
                _ => {}
            }
        }
    }
    None
}

fn resolve_module_file(parent: &FsPath, name: &Name) -> Result<PathBuf, SourceLoadError> {
    let direct = parent.join(format!("{}.yu", name.0));
    if direct.is_file() {
        return Ok(direct);
    }
    let nested = parent.join(&name.0).join("mod.yu");
    if nested.is_file() {
        return Ok(nested);
    }
    Err(SourceLoadError::ModuleNotFound {
        parent: parent.to_path_buf(),
        name: name.clone(),
    })
}

fn resolve_module_path_under_root(root: &FsPath, module_path: &[Name]) -> Option<PathBuf> {
    if module_path.is_empty() {
        let nested = root.join("mod.yu");
        return nested.is_file().then_some(nested);
    }

    let mut base = root.to_path_buf();
    for segment in &module_path[..module_path.len() - 1] {
        base.push(&segment.0);
    }
    let last = &module_path[module_path.len() - 1];
    let direct = base.join(format!("{}.yu", last.0));
    if direct.is_file() {
        return Some(direct);
    }
    let nested = base.join(&last.0).join("mod.yu");
    nested.is_file().then_some(nested)
}

fn canonicalize_for_dedupe(path: &FsPath) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

fn has_direct_token(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> bool {
    node.children_with_tokens()
        .any(|item| matches!(item, NodeOrToken::Token(tok) if tok.kind() == kind))
}

fn direct_token_text(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> Option<String> {
    node.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok) if tok.kind() == kind => Some(tok.text().to_string()),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(path: &ModulePath) -> Vec<&str> {
        path.segments.iter().map(|name| name.0.as_str()).collect()
    }

    fn temp_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-source-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn module_path(segments: &[&str]) -> ModulePath {
        ModulePath {
            segments: segments
                .iter()
                .map(|segment| Name((*segment).to_string()))
                .collect(),
        }
    }

    #[test]
    fn inline_sources_keep_entry_and_std_origins() {
        let set = collect_inline_source_files_with_options(
            "1",
            [InlineSource {
                path: PathBuf::from("<std>/prelude.yu"),
                module_path: module_path(&["std", "prelude"]),
                origin: SourceOrigin::Std,
                source: String::new(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        );

        assert_eq!(set.entry_files().count(), 1);
        assert_eq!(set.std_files().count(), 1);
        assert_eq!(set.user_files().count(), 0);
    }

    #[test]
    fn parses_leading_mod_file_and_use_metadata() {
        let meta =
            parse_source_meta("pub mod list;\nuse list::{List, map as list_map}\nmy x = list_map");

        assert_eq!(
            meta.module_files,
            vec![ModuleFileDecl {
                visibility: Visibility::Pub,
                name: Name("list".to_string()),
            }]
        );
        assert_eq!(meta.uses.len(), 2);
        let UseImport::Alias { name, path } = &meta.uses[0].import else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "List");
        assert_eq!(names(path), vec!["list", "List"]);
        let UseImport::Alias { name, path } = &meta.uses[1].import else {
            panic!("expected alias import");
        };
        assert_eq!(name.0, "list_map");
        assert_eq!(names(path), vec!["list", "map"]);
    }

    #[test]
    fn parses_operator_use_metadata() {
        let meta = parse_source_meta("use ops::{(+), id}\nmy x = 1");

        assert_eq!(meta.uses.len(), 2);
        let UseImport::Alias { name, path } = &meta.uses[0].import else {
            panic!("expected operator alias import");
        };
        assert_eq!(name.0, "+");
        assert_eq!(names(path), vec!["ops", "+"]);
    }

    #[test]
    fn parses_glob_without_metadata() {
        let meta = parse_source_meta("use ops::* without (%%), id\nmy x = 1");

        assert_eq!(meta.uses.len(), 1);
        let UseImport::Glob { prefix, excluded } = &meta.uses[0].import else {
            panic!("expected glob import");
        };
        assert_eq!(names(prefix), vec!["ops"]);
        assert_eq!(
            excluded
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>(),
            vec!["%%", "id"]
        );
    }

    #[test]
    fn parses_leading_operator_export_metadata() {
        let meta = parse_source_meta("pub infix (%%) 50 51 = \\x -> \\y -> y\nmy x = 1");

        assert_eq!(meta.syntax_exports.len(), 1);
        let export = &meta.syntax_exports[0];
        assert_eq!(export.visibility, Visibility::Pub);
        assert_eq!(export.name.0, "%%");
        assert!(export.op.infix.is_some());
    }

    #[test]
    fn stops_metadata_after_first_ordinary_item() {
        let meta = parse_source_meta("my x = 1\nmod late;\nuse late::x");

        assert!(meta.module_files.is_empty());
        assert!(meta.uses.is_empty());
    }

    #[test]
    fn collects_module_files_recursively() {
        let root = temp_root("collects-module-files");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("list")).unwrap();
        fs::write(root.join("main.yu"), "mod list;\nmy x = 1").unwrap();
        fs::write(root.join("list").join("mod.yu"), "mod inner;\nmy y = 2").unwrap();
        fs::write(root.join("list").join("inner.yu"), "my z = 3").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let file_names = set
            .files
            .iter()
            .map(|file| file.path.file_name().unwrap().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(file_names, vec!["inner.yu", "mod.yu", "main.yu"]);
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();
        assert_eq!(
            module_paths,
            vec![vec!["list", "inner"], vec!["list"], Vec::<&str>::new()]
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn imported_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("operator-syntax");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nuse ops::*\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(
            parsed
                .descendants()
                .any(|node| node.kind() == SyntaxKind::InfixNode)
        );
        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn reexported_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("operator-syntax-reexport");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nmod prelude;\nuse prelude::*\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();
        fs::write(root.join("prelude.yu"), "pub use ops::*\n").unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(
            parsed
                .descendants()
                .any(|node| node.kind() == SyntaxKind::InfixNode)
        );
        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn implicit_prelude_loads_std_source_and_imports_it_into_entry() {
        let root = temp_root("implicit-prelude");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(root.join("main.yu"), "my y = id 1\n").unwrap();
        fs::write(root.join("std").join("prelude.yu"), "pub id x = x\n").unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();

        assert_eq!(
            module_paths,
            vec![vec!["std", "prelude"], Vec::<&str>::new()]
        );
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        assert!(main.source.starts_with("use std::prelude::*\n"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn implicit_prelude_operator_syntax_is_available_for_full_parse() {
        let root = temp_root("implicit-prelude-operator-syntax");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(root.join("main.yu"), "my y = 1 %% true\n").unwrap();
        fs::write(
            root.join("std").join("prelude.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> x\n",
        )
        .unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn explicit_std_import_loads_std_module_source() {
        let root = temp_root("explicit-std-import");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("std")).unwrap();
        fs::write(
            root.join("main.yu"),
            "use std::index::Index\nmy f = Index::index\n",
        )
        .unwrap();
        fs::write(
            root.join("std").join("index.yu"),
            "pub role Index 'container 'key 'value:\n  our index: 'container -> 'key -> 'value\n",
        )
        .unwrap();

        let set = collect_source_files_with_options(
            root.join("main.yu"),
            SourceOptions {
                std_root: Some(root.join("std")),
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let module_paths = set
            .files
            .iter()
            .map(|file| names(&file.module_path))
            .collect::<Vec<_>>();

        assert_eq!(module_paths, vec![vec!["std", "index"], Vec::<&str>::new()]);
        assert_eq!(set.std_files().count(), 1);
        assert_eq!(set.entry_files().count(), 1);
        assert_eq!(set.user_files().count(), 0);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn glob_without_excludes_operator_syntax_from_full_parse() {
        let root = temp_root("operator-syntax-without");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("main.yu"),
            "mod ops;\nuse ops::* without (%%)\nmy y = 1 %% true\n",
        )
        .unwrap();
        fs::write(
            root.join("ops.yu"),
            "pub infix (%%) 50 51 = \\x -> \\y -> y\n",
        )
        .unwrap();

        let set = collect_source_files(root.join("main.yu")).unwrap();
        let main = set
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops(&main.source, main.op_table.clone()),
        );

        assert!(!parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compilation_units_keep_file_sccs_and_operator_exports() {
        let set = collect_inline_source_files_with_options(
            "use a::*\n1 %% 2\n",
            [
                InlineSource {
                    path: PathBuf::from("<a>.yu"),
                    module_path: module_path(&["a"]),
                    origin: SourceOrigin::User,
                    source: "use b::*\npub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                    meta: None,
                },
                InlineSource {
                    path: PathBuf::from("<b>.yu"),
                    module_path: module_path(&["b"]),
                    origin: SourceOrigin::User,
                    source: "use a::*\npub prefix(not) 8.0.0 = \\x -> x\n".to_string(),
                    meta: None,
                },
            ],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let units = set.compilation_units();
        let cyclic_unit = units
            .units
            .iter()
            .find(|unit| unit.files.len() == 2)
            .expect("a/b should form one SCC");
        let unit_modules = cyclic_unit
            .files
            .iter()
            .map(|&idx| names(&set.files[idx].module_path))
            .collect::<Vec<_>>();
        assert!(unit_modules.contains(&vec!["a"]));
        assert!(unit_modules.contains(&vec!["b"]));
        assert!(
            cyclic_unit
                .syntax_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );
        assert!(
            cyclic_unit
                .syntax_exports
                .iter()
                .any(|export| export.name == Name("not".to_string()))
        );
    }

    #[test]
    fn compiled_syntax_artifact_preserves_operator_exports_and_reexports() {
        let set = collect_inline_source_files_with_options(
            "use prelude::*\n1 %% 2\n",
            [
                InlineSource {
                    path: PathBuf::from("<ops>.yu"),
                    module_path: module_path(&["ops"]),
                    origin: SourceOrigin::User,
                    source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                    meta: None,
                },
                InlineSource {
                    path: PathBuf::from("<prelude>.yu"),
                    module_path: module_path(&["prelude"]),
                    origin: SourceOrigin::User,
                    source: "pub use ops::*\n".to_string(),
                    meta: None,
                },
            ],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );

        let artifacts = set.compiled_unit_syntax_artifacts();
        let ops_artifact = artifacts
            .iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops unit should exist");
        assert!(
            ops_artifact
                .syntax
                .direct_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );

        let prelude_artifact = artifacts
            .iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["prelude"])
            })
            .expect("prelude unit should exist");
        assert!(
            prelude_artifact
                .syntax
                .public_exports
                .iter()
                .any(|export| export.name == Name("%%".to_string()))
        );
    }

    #[test]
    fn compiled_syntax_artifact_rebuilds_operator_table_for_parse() {
        let set = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let artifact = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops artifact should exist");
        let mut table = standard_op_table();
        for export in &artifact.syntax.public_exports {
            insert_table_op_def(&mut table.0, export.name.clone(), export.op.to_op_def());
        }
        let parsed = SyntaxNode::<YulangLanguage>::new_root(
            yulang_parser::parse_module_to_green_with_ops("my y = 1 %% 2\n", table),
        );

        assert!(parsed.descendants_with_tokens().any(|item| {
            matches!(
                item,
                NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Infix && tok.text() == "%%"
            )
        }));
    }

    #[test]
    fn compiled_syntax_artifact_round_trips_through_json() {
        let set = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let artifact = set
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .expect("ops artifact should exist");

        let encoded = serde_json::to_string(&artifact).unwrap();
        let decoded: CompiledUnitSyntaxArtifact = serde_json::from_str(&encoded).unwrap();

        assert_eq!(decoded, artifact);
    }

    #[test]
    fn compiled_syntax_artifact_hash_changes_when_operator_changes() {
        let first = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 50 51 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let second = collect_inline_source_files_with_options(
            "use ops::*\n1 %% 2\n",
            [InlineSource {
                path: PathBuf::from("<ops>.yu"),
                module_path: module_path(&["ops"]),
                origin: SourceOrigin::User,
                source: "pub infix (%%) 60 61 = \\x -> \\y -> x\n".to_string(),
                meta: None,
            }],
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        );
        let first_artifact = first
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .unwrap();
        let second_artifact = second
            .compiled_unit_syntax_artifacts()
            .into_iter()
            .find(|artifact| {
                artifact
                    .manifest
                    .files
                    .iter()
                    .any(|file| names(&file.module_path) == vec!["ops"])
            })
            .unwrap();

        assert_ne!(
            first_artifact.manifest.source_hash,
            second_artifact.manifest.source_hash
        );
        assert_ne!(
            first_artifact.manifest.syntax_hash,
            second_artifact.manifest.syntax_hash
        );
    }
}
