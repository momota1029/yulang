use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path as FsPath, PathBuf};

use rowan::{NodeOrToken, SyntaxNode};
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone)]
pub struct SourceSet {
    pub files: Vec<SourceFile>,
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub op_table: OpTable,
    pub source: String,
    pub meta: SourceMeta,
}

#[derive(Debug, Clone)]
pub struct InlineSource {
    pub path: PathBuf,
    pub module_path: ModulePath,
    pub source: String,
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
            source,
            source_prefix,
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
            source,
        } = source;
        self.load_source(path, module_path, &source, "");
    }

    fn load_source(
        &mut self,
        path: PathBuf,
        module_path: ModulePath,
        source: &str,
        source_prefix: &str,
    ) {
        if !self.seen.insert(module_path.clone()) {
            return;
        }

        let mut source = source.to_string();
        if !source_prefix.is_empty() {
            source.insert_str(0, source_prefix);
        }
        let meta = parse_source_meta(&source);
        let dependencies = inline_dependencies(&module_path, &meta);
        self.files.push(SourceFile {
            path,
            module_path,
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
        self.load_module_with_prefix(path, ModulePath { segments: vec![] }, source_prefix)
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
            source_prefix,
            base_dir,
        )
    }

    fn load_module(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
    ) -> Result<(), SourceLoadError> {
        self.load_module_with_prefix(path, module_path, "")
    }

    fn load_module_with_prefix(
        &mut self,
        path: &FsPath,
        module_path: ModulePath,
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
                    .map(|path| (path, module_path))
            })
            .collect::<Vec<_>>();

        self.files.push(SourceFile {
            path: path.to_path_buf(),
            module_path,
            op_table: standard_op_table(),
            source,
            meta,
        });

        for (path, module_path) in module_paths {
            self.load_module(&path, module_path)?;
        }
        for (path, module_path) in imported_paths {
            self.load_module(&path, module_path)?;
        }
        Ok(())
    }

    fn load_virtual_module_with_prefix(
        &mut self,
        source: &str,
        module_path: ModulePath,
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
                    .map(|path| (path, module_path))
            })
            .collect::<Vec<_>>();

        self.files.push(SourceFile {
            path: synthetic_path,
            module_path,
            op_table: standard_op_table(),
            source,
            meta,
        });

        for (path, module_path) in module_paths {
            self.load_module(&path, module_path)?;
        }
        for (path, module_path) in imported_paths {
            self.load_module(&path, module_path)?;
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
    let mut public_exports = files
        .iter()
        .map(|file| local_public_syntax_exports(&file.meta))
        .collect::<Vec<_>>();

    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..files.len() {
            for use_ in &files[idx].meta.uses {
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
}
