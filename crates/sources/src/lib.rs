//! 新ソース収集層。ファイル別 op テーブルを正しく組んでフルパースするのが目的。
//! まずは先読み（`parse_header_to_green` → CST から use/op を抽出）から積む。

use rowan::{GreenNode, NodeOrToken, SyntaxNode};
use std::collections::HashMap;
use yulang_parser::lex::SyntaxKind;
use yulang_parser::op::{standard_op_table, BpVec, OpDef, OpTable};
use yulang_parser::sink::YulangLanguage;

// ── 基礎型（旧 typed-ir から写経。realm/band バージョンは後で足す）─────────────

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name(pub String);

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Vec<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseImport {
    /// `use a::b::c` / `use a::b as c`
    Alias { name: Name, path: Path },
    /// `use a::b::*`
    Glob { prefix: Path },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDecl {
    pub visibility: Visibility,
    pub import: UseImport,
}

/// ファイル先頭で宣言された演算子（他ファイルへの export 候補）。
#[derive(Debug, Clone)]
pub struct OpExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: OpDef,
}

/// 先読みの成果。本体パース前に取れる use と op。
#[derive(Debug, Clone, Default)]
pub struct Header {
    pub uses: Vec<UseDecl>,
    pub ops: Vec<OpExport>,
}

// ── 先読み ──────────────────────────────────────────────────────────────

/// ソースの先頭から use / op 宣言だけを読み取る。body には踏み込まない
/// （[`yulang_parser::parse_header_to_green`] が最初の定義文で停止する）。
pub fn read_header(source: &str) -> Header {
    let green = yulang_parser::parse_header_to_green(source);
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    let mut header = Header::default();
    for node in root.children() {
        match node.kind() {
            SyntaxKind::UseDecl => {
                let visibility = visibility_of(&node);
                for import in use_imports(&node) {
                    header.uses.push(UseDecl { visibility, import });
                }
            }
            SyntaxKind::OpDef => {
                if let Some(op) = op_export(&node) {
                    header.ops.push(op);
                }
            }
            _ => {}
        }
    }
    header
}

// ── use 抽出（旧 use_decl_imports の最小版。realm/anchor/without/group は後で）──

pub fn use_imports(node: &SyntaxNode<YulangLanguage>) -> Vec<UseImport> {
    let mut path: Vec<Name> = Vec::new();
    let mut alias: Option<Name> = None;
    let mut after_as = false;
    let mut imports = Vec::new();
    for item in node.children_with_tokens() {
        // TODO: BraceGroup（`use a::{b, c}`）は後で対応する。
        let NodeOrToken::Token(tok) = item else {
            continue;
        };
        match tok.kind() {
            SyntaxKind::As => after_as = true,
            SyntaxKind::OpName if tok.text() == "*" => {
                imports.push(UseImport::Glob {
                    prefix: Path {
                        segments: std::mem::take(&mut path),
                    },
                });
                alias = None;
                after_as = false;
            }
            SyntaxKind::Ident if after_as => {
                alias = Some(Name(tok.text().to_string()));
                after_as = false;
            }
            SyntaxKind::Ident | SyntaxKind::OpName => {
                path.push(Name(tok.text().to_string()));
            }
            // Pub/Our/My/Use/Mod/ColonColon/Slash/ParenL/ParenR 等は構造トークン
            _ => {}
        }
    }
    push_alias_import(&mut imports, path, alias);
    imports
}

fn push_alias_import(imports: &mut Vec<UseImport>, path: Vec<Name>, alias: Option<Name>) {
    let Some(last) = path.last().cloned() else {
        return;
    };
    let name = alias.unwrap_or(last);
    imports.push(UseImport::Alias {
        name,
        path: Path { segments: path },
    });
}

// ── op 抽出（旧 syntax_export / op_def_from_header の写経）───────────────────

fn op_export(node: &SyntaxNode<YulangLanguage>) -> Option<OpExport> {
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
    Some(OpExport {
        visibility: visibility_of(node),
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

// ── 共通ヘルパ ──────────────────────────────────────────────────────────

/// 宣言ノード（または OpDefHeader 子）直下の visibility トークンを読む。
/// 無ければ `Our`（＝band 外からは見えない）を既定とする。
fn visibility_of(node: &SyntaxNode<YulangLanguage>) -> Visibility {
    fn direct(node: &SyntaxNode<YulangLanguage>) -> Option<Visibility> {
        node.children_with_tokens().find_map(|item| match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Pub => Some(Visibility::Pub),
                SyntaxKind::Our => Some(Visibility::Our),
                SyntaxKind::My => Some(Visibility::My),
                _ => None,
            },
            _ => None,
        })
    }
    direct(node)
        .or_else(|| {
            node.children()
                .find(|child| child.kind() == SyntaxKind::OpDefHeader)
                .and_then(|header| direct(&header))
        })
        .unwrap_or(Visibility::Our)
}

fn direct_token_text(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> Option<String> {
    node.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok) if tok.kind() == kind => Some(tok.text().to_string()),
        _ => None,
    })
}

// ── 複数ファイルの読み込み ──────────────────────────────────────────────
// 依存解決 → 実効 export op の不動点 → ファイル別初期テーブル → フルパース。
// 全段階が順序無関係（先読み独立／不動点収束／フルパース独立）＝SCC は不要。

/// 入力ファイル。`module_path` は収集層（FS を辿る上位層）が付けてくる前提。
pub struct SourceFile {
    pub module_path: Path,
    pub source: String,
}

/// 先読み・op テーブル確定・フルパースまで済んだファイル。
pub struct LoadedFile {
    pub module_path: Path,
    pub source: String,
    pub header: Header,
    /// このファイルを打つのに使った op テーブル（standard + 輸入 op）。
    pub op_table: OpTable,
    pub cst: GreenNode,
}

/// 全ファイルを読み込む。op テーブルはファイル別に正しく組む（循環 use でも OK）。
pub fn load(files: Vec<SourceFile>) -> Vec<LoadedFile> {
    let n = files.len();

    // 1. 先読み（各ファイル独立）
    let headers: Vec<Header> = files.iter().map(|f| read_header(&f.source)).collect();

    // 2. module_path → ファイル index
    let mut index: HashMap<Path, usize> = HashMap::with_capacity(n);
    for (i, f) in files.iter().enumerate() {
        index.insert(f.module_path.clone(), i);
    }

    // 3. 自前 export op（先頭の pub/our op。my はファイル内のみ）
    let mut effective: Vec<HashMap<Name, OpDef>> = headers
        .iter()
        .map(|header| {
            let mut map = HashMap::new();
            for op in &header.ops {
                if matches!(op.visibility, Visibility::Pub | Visibility::Our) {
                    merge_into(&mut map, op.name.clone(), op.op.clone());
                }
            }
            map
        })
        .collect();

    // 4. pub/our use の再エクスポート連鎖を不動点で閉包（循環でも単調収束）
    loop {
        let mut changed = false;
        for i in 0..n {
            for use_decl in &headers[i].uses {
                // my use はローカル取り込みのみで、再エクスポートしない
                if matches!(use_decl.visibility, Visibility::My) {
                    continue;
                }
                let Some(j) = resolve_use(&use_decl.import, &index) else {
                    continue;
                };
                if i == j {
                    continue;
                }
                for (name, op) in effective[j].clone() {
                    if merge_into(&mut effective[i], name, op) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // 5+6. 各ファイルの初期テーブル（standard + use 先の実効 export op）でフルパース。
    //      自前 op はフルパース中に update_op_table が順次入れるので、ここでは入れない。
    let mut loaded = Vec::with_capacity(n);
    for (i, (file, header)) in files.into_iter().zip(headers).enumerate() {
        let mut table = standard_op_table();
        for use_decl in &header.uses {
            if let Some(j) = resolve_use(&use_decl.import, &index) {
                if j == i {
                    continue;
                }
                for (name, op) in &effective[j] {
                    insert_op(&mut table, name.clone(), op.clone());
                }
            }
        }
        let cst = yulang_parser::parse_module_to_green_with_ops(&file.source, table.clone());
        loaded.push(LoadedFile {
            module_path: file.module_path,
            source: file.source,
            header,
            op_table: table,
            cst,
        });
    }
    loaded
}

/// use の指す module_path を、最長 prefix マッチでファイル index に解決する。
fn resolve_use(import: &UseImport, index: &HashMap<Path, usize>) -> Option<usize> {
    let path = match import {
        UseImport::Alias { path, .. } => path,
        UseImport::Glob { prefix } => prefix,
    };
    let mut segments = path.segments.clone();
    loop {
        if let Some(&i) = index.get(&Path {
            segments: segments.clone(),
        }) {
            return Some(i);
        }
        if segments.pop().is_none() {
            return None;
        }
    }
}

/// 実効 export op マップへの取り込み。変化があれば true（不動点の駆動用）。
/// fixity の有無で変化を判定する（rhs を優先して or-merge）。
fn merge_into(map: &mut HashMap<Name, OpDef>, name: Name, op: OpDef) -> bool {
    match map.get_mut(&name) {
        Some(existing) => {
            let before = fixity_shape(existing);
            existing.prefix = op.prefix.or(existing.prefix.take());
            existing.infix = op.infix.or(existing.infix.take());
            existing.suffix = op.suffix.or(existing.suffix.take());
            existing.nullfix = existing.nullfix || op.nullfix;
            before != fixity_shape(existing)
        }
        None => {
            map.insert(name, op);
            true
        }
    }
}

fn fixity_shape(op: &OpDef) -> (bool, bool, bool, bool) {
    (
        op.prefix.is_some(),
        op.infix.is_some(),
        op.suffix.is_some(),
        op.nullfix,
    )
}

/// op テーブルへの挿入（既存と or-merge）。旧 sources の insert_table_op_def 相当。
fn insert_op(table: &mut OpTable, name: Name, op: OpDef) {
    let key = name.0;
    let merged = table
        .0
        .get(key.as_bytes())
        .cloned()
        .map(|existing| merge_op_defs(existing, op.clone()))
        .unwrap_or(op);
    table.0.insert(key.into(), merged);
}

fn merge_op_defs(mut lhs: OpDef, rhs: OpDef) -> OpDef {
    lhs.prefix = rhs.prefix.or(lhs.prefix);
    lhs.infix = rhs.infix.or(lhs.infix);
    lhs.suffix = rhs.suffix.or(lhs.suffix);
    lhs.nullfix = lhs.nullfix || rhs.nullfix;
    lhs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_leading_uses_and_ops() {
        let source = "use std::prelude::*\nuse a::b as c\ninfix (<+>) 50 50 = foo\nmy main = 1\n";
        let header = read_header(source);

        // use: glob と alias を1つずつ
        assert_eq!(header.uses.len(), 2, "uses: {:?}", header.uses);
        assert!(
            matches!(
                &header.uses[0].import,
                UseImport::Glob { prefix }
                    if prefix.segments == vec![Name("std".into()), Name("prelude".into())]
            ),
            "first use: {:?}",
            header.uses[0]
        );
        assert!(
            matches!(
                &header.uses[1].import,
                UseImport::Alias { name, path }
                    if name == &Name("c".into())
                        && path.segments == vec![Name("a".into()), Name("b".into())]
            ),
            "second use: {:?}",
            header.uses[1]
        );

        // op: <+> を1つ、infix として
        assert_eq!(header.ops.len(), 1, "ops: {:?}", header.ops);
        assert_eq!(header.ops[0].name, Name("<+>".into()));
        assert!(header.ops[0].op.infix.is_some());
    }

    fn path(segments: &[&str]) -> Path {
        Path {
            segments: segments.iter().map(|s| Name(s.to_string())).collect(),
        }
    }

    #[test]
    fn imported_ops_reach_dependent_file() {
        let files = vec![
            SourceFile {
                module_path: path(&["a"]),
                source: "pub infix (<+>) 50 50 = foo\nmy x = 1\n".into(),
            },
            SourceFile {
                module_path: path(&["b"]),
                source: "use a\nmy y = 1\n".into(),
            },
        ];
        let loaded = load(files);
        assert!(
            loaded[1].op_table.0.get("<+>".as_bytes()).is_some(),
            "b should see a's exported op"
        );
    }

    #[test]
    fn cyclic_use_resolves_ops_both_ways() {
        let files = vec![
            SourceFile {
                module_path: path(&["a"]),
                source: "use b\npub infix (<a>) 50 50 = foo\n".into(),
            },
            SourceFile {
                module_path: path(&["b"]),
                source: "use a\npub infix (<b>) 50 50 = bar\n".into(),
            },
        ];
        let loaded = load(files);
        assert!(
            loaded[0].op_table.0.get("<b>".as_bytes()).is_some(),
            "a should see b's op across the cycle"
        );
        assert!(
            loaded[1].op_table.0.get("<a>".as_bytes()).is_some(),
            "b should see a's op across the cycle"
        );
    }
}
