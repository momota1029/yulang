use std::collections::HashMap;

use crate::ids::DefId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Vec<Name>,
}

/// `pub use path::to::name` の転送先。
/// どの名前空間への再エクスポートかを示す。
#[derive(Debug, Clone)]
pub struct Reexport {
    pub path: Path,
    pub ns: Namespace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Namespace {
    Value,
    Type,
    Module,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    My,
    Our,
    Pub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OperatorFixity {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

/// 全モジュールのテーブル。
/// lowering ワンパスで積み上げていく。
#[derive(Debug, Default)]
pub struct ModuleTable {
    modules: Vec<ModuleNode>,
}

/// モジュールひとつの中身。名前空間ごとに分離している。
/// 値・型・モジュールは同じ名前で共存できる。
#[derive(Debug, Default)]
pub struct ModuleNode {
    /// 親モジュール。root は None。
    pub parent: Option<ModuleId>,
    /// 変数・関数・コンストラクタ（値名前空間）
    pub values: HashMap<Name, DefId>,
    /// 値名前空間エントリの可視性。
    pub value_visibilities: HashMap<Name, Visibility>,
    /// 演算子定義（記号名 + fixity）
    pub operator_values: HashMap<(Name, OperatorFixity), DefId>,
    /// 演算子定義の可視性。
    pub operator_visibilities: HashMap<(Name, OperatorFixity), Visibility>,
    /// struct / enum / role / act などの型名（型名前空間）
    pub types: HashMap<Name, DefId>,
    /// 型名前空間エントリの可視性。
    pub type_visibilities: HashMap<Name, Visibility>,
    /// ネストしたモジュール（モジュール名前空間）
    pub modules: HashMap<Name, ModuleId>,
    /// モジュール名前空間エントリの可視性。
    pub module_visibilities: HashMap<Name, Visibility>,
    /// pub use による再エクスポート（名前空間を含む）
    pub reexports: HashMap<Name, Reexport>,
}

impl ModuleTable {
    pub fn new_module(&mut self) -> ModuleId {
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(ModuleNode::default());
        id
    }

    pub fn node(&self, id: ModuleId) -> &ModuleNode {
        &self.modules[id.0 as usize]
    }

    pub fn node_mut(&mut self, id: ModuleId) -> &mut ModuleNode {
        &mut self.modules[id.0 as usize]
    }

    pub fn module_ids(&self) -> impl Iterator<Item = ModuleId> + '_ {
        (0..self.modules.len()).map(|idx| ModuleId(idx as u32))
    }

    pub fn insert_value(&mut self, id: ModuleId, name: Name, def: DefId) {
        self.insert_value_with_visibility(id, name, def, Visibility::Pub);
    }

    pub fn insert_value_with_visibility(
        &mut self,
        id: ModuleId,
        name: Name,
        def: DefId,
        visibility: Visibility,
    ) {
        let node = self.node_mut(id);
        node.value_visibilities.insert(name.clone(), visibility);
        node.values.insert(name, def);
    }

    pub fn insert_operator_value_with_visibility(
        &mut self,
        id: ModuleId,
        name: Name,
        fixity: OperatorFixity,
        def: DefId,
        visibility: Visibility,
    ) {
        let node = self.node_mut(id);
        node.operator_visibilities
            .insert((name.clone(), fixity), visibility);
        node.operator_values.insert((name, fixity), def);
    }

    pub fn insert_type(&mut self, id: ModuleId, name: Name, def: DefId) {
        self.insert_type_with_visibility(id, name, def, Visibility::Pub);
    }

    pub fn insert_type_with_visibility(
        &mut self,
        id: ModuleId,
        name: Name,
        def: DefId,
        visibility: Visibility,
    ) {
        let node = self.node_mut(id);
        node.type_visibilities.insert(name.clone(), visibility);
        node.types.insert(name, def);
    }

    pub fn insert_module(&mut self, id: ModuleId, name: Name, child: ModuleId) {
        self.insert_module_with_visibility(id, name, child, Visibility::Pub);
    }

    pub fn insert_module_with_visibility(
        &mut self,
        id: ModuleId,
        name: Name,
        child: ModuleId,
        visibility: Visibility,
    ) {
        self.node_mut(child).parent = Some(id);
        let node = self.node_mut(id);
        node.module_visibilities.insert(name.clone(), visibility);
        node.modules.insert(name, child);
    }

    pub fn insert_module_alias_with_visibility(
        &mut self,
        id: ModuleId,
        name: Name,
        child: ModuleId,
        visibility: Visibility,
    ) {
        let node = self.node_mut(id);
        node.module_visibilities.insert(name.clone(), visibility);
        node.modules.insert(name, child);
    }

    pub fn insert_reexport(&mut self, id: ModuleId, name: Name, reexport: Reexport) {
        self.node_mut(id).reexports.insert(name, reexport);
    }

    pub fn value_visibility(&self, id: ModuleId, name: &Name) -> Visibility {
        self.node(id)
            .value_visibilities
            .get(name)
            .copied()
            .unwrap_or(Visibility::Pub)
    }

    pub fn operator_visibility(
        &self,
        id: ModuleId,
        name: &Name,
        fixity: OperatorFixity,
    ) -> Visibility {
        self.node(id)
            .operator_visibilities
            .get(&(name.clone(), fixity))
            .copied()
            .unwrap_or(Visibility::Pub)
    }

    pub fn type_visibility(&self, id: ModuleId, name: &Name) -> Visibility {
        self.node(id)
            .type_visibilities
            .get(name)
            .copied()
            .unwrap_or(Visibility::Pub)
    }

    pub fn module_visibility(&self, id: ModuleId, name: &Name) -> Visibility {
        self.node(id)
            .module_visibilities
            .get(name)
            .copied()
            .unwrap_or(Visibility::Pub)
    }
}
