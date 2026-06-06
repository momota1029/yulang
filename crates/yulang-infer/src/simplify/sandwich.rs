//! グローバル sandwich：不変型の中心変数が「主型全体で例外なく同じ単一の具体型 K と
//! 共起」していれば中心変数を捨てる。詳細 spec/2026-06-06-invariant-type-sandwich.md。
//!
//! - K が Con/Tuple → その K を lift（区間を `Con`/`Tuple` 変種に畳む）。
//! - K が prim（int 等）→ lift 先が無いので中心変数を**主型全体から削除**するだけ（collapse）。
//!   区間 `(α&int, int|α)` から α を抜くと `(int, int)`＝int になる。`pick` の戻り α がこれ。
//! - 共起判定はスキーマ（1 def の主型）全体で行う（局所判定では `(int,int)|α&(int,int) -> α`
//!   の ret に裸 α がいるケースを誤って畳んでしまう）。**一度でも裸（具体型を伴わない単独 var）で
//!   出た中心は対象外**＝ `xs : list<int|α>`（負側が裸 α の `(α, α|int)`）は残る。
//! - lift 後の子をもう一度 sandwich（さらに潰れうるため fixpoint）。

use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;
use crate::symbols::Path;

use super::compact::{CompactBounds, CompactCon, CompactFun, CompactType, CompactTypeScheme};

/// 中心変数が共起しうる具体型の種。同種（path+arity が一致）なら同じ kind。
#[derive(Clone, PartialEq, Eq, Debug)]
enum ConKind {
    /// lift 可能な名前付きコンストラクタ。
    Con(Path, usize),
    /// lift 可能なタプル。
    Tuple(usize),
    /// lift 可能な関数型。
    Fun,
    /// プリミティブ型（int 等）。lift 先が無いので中心を削除（collapse）する。
    Prim(Path),
    /// Record/Variant/Row。今は lift も collapse もしない（裸ではない種として共起判定だけ参加）。
    NonLiftable,
}

/// 各 CompactType が表に持つ具体型の種を集める。空なら「裸（具体型なし）」。
fn type_con_kinds(ty: &CompactType) -> Vec<ConKind> {
    let mut kinds = Vec::new();
    for con in &ty.cons {
        kinds.push(ConKind::Con(con.path.clone(), con.args.len()));
    }
    for tuple in &ty.tuples {
        kinds.push(ConKind::Tuple(tuple.len()));
    }
    if !ty.funs.is_empty() {
        kinds.push(ConKind::Fun);
    }
    for prim in &ty.prims {
        kinds.push(ConKind::Prim(prim.clone()));
    }
    if !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.rows.is_empty()
    {
        kinds.push(ConKind::NonLiftable);
    }
    kinds
}

/// 中心変数 α の「共起判定」の途中状態。
#[derive(Clone)]
enum Verdict {
    /// まだ矛盾なく、この単一 kind と共起している。
    Single(ConKind),
    /// 裸出現・複数 kind・矛盾 → lift しない。
    NoLift,
}

/// sandwich の判定結果。`lift` は区間を畳む中心→Con/Tuple、`collapse` は主型全体から削除する中心。
#[derive(Default)]
struct SandwichVerdicts {
    lift: HashMap<TypeVar, ConKind>,
    collapse: HashSet<TypeVar>,
}

impl SandwichVerdicts {
    fn is_empty(&self) -> bool {
        self.lift.is_empty() && self.collapse.is_empty()
    }
}

/// 主型全体での極性。`lower`（共変・正）／`upper`（反変・負）から始まり、fun arg で反転する。
/// con 引数は不変なので極性をリセットして両極（lower=正・upper=負）を独立に拾う。
#[derive(Clone, Copy, PartialEq)]
enum Pol {
    Pos,
    Neg,
}

impl Pol {
    fn flip(self) -> Pol {
        match self {
            Pol::Pos => Pol::Neg,
            Pol::Neg => Pol::Pos,
        }
    }
}

/// 判定走査の累積。`verdicts`＝各変数の共起 kind。`pos_vars`/`neg_vars`＝**主型全体で**その変数が
/// 正（共変）／負（反変）位置に一度でも出たか。collapse は「具体 atomic 型と全共起・裸なし」かつ
/// 「pos と neg の双方に出た（＝不変の中心）」変数に限る。中心判定をスキーマ全体で行うのが要点で、
/// 単一区間の lower∩upper だけ見ると `take_fold` の累算器のように**複数区間にまたがる中心**を
/// 取りこぼす（z 引数の上界 neg と戻り値の下界 pos が別区間）。これで `pick`/`take_fold` の中心は
/// 消え、pl3 のような**共変位置のみに出る値束縛の残差 α**（neg に出ない＝中心でない）は残る。
#[derive(Default)]
struct VerdictAcc {
    verdicts: HashMap<TypeVar, Verdict>,
    pos_vars: HashSet<TypeVar>,
    neg_vars: HashSet<TypeVar>,
}

/// スキーマ全体を走査し、各型変数が「全出現で同じ単一の具体型と共起し、一度も裸で出ない」かを
/// 判定する。共起先が引数つき Con/Tuple なら lift（畳む）、atomic（nullary con / prim）かつ
/// 不変区間の中心なら collapse（主型全体から削除）に振り分ける。
fn compute_sandwich_verdicts(scheme: &CompactTypeScheme) -> SandwichVerdicts {
    let mut acc = VerdictAcc::default();
    visit_bounds_for_verdict(&scheme.cty, &mut acc);
    for bounds in scheme.rec_vars.values() {
        visit_bounds_for_verdict(bounds, &mut acc);
    }
    let VerdictAcc {
        verdicts,
        pos_vars,
        neg_vars,
    } = acc;
    // 中心 = 主型全体で正と負の双方に出た変数。
    let centers: HashSet<TypeVar> = pos_vars.intersection(&neg_vars).copied().collect();
    let mut out = SandwichVerdicts::default();
    for (tv, v) in verdicts {
        // μ束縛変数（rec_vars のキー）は触らない。lift すれば再帰型を無限展開し、collapse すれば
        // 再帰の参照先が消えて壊れる。再帰型は Interval のまま残す。
        if scheme.rec_vars.contains_key(&tv) {
            continue;
        }
        match v {
            // atomic（int 等の nullary con / prim）かつ中心 → 主型全体から削除。引数つき con は
            // lift で構造を畳む必要があるので lift 側へ（nullary は畳んでも局所的にしか中心を
            // 消せず、共変位置の同一 var が残るので collapse が正しい＝`pick` の戻り α）。
            Verdict::Single(ConKind::Con(_, 0) | ConKind::Prim(_)) if centers.contains(&tv) => {
                out.collapse.insert(tv);
            }
            Verdict::Single(kind @ (ConKind::Con(..) | ConKind::Tuple(_) | ConKind::Fun)) => {
                out.lift.insert(tv, kind);
            }
            _ => {}
        }
    }
    out
}

fn record_var_occurrence(verdicts: &mut HashMap<TypeVar, Verdict>, tv: TypeVar, kinds: &[ConKind]) {
    // この出現で α が共起する kind は、kinds がちょうど 1 種なら Single、0 種（裸）or 複数なら NoLift。
    let this = if kinds.len() == 1 {
        Verdict::Single(kinds[0].clone())
    } else {
        Verdict::NoLift
    };
    let merged = match (verdicts.get(&tv), &this) {
        (None, _) => this.clone(),
        (Some(Verdict::NoLift), _) | (_, Verdict::NoLift) => Verdict::NoLift,
        (Some(Verdict::Single(a)), Verdict::Single(b)) => {
            if a == b {
                Verdict::Single(a.clone())
            } else {
                Verdict::NoLift
            }
        }
    };
    verdicts.insert(tv, merged);
}

fn visit_type_for_verdict(ty: &CompactType, pol: Pol, acc: &mut VerdictAcc) {
    let kinds = type_con_kinds(ty);
    for &tv in &ty.vars {
        record_var_occurrence(&mut acc.verdicts, tv, &kinds);
        match pol {
            Pol::Pos => acc.pos_vars.insert(tv),
            Pol::Neg => acc.neg_vars.insert(tv),
        };
    }
    // ネストした不変位置（con args）は不変なので極性をリセットして両極を独立に拾う。
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_for_verdict(arg, acc);
        }
    }
    // tuple 成分（共変）・fun・record 等の CompactType もたどる（変数の出現と極性を拾うため）。
    for tuple in &ty.tuples {
        for item in tuple {
            visit_type_for_verdict(item, pol, acc);
        }
    }
    for fun in &ty.funs {
        // 引数は反変、戻りは共変。eff スロットも arg 側は反変・ret 側は共変に揃える
        // （effect 変数は具体型 con と共起しないので collapse 判定には実質効かない）。
        visit_type_for_verdict(&fun.arg, pol.flip(), acc);
        visit_type_for_verdict(&fun.arg_eff, pol.flip(), acc);
        visit_type_for_verdict(&fun.ret_eff, pol, acc);
        visit_type_for_verdict(&fun.ret, pol, acc);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_for_verdict(&field.value, pol, acc);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_for_verdict(&field.value, pol, acc);
        }
        visit_type_for_verdict(&spread.tail, pol, acc);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_for_verdict(payload, pol, acc);
            }
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_for_verdict(item, pol, acc);
        }
        visit_type_for_verdict(&row.tail, pol, acc);
    }
}

fn visit_bounds_for_verdict(bounds: &CompactBounds, acc: &mut VerdictAcc) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            // self_var は共変・反変の両方向に現れる中心として扱う（lower/upper と同じ kind 集合で判定）。
            if let Some(sv) = self_var {
                acc.pos_vars.insert(*sv);
                acc.neg_vars.insert(*sv);
                let lk = type_con_kinds(lower);
                let uk = type_con_kinds(upper);
                record_var_occurrence(&mut acc.verdicts, *sv, &lk);
                record_var_occurrence(&mut acc.verdicts, *sv, &uk);
            }
            // 区間の lower は正（共変）、upper は負（反変）位置。
            visit_type_for_verdict(lower, Pol::Pos, acc);
            visit_type_for_verdict(upper, Pol::Neg, acc);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_for_verdict(arg, acc);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_for_verdict(item, acc);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_for_verdict(arg, acc);
            visit_bounds_for_verdict(arg_eff, acc);
            visit_bounds_for_verdict(ret_eff, acc);
            visit_bounds_for_verdict(ret, acc);
        }
    }
}

/// スキーマに sandwich を適用する。
pub(crate) fn sandwich_scheme(scheme: &mut CompactTypeScheme) {
    // verdict は lift / collapse で構造が変わると変わりうるので fixpoint で回す。各パスで実際に
    // 何か起きたかを `changed` フラグで追い、起きなければ収束として打ち切る（scheme の clone /
    // 等価比較は巨大型で O(size) になり重いので避ける）。lift も collapse も不変中心を 1 つ消す
    // ので反復は有限だが、念のため上限も置く。
    for _ in 0..MAX_SANDWICH_PASSES {
        let verdicts = compute_sandwich_verdicts(scheme);
        if verdicts.is_empty() {
            break;
        }
        let mut changed = false;
        // collapse（prim 共起の中心）は主型全体から var を削除するだけ。lift とは対象が交わらない
        // （collapse=prim / lift=Con·Tuple）ので同じ verdict で両方適用してよい。
        if !verdicts.collapse.is_empty() {
            remove_vars_from_bounds(&mut scheme.cty, &verdicts.collapse);
            for bounds in scheme.rec_vars.values_mut() {
                remove_vars_from_bounds(bounds, &verdicts.collapse);
            }
            changed = true;
        }
        if !verdicts.lift.is_empty() {
            scheme.cty = sandwich_spine(
                std::mem::take(&mut scheme.cty),
                &verdicts.lift,
                &mut changed,
            );
            let rec_vars = std::mem::take(&mut scheme.rec_vars);
            scheme.rec_vars = rec_vars
                .into_iter()
                .map(|(tv, b)| (tv, sandwich_spine(b, &verdicts.lift, &mut changed)))
                .collect();
        }
        if !changed {
            break;
        }
    }
}

/// collapse 対象の中心変数を `bounds` 配下の全 CompactType から削除する。区間の self_var も外す。
fn remove_vars_from_bounds(bounds: &mut CompactBounds, vars: &HashSet<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if self_var.is_some_and(|sv| vars.contains(&sv)) {
                *self_var = None;
            }
            remove_vars_from_type(lower, vars);
            remove_vars_from_type(upper, vars);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                remove_vars_from_bounds(arg, vars);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                remove_vars_from_bounds(item, vars);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            remove_vars_from_bounds(arg, vars);
            remove_vars_from_bounds(arg_eff, vars);
            remove_vars_from_bounds(ret_eff, vars);
            remove_vars_from_bounds(ret, vars);
        }
    }
}

/// collapse 対象の中心変数を `ty` 配下の全 vars 集合から削除する（再帰）。
fn remove_vars_from_type(ty: &mut CompactType, vars: &HashSet<TypeVar>) {
    ty.vars.retain(|v| !vars.contains(v));
    for con in &mut ty.cons {
        for arg in &mut con.args {
            remove_vars_from_bounds(arg, vars);
        }
    }
    for fun in &mut ty.funs {
        remove_vars_from_type(&mut fun.arg, vars);
        remove_vars_from_type(&mut fun.arg_eff, vars);
        remove_vars_from_type(&mut fun.ret_eff, vars);
        remove_vars_from_type(&mut fun.ret, vars);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            remove_vars_from_type(&mut field.value, vars);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            remove_vars_from_type(&mut field.value, vars);
        }
        remove_vars_from_type(&mut spread.tail, vars);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                remove_vars_from_type(payload, vars);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            remove_vars_from_type(item, vars);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            remove_vars_from_type(item, vars);
        }
        remove_vars_from_type(&mut row.tail, vars);
    }
}

/// fixpoint の反復上限（不変中心は有限なので通常はネスト深さ分で収束する）。
const MAX_SANDWICH_PASSES: usize = 64;

/// 中心変数 `center` が `lower`/`upper` の双方で kind `K` と共起しているなら、その K を lift して
/// 中心を捨てた `CompactBounds`（lift 変種）を返す。できなければ None。
fn try_lift_interval(
    self_var: Option<TypeVar>,
    lower: &CompactType,
    upper: &CompactType,
    verdicts: &HashMap<TypeVar, ConKind>,
) -> Option<CompactBounds> {
    // 中心候補 = lower.vars ∩ upper.vars、または self_var。verdict を持つものを選ぶ。
    let center = self_var
        .filter(|tv| verdicts.contains_key(tv))
        .or_else(|| {
            lower
                .vars
                .iter()
                .find(|tv| upper.vars.contains(tv) && verdicts.contains_key(tv))
                .copied()
        })?;
    let kind = verdicts.get(&center)?.clone();
    // lower/upper の双方に同種コンストラクタがちょうど 1 つあること。
    match kind {
        ConKind::Tuple(n) => {
            let l = single_tuple(lower, n)?;
            let u = single_tuple(upper, n)?;
            let items = l
                .iter()
                .zip(u)
                .map(|(li, ui)| CompactBounds::Interval {
                    self_var: None,
                    lower: li.clone(),
                    upper: ui.clone(),
                })
                .collect();
            Some(CompactBounds::Tuple { items })
        }
        ConKind::Con(path, n) => {
            let l = single_con(lower, &path, n)?;
            let u = single_con(upper, &path, n)?;
            // con args は既に CompactBounds（不変区間）。lower 側 con と upper 側 con の対応引数を
            // 区間として組む：covariant の引数は lower の lower/upper をそのまま、という単純化は
            // できないので、各引数の (+,-) を「lower-con-arg と upper-con-arg のマージ」で作る。
            let args = l
                .iter()
                .zip(u)
                .map(|(la, ua)| merge_arg_bounds(la, ua))
                .collect();
            Some(CompactBounds::Con { path, args })
        }
        ConKind::Fun => {
            let l = single_fun(lower)?;
            let u = single_fun(upper)?;
            Some(CompactBounds::Fun {
                arg: Box::new(contravariant_fun_field_bounds(&l.arg, &u.arg)),
                arg_eff: Box::new(contravariant_fun_field_bounds(&l.arg_eff, &u.arg_eff)),
                ret_eff: Box::new(covariant_fun_field_bounds(&l.ret_eff, &u.ret_eff)),
                ret: Box::new(covariant_fun_field_bounds(&l.ret, &u.ret)),
            })
        }
        // prim は collapse 側で処理済み（lift map には Con/Tuple/Fun しか入らない）。
        ConKind::Prim(_) | ConKind::NonLiftable => None,
    }
}

/// con 引数（不変区間）を lower 側出現と upper 側出現から1つに合流する。
/// lower 側の con arg は「正の側に現れた不変引数」、upper 側は「負の側に現れた不変引数」。
/// 不変なので両者の lower どうし・upper どうしを取る（= 同じ中心の (+,-) を保つ）。
fn merge_arg_bounds(l: &CompactBounds, u: &CompactBounds) -> CompactBounds {
    match (l, u) {
        (
            CompactBounds::Interval {
                self_var: ls,
                lower: ll,
                upper: lu,
            },
            CompactBounds::Interval {
                lower: ul,
                upper: uu,
                ..
            },
        ) => CompactBounds::Interval {
            self_var: *ls,
            lower: super::compact::merge_compact_types(true, ll.clone(), ul.clone()),
            upper: super::compact::merge_compact_types(false, lu.clone(), uu.clone()),
        },
        // すでに lift 済みの引数はそのまま lower 側を採用（保守的）。
        _ => l.clone(),
    }
}

fn covariant_fun_field_bounds(lower: &CompactType, upper: &CompactType) -> CompactBounds {
    CompactBounds::Interval {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    }
}

fn contravariant_fun_field_bounds(lower: &CompactType, upper: &CompactType) -> CompactBounds {
    CompactBounds::Interval {
        self_var: None,
        lower: upper.clone(),
        upper: lower.clone(),
    }
}

fn single_tuple(ty: &CompactType, n: usize) -> Option<&Vec<CompactType>> {
    if ty.tuples.len() == 1 && ty.tuples[0].len() == n && ty.cons.is_empty() {
        Some(&ty.tuples[0])
    } else {
        None
    }
}

fn single_con<'a>(ty: &'a CompactType, path: &Path, n: usize) -> Option<&'a Vec<CompactBounds>> {
    if ty.cons.len() == 1
        && ty.cons[0].path == *path
        && ty.cons[0].args.len() == n
        && ty.tuples.is_empty()
    {
        Some(&ty.cons[0].args)
    } else {
        None
    }
}

fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
    if ty.funs.len() == 1
        && ty.cons.is_empty()
        && ty.tuples.is_empty()
        && ty.prims.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.funs[0])
    } else {
        None
    }
}

/// スパイン（root cty / rec_var の top）を sandwich する。**その interval 自体は lift しない**
/// （binding の型そのものを表す位置なので lift すると coalesce 経路が `.lower()` で壊れる）。
/// con-arg などネストした不変位置だけ `sandwich_type` 経由で lift する。
fn sandwich_spine(
    bounds: CompactBounds,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => CompactBounds::Interval {
            self_var,
            lower: sandwich_type(lower, verdicts, changed),
            upper: sandwich_type(upper, verdicts, changed),
        },
        // スパインが既に lift 済み（通常起きない）なら子へ降りるだけ。
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|a| sandwich_spine(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|a| sandwich_spine(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(sandwich_spine(*arg, verdicts, changed)),
            arg_eff: Box::new(sandwich_spine(*arg_eff, verdicts, changed)),
            ret_eff: Box::new(sandwich_spine(*ret_eff, verdicts, changed)),
            ret: Box::new(sandwich_spine(*ret, verdicts, changed)),
        },
    }
}

/// bounds を sandwich 変換する。lift できれば lift し（`changed` を立てる）、できなければネストへ再帰。
fn sandwich_bounds(
    bounds: CompactBounds,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(lifted) = try_lift_interval(self_var, &lower, &upper, verdicts) {
                *changed = true;
                sandwich_bounds(lifted, verdicts, changed)
            } else {
                CompactBounds::Interval {
                    self_var,
                    lower: sandwich_type(lower, verdicts, changed),
                    upper: sandwich_type(upper, verdicts, changed),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(sandwich_bounds(*arg, verdicts, changed)),
            arg_eff: Box::new(sandwich_bounds(*arg_eff, verdicts, changed)),
            ret_eff: Box::new(sandwich_bounds(*ret_eff, verdicts, changed)),
            ret: Box::new(sandwich_bounds(*ret, verdicts, changed)),
        },
    }
}

/// CompactType 内のネストした不変位置（con args など）を sandwich する。
fn sandwich_type(
    mut ty: CompactType,
    verdicts: &HashMap<TypeVar, ConKind>,
    changed: &mut bool,
) -> CompactType {
    ty.cons = ty
        .cons
        .into_iter()
        .map(|con| CompactCon {
            path: con.path,
            args: con
                .args
                .into_iter()
                .map(|a| sandwich_bounds(a, verdicts, changed))
                .collect(),
        })
        .collect();
    for fun in &mut ty.funs {
        fun.arg = sandwich_type(std::mem::take(&mut fun.arg), verdicts, changed);
        fun.arg_eff = sandwich_type(std::mem::take(&mut fun.arg_eff), verdicts, changed);
        fun.ret_eff = sandwich_type(std::mem::take(&mut fun.ret_eff), verdicts, changed);
        fun.ret = sandwich_type(std::mem::take(&mut fun.ret), verdicts, changed);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = sandwich_type(std::mem::take(&mut field.value), verdicts, changed);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = sandwich_type(std::mem::take(&mut field.value), verdicts, changed);
        }
        spread.tail = Box::new(sandwich_type(
            *std::mem::take(&mut spread.tail),
            verdicts,
            changed,
        ));
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload = sandwich_type(std::mem::take(payload), verdicts, changed);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            *item = sandwich_type(std::mem::take(item), verdicts, changed);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            *item = sandwich_type(std::mem::take(item), verdicts, changed);
        }
        row.tail = Box::new(sandwich_type(
            *std::mem::take(&mut row.tail),
            verdicts,
            changed,
        ));
    }
    ty
}
