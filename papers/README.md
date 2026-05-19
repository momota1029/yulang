# Yulang CPS 最適化向け論文コレクション

ChatGPT Pro が yulang の native backend（`runtime IR → effect-aware CPS IR → CPS optimization → Cranelift codegen`）に対して推薦した文献リスト。`pdf/` に PDF、`md/` に marker による markdown 変換結果。

## 文献一覧

| 優先 | 著者 | タイトル | 年 | yulang での使い道 |
|---:|---|---|---:|---|
| 1 | Flanagan, Sabry, Duba, Felleisen | The Essence of Compiling with Continuations | 1993 | administrative continuation の削減、ANF との対応、CPS simplifier 設計。`return / continue / force` chain 除去に直撃 |
| 2 | Andrew W. Appel | *Compiling with Continuations*（書籍） | 1992 | CPS を IR として扱う基本設計の古典。**書籍のため未収録** |
| 3 | Andrew Kennedy | Compiling with Continuations, Continued | 2007 | primitive wrapper reification、known callee 化、partial application closure の戻し最適化 |
| 4a | Richard Kelsey | A Correspondence between CPS and SSA Form | 1995 | direct-style / SSA island extraction、Cranelift block parameter lowering の理論基盤 |
| 4b | Andrew W. Appel | SSA is Functional Programming | 1998 | 同上。`CpsContinuation` を block に潰す条件の整理 |
| 5 | Bruggeman, Waddell, Dybvig | Representing Control in the Presence of One-Shot Continuations | 1996 | `CpsShotKind::{OneShot, MultiShot}` を最適化条件に使うときの境界設計 |
| 6 | Plotkin, Pretnar | Handling Algebraic Effects | 2013 | handler の意味論の土台。yulang の effect handler / nondeterminism / state / I/O / time の整理 |
| 7 | Daan Leijen | Koka: Programming with Row Polymorphic Effect Types | 2014 | effect rows / hidden evidence / handler frame elimination |
| 8 | Sivaramakrishnan et al. | Retrofitting Effect Handlers onto OCaml | 2021 | effect handler を実装として速くする話。runtime/ABI 設計の参考 |
| 9 | Kiselyov, Sivaramakrishnan | Eff Directly in OCaml | 2018 | multi-prompt delimited control、higher-order/dynamic effects、polymorphism |
| 10 | van den Berg, Schrijvers | A Framework for Higher-Order Effects & Handlers | 2023 | scoped effects / latent effects / bracketing。thunk boundary、handler scope、loop/control effects |

## 実装パスへの落とし込み（推奨順）

1. **CPS simplifier の土台** — reachability / liveness / use-count / value kind / ABI lane / purity summary、bounded fixpoint + trace
2. **administrative continuation 除去** — 主に Flanagan
3. **continuation parameter trimming** — IR hygiene。後続 inline / island extraction の前処理
4. **shot-aware inlining** — Bruggeman ベース。`OneShot` は inline 可、`MultiShot` は clone/resume の意味論破壊禁止
5. **effect evidence による handler/delimiter 削除** — Plotkin/Pretnar + Koka + Retrofitting OCaml
6. **known closure / partial application reification** — Kennedy ベース。primitive wrapper / local partial application を direct call に戻す
7. **direct-style / SSA island extraction** — Kelsey + Appel SSA。Cranelift codegen 直前のパス

## 推奨読書順

1. Flanagan et al. — Essence of Compiling with Continuations
2. Kelsey + Appel — CPS ↔ SSA
3. Bruggeman/Waddell/Dybvig — One-Shot Continuations
4. Plotkin/Pretnar — Handling Algebraic Effects
5. Leijen — Koka
6. Sivaramakrishnan et al. — Retrofitting Effect Handlers onto OCaml
7. Kiselyov — Eff Directly in OCaml
8. van den Berg/Schrijvers — Higher-Order Effects & Handlers

最初の実装 PR に直結させるなら **Flanagan + Kelsey/Appel + Bruggeman** の 3 本を軸に、handler 削除や effect evidence に入る段階で **Plotkin/Pretnar + Koka + OCaml effect handlers** を足すのが堅い。

## ソース URL

- Flanagan: <https://users.soe.ucsc.edu/~cormac/papers/pldi93.pdf>
- Kennedy: <https://www.microsoft.com/en-us/research/wp-content/uploads/2007/10/compilingwithcontinuationscontinued.pdf>
- Kelsey: <https://bernsteinbear.com/assets/img/kelsey-ssa-cps.pdf>（bernsteinbear のミラー）
- Appel SSA: <https://www.cs.princeton.edu/~appel/papers/ssafun.pdf>
- Bruggeman: <https://www.cs.tufts.edu/comp/150FP/archive/kent-dybvig/one-shot-continuations.pdf>（Tufts のミラー）
- Plotkin/Pretnar: <https://arxiv.org/abs/1312.1399>
- Leijen Koka: <https://arxiv.org/abs/1406.2061>
- Retrofitting OCaml: <https://arxiv.org/abs/2104.00250>
- Eff in OCaml: <https://arxiv.org/abs/1812.11664>
- Higher-Order Effects: <https://arxiv.org/abs/2302.01415>
