# Finite associated closure with ordinary source identity

状態: Draft。2026-11-10、cycle76。I-13の入力監査から得た有限断片の接続。

## 部分目標と境界

既存の `CommonRoleFiniteAssociatedClosure.Source.identity` は、既知のscalar factを
同名slotへ伝播する。未知の同名slotの任意の型値を等しくするordinary制約を
`CommonRoleFiniteAssociatedModels.run` 自体が追加するわけではない。
一方、`CommonRoleNamedPath.run` は先に `CommonRoleSourceIdentity.extend` を呼ぶ。
この差を埋め、**与えられた有限source tableとassociated occurrence列**に限り、
既存ordinary状態、source同一性、独立associated導出を一つのmodel iffへ接続する。

spec6.2の同名変数、6.3の普通の型変数と関連型等式が根拠。これは新しい意味の選択でない。
source名が実際にどのscopeを共有するかはcaller入力のままで、Q1の回答を代行しない。
finite graphは入力。parser、dynamic where生成、一般区間knownness、候補guard、
最終分類と辞書順を閉じない。B4主要5橋の数は変えない。

## データ、独立判断、実行

- `table : CommonRoleSourceIdentity.Table`、`occurrences : List (Occurrence table.length)`。
  各occurrenceはreceiver/output slot、関連名、`Inference.Base → Roles.Goal` templateを持つ。
- env/roles、core `WellFormed`、declaration-only exactnessの `AssocWellFormed`。
- `s : State table.length` は任意の旧ordinary制約。成功やModelsは実行前提にしない。
- 実行は `extend table s` の後、既存有限associated saturationとemitを行う。
- 独立判断は `DeclarativeDerives`。公開結論に一つのsource型valuationを存在量化する。
  valuationはcallerが実行時に選ぶoracleでない。effect行は元の制約を保持し、
  sourceの型同一性だけからeffect行の同一性は追加しない。

## 目標の型

任意のenv、roles、wf、awf、table、occurrences、旧state s、assignment vについて:

`All v (run env roles wf table occurrences s).atoms ↔
 All v s.atoms ∧ ∃ sourceValues,
 Factors table v sourceValues ∧
 ∀ fact, DeclarativeDerives env roles (source table occurrences) (extend table s) fact →
 Equivalent (sourceValues (source table fact.slot)) (base fact.head)`。

同じ右辺についてvも存在量化すると、実ordinary solverのconsistent=trueと同値。
補助のsource_factorizationは全返却modelが同名slotを共有することを与える。
四方向のclassification、全言語主型性、source名の妥当性を結論に追加しない。

## 必要な連鎖

既存 `extend_exact` → `factorization_exact`、
`FiniteAssociatedModels.run_models_exact` → `FiniteAssociatedDeclaration.derives_exact`、
source factorを通したscalar等式の両方向輸送、実ordinary solverの`consistent_exact`。
この有限断片の接続に新しい意味論公理や新しい停止性の仮定は必要ない。

## Yulang2との照合

live `work/dots-audit` の `x-oracle.md`（55574b605）のC3-PARENTは
left/right両順とgeneric functionの実行結果(11,22)、missing-childの拒否を記録する。
これは6.3の関連型/whereの素材であって、内部source tableの同一性やこのmodel iffを
直接測るoracleではない。X13〜X16は区間の局所入力に限る。新しい実機実行はしない。
