# dots T1 結果 (2026-11-08)

**T1 は部分達成。受け入れ条件の resolve_exact と外側入口を通る X13–X16 は未達。**
検証は PASS。これを T1 done / full B4 E1 と扱わない。

## 対象と公開

- 取得した base: `e65ad7b212e5da3b3f4116ab7ebecf3be568cdf4` (`integration/m1-final`)。
- コード検証 commit: `d2ebc45b7`。GitHub API の公開 commit はこれと別だが、公開後に tree を照合する。
- 公開先: `work/dots-T1` のみ。10 ファイル（新規 Lean 5、本報告、設計ノート、既存の Yulang.lean/Audit.lean/README.md への追記）。
- spec と plan と既存の定理は変更していない。lakefile 変更なし。

## 達成と未達

| 受け入れ・目標 | 結果 |
| --- | --- |
| 非単一区間で source frontier exactness と outer resolve_exact | **未達**。この名の完成定理を追加していない |
| 実 producer の全 child の accessibility | **未達**。独立した二端点 Inspect の Step については導出済み。実 producer Child との包含は未証明 |
| X13–X16 の少なくとも一つが外側入口を通る | **未達**。X15/X16 は局所 normalizer のみ。PROVED 状態へ変更しない |
| 同頭 constructor を内側へ無制限深さで持ち上げる | 構文上の正規化と独立判断の iff、両端復元を証明 |
| 異頭を区間として保持 | 局所正規化で証明 |
| 開区間の生成制約を消さない修正 | 2 fresh slots で exactness、固定更新列を保持する accumulator と実 ordinary solver の iff を証明 |
| verify-lean.sh | **PASS、exit 0、1125 jobs** |

## 設計と反例からの修正

設計は大きな Lean を書く前に `notes/design/2026-11-08-dots-T1-open-intervals.md` に記した。
Astra の settled fragment は両端が同じ fresh slot なので、全 self/cross 制約が反射律となり、古い状態をそのまま子へ渡せる。
この証明を二つの fresh slot にコピーしてはいけない。`int <: str` になる開いた capture は不整合で、元の空状態は整合している。
`open_capture_not_noop` がその具体反例を Lean で証明する。

反例だけで止まらず、修正版 `OpenState.add/recollect/solve` を実装した。
この accumulator は全 original atom と全生成 atom を同じ assignment の下に保持し、その同時整合性を実 family solver と iff で結んでいる。
ただし更新列は事前入力。更新後に各兄弟を再生成し、親 frontier を再計算する driver ではない。
従って **一般の where_state_recollection を解決したとは言えない**。

## 追加定理の日本語の主張（前提・量化を省かない）

以下の `State n` は n 個の元 slot の atom 列に、既存 solver の child/width/row grammar 条件を持つ。
`Ty` は Astra の有限 unary spine・未解決・原子的/nominal・regular leaf の構文であり、任意の Yulang 型全体ではない。
完全な Lean 型は末尾に全 31 公開定理分を付す。

### CommonRoleOpenConstraints

- `bounds_slots` / `bounds_present`: 任意の n・名前列・名前・endpoint slot 対について、実 capture list に現れる対は (0,1)。名前が元列にあればその対は実 bounds に現れる。
- `compatible_exact`: 任意の n、名前列、n+2 個の Common value/row assignment に対し、実生成器の Compatible は「名前列が空、または slot 0 の型 <: slot 1 の型」と同値。
- `generated_state_exact`: 任意の n、State n、名前列、元 assignment、二つの Common value/row payload に対し、2 fresh slots で拡張した assignment が original+generated atoms を満たす iff、元 assignment が元 atoms を満たし、名前列が空または lower.ty <: upper.ty。端点の同一性を仮定しない。
- `merged_binding_exact`: 任意の n、名前列とその中の任意の名前、元 assignment、任意の Common 型 lower/upper/actual に対し、実 occurrence list の coalesced interval に actual が入る iff lower <: actual <: upper。出現は省略しない。
- `open_capture_not_noop`: n=0 の空状態に名前0の capture を実生成し lower=int、upper=str を与えた具体 assignment は満たさない。元の空状態と同値ではない。

### CommonRoleOpenDescent

- `checked_child_decreases`: 任意の実 Declaration d、d.check=true の証明、元の requirements の任意の要素 r、任意の lower/upper と両 payload、および d.head が各 endpoint を Inspect して各 payload を得る二つの導出に対し、r の両 endpoint への代入後サイズ和は親のサイズ和より真に小さい。
- `step_decreases`: 任意の宣言列と全要素の実 check=true の証明、任意の child/parent、独立 Step 導出に対し、weight child < weight parent。
- `accessible`: 同じ checked 宣言列の任意の Request に対し Acc Step。成功証明・fuel・role rank は入力しない。ただし Step 自体に実 Inspect が二つある。一般候補伝播の全 child を覆うとはまだ示していない。

### CommonRoleOpenState

- `add_exact`: 任意の State n、任意の同じ n slot 上の bindings、任意の assignment に対し、更新後 atoms の充足 iff 元 atoms の充足とその bindings の Compatible。
- `recollect_sound` / `recollect_complete` / `recollect_exact`: 任意の State n、任意の有限 bindings 更新列、任意の最終 atom 列について、accumulator の返す列との等号 iff 独立 Recollect 導出。独立判断は primitive add を使うが recollect を呼ばない。
- `recollect_models`: 同じ任意の入力と assignment について、結果の充足 iff 元 atoms と全更新の Compatible が同じ assignment で成立。
- `recollect_atoms`: 任意の State n と更新列について、結果 atoms は元 atoms ++ 全 update の generate を順に連結した列に等しい。
- `recollect_preserves_prefix`: 任意の State n、二つの更新列 before/after、assignment に対し、before++after の結果を満たせば before の結果も満たす。
- `solve_all_instances_exact`: 任意の State n、更新列、assignment に対し、元 atoms と全更新の Compatible の同時充足 iff 実 solve が返す scheme とその row/型 parameters が存在し、instantiate がその assignment と AssignmentEquivalent。ここでの存在は実 solver の返す family の意味であり、head の点代入探索ではない。
- `solve_empty_exact`: 任意の State n と更新列について、実 solve の返す family が空 iff 元 atoms と全更新を同時に満たす assignment が存在しない。

### CommonRoleOpenNormalization

- `normalize_same`: 任意の constructor c と endpoint lo/up に対し、両端の c を外へ出して中を再帰正規化する。
- `normalize_different`: 任意の異なる c/d と endpoint lo/up に対し、異頭の endpoint 対は区間のまま。
- `normalize_interval`: 任意の lo/up で SameWrap が成立しないなら区間のまま。
- `normalize_sound` / `normalize_complete` / `normalize_exact`: 任意の lo/up と候補 Normal result について、実 normalize の結果との等号 iff 独立 Normalizes 導出。
- `endpoints_preserved`: 任意の Normalizes lo up result 導出に対し、result の下界/上界の復元は元 lo/up と等しい。
- `normalize_lower` / `normalize_upper`: 任意の lo/up で、実 normalize 後も各端点が復元される。
- `normalize_prefix`: 任意の有限 constructor 列と任意の lo/up に対し、共通 prefix 全体を外へ出した正規化と等しい。固定の深さ上限なし。

これは constructor lifting のみで、同じ atomic endpoint の点への collapse はまだない。完全 canonicalizer ではない。

### CommonRoleOpenExamples

- `x15_local`: 任意の A/B で list(box A), list(box B) の正規化は list(box(normalize A B))。
- `x16_local`: 任意の A/B で list(box A), list(list B) の正規化は list の下に異頭 endpoint pair を保つ。
- `unequal_endpoint_example`: box int と box(named 2) は構文的に異なる。この具体対の意味的整合性は主張していない。

## 正確に残る橋

1. 元の source/graph slot から、本当の lower/upper と捕捉位置ごとの bindings を回収する producer。今回 slots は同一 payload pair の繰り返しだけ。
2. 同頭 exact-match だけではなく、候補が区間を狭める通常伝播を含む Local/frontier exactness。例えば (int,top) と head int を片端 exact-match の不一致で捨てないこと。
3. 生成された各子の更新を次の兄弟へ渡して再生成し、必要な親 frontier を再収集する動的 driver。今回の固定更新列の accumulator とは別。
4. その実 producer の Child が停止尺度に従う証明。今回 Step の accessibility だけでは足りない。
5. 上記を外側 resolve に接続し、X13–X16 をその入口で証明。正規化・制約・下降の部品の足し算を全体の完了にしない。

新しい意味論の選択はしていない。質問ノートは作っていない。上記は設計者の回答を待つ理由ではなく、残る証明・実装の課題。

## 実行と中断・制限

- fresh clone、Lean v4.35.0（既存 elan 環境を再利用）。
- 初回 baseline verify と focused build を誤って同時起動した。baseline は ProducerCanonicalOpen.olean の `no such file or directory (error code: 2)` で失敗し、続く Audit/gate も失敗。既存ソースを変更せず、以後直列で再実行した。並行 build の一時ファイル競合と整合するが、OS レベルの根本原因を別途調査したわけではない。
- 中間の直列 verify は build 1120 jobs と Audit/gate は通過したが、新規 module の import 登録前なので新規未import検査で FAIL。この時点を最終 PASS として使っていない。
- focused: `cd lean && lake build Yulang.CommonRoleOpenConstraints Yulang.CommonRoleOpenDescent Yulang.CommonRoleOpenState` PASS (268 jobs)、State追記後267 jobs、Normalization265 jobs、Examples269 jobs。
- Normalization の初回は ELAN_HOME 未指定で既存環境を見つけられず失敗、設定して再実行。通常の Lean 証明エラー修正後に通過。
- 全最終コードを import、主要定理を Audit 登録してから最終 verify を直列実行。
- セッション消失、時間切れ、環境再作成なし。使用量の計上先・消費量・最大実行時間は不明。
- read-only の独立レビューで明白な偽の弱化・循環は見つからず、固定更新列・Step の限定・source provenance 未証明を報告へ反映。レビュー側は独立 kernel build を行っていない。

## 最終検証全文

コマンド: `bash tools/verify-lean.sh . origin/integration/m1-final`

```text
verify-lean: . @ d2ebc45b7 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1125 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6026 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 81677 declarations
verify-lean: PASS
```

終了コード: 0。所要 40 秒（差分ビルド）。
開始: 2026-11-08T07:23:33Z。終了: 2026-11-08T07:24:13Z。

## 定理の完全な型

`lake env lean --trust=0` で全公開定理の `#check @...` を実行し終了コード 0。

```text
@Yulang.CommonRoleOpenConstraints.bounds_slots : ∀ {n : Nat} (names : List.{0} Nat) (name : Nat)
  (pair :
    Prod.{0, 0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))),
  @Membership.mem.{0, 0}
      (Prod.{0, 0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (List.{0}
        (Prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@List.instMembership.{0}
        (Prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Yulang.CommonRoleCandidateConstraints.bounds
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Yulang.CommonRoleOpenConstraints.slots n names) name)
      pair →
    @Eq.{1}
      (Prod.{0, 0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      pair
      (@Prod.mk.{0, 0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (nat_lit 0)
          (@Fin.instOfNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            ⋯ (nat_lit 0)))
        (@OfNat.ofNat.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (nat_lit 1)
          (@Fin.instOfNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            ⋯ (nat_lit 1))))
@Yulang.CommonRoleOpenConstraints.bounds_present : ∀ {n : Nat} (names : List.{0} Nat) (name : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) names name →
    @Membership.mem.{0, 0}
      (Prod.{0, 0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (List.{0}
        (Prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@List.instMembership.{0}
        (Prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Yulang.CommonRoleCandidateConstraints.bounds
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Yulang.CommonRoleOpenConstraints.slots n names) name)
      (@Prod.mk.{0, 0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (nat_lit 0)
          (@Fin.instOfNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            ⋯ (nat_lit 0)))
        (@OfNat.ofNat.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (nat_lit 1)
          (@Fin.instOfNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            ⋯ (nat_lit 1))))
@Yulang.CommonRoleOpenConstraints.compatible_exact : ∀ {n : Nat} (names : List.{0} Nat)
  (assignment :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Iff
    (@Yulang.CommonRoleCandidateConstraints.Compatible
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Yulang.CommonRoleOpenConstraints.slots n names) assignment)
    (Or (@Eq.{1} (List.{0} Nat) names (@List.nil.{0} Nat))
      (Yulang.Common.Subtype
        (@Prod.fst.{0, 0} Yulang.Common.model.Ty Yulang.Common.model.Row
          (assignment
            (@OfNat.ofNat.{0}
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (nat_lit 0)
              (@Fin.instOfNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                ⋯ (nat_lit 0)))))
        (@Prod.fst.{0, 0} Yulang.Common.model.Ty Yulang.Common.model.Row
          (assignment
            (@OfNat.ofNat.{0}
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (nat_lit 1)
              (@Fin.instOfNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                ⋯ (nat_lit 1)))))))
@Yulang.CommonRoleOpenConstraints.generated_state_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (names : List.{0} Nat) (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model)
  (lower upper : Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Iff
    (@Yulang.PresenceNormalForm.All.{0, 0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      Yulang.Common.model (@Yulang.CommonRoleOpenConstraints.extend n lower upper assignment)
      (@HAppend.hAppend.{0, 0, 0}
        (List.{0}
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (List.{0}
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (List.{0}
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@instHAppendOfAppend.{0}
          (List.{0}
            (Yulang.PresenceNormalForm.Atom
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@List.instAppend.{0}
            (Yulang.PresenceNormalForm.Atom
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
        (@List.map.{0, 0} (Yulang.PresenceNormalForm.Atom (Fin n))
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Yulang.PresenceNormalForm.Atom.rename (Fin n)
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Yulang.CommonRoleOpenConstraints.shift n))
          (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
        (@Yulang.CommonRoleCandidateConstraints.generate
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Yulang.CommonRoleOpenConstraints.slots n names))))
    (And
      (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
        (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
      (Or (@Eq.{1} (List.{0} Nat) names (@List.nil.{0} Nat))
        (Yulang.Common.Subtype (@Prod.fst.{0, 0} Yulang.Common.model.Ty Yulang.Common.model.Row lower)
          (@Prod.fst.{0, 0} Yulang.Common.model.Ty Yulang.Common.model.Row upper))))
@Yulang.CommonRoleOpenConstraints.merged_binding_exact : ∀ {n : Nat} (names : List.{0} Nat) (name : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) names name →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model)
      (lower upper actual : Yulang.Common.Ty),
      Iff
        (Yulang.CommonRoleIntervals.Fits
          (@Yulang.CommonRoleIntervalGeneration.meaning
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Yulang.CommonRoleOpenConstraints.extend n
              (Yulang.Core.PresenceGeneration.Comp.pure.{0, 0} Yulang.Common.model lower)
              (Yulang.Core.PresenceGeneration.Comp.pure.{0, 0} Yulang.Common.model upper) assignment)
            (@Yulang.CommonRoleCandidateConstraints.arguments
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Yulang.CommonRoleOpenConstraints.slots n names) name))
          actual)
        (Yulang.CommonRoleIntervals.Fits (@Prod.mk.{0, 0} Yulang.Common.Ty Yulang.Common.Ty lower upper) actual)
Yulang.CommonRoleOpenConstraints.open_capture_not_noop : Not
  (@Yulang.PresenceNormalForm.All.{0, 0}
    (Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    Yulang.Common.model
    (@Yulang.CommonRoleOpenConstraints.extend (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Yulang.Core.PresenceGeneration.Comp.pure.{0, 0} Yulang.Common.model
        (@Yulang.CommonSyntax.Layer.base.{0, 0} Yulang.Common.Row (Yulang.CommonSyntax.State.{0} Yulang.Common.Row)
          Yulang.Inference.Base.int))
      (Yulang.Core.PresenceGeneration.Comp.pure.{0, 0} Yulang.Common.model
        (@Yulang.CommonSyntax.Layer.base.{0, 0} Yulang.Common.Row (Yulang.CommonSyntax.State.{0} Yulang.Common.Row)
          Yulang.Inference.Base.str))
      fun i => @Fin.elim0.{1} (Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model) i)
    (@HAppend.hAppend.{0, 0, 0}
      (List.{0}
        (Yulang.PresenceNormalForm.Atom
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (List.{0}
        (Yulang.PresenceNormalForm.Atom
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (List.{0}
        (Yulang.PresenceNormalForm.Atom
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@instHAppendOfAppend.{0}
        (List.{0}
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@List.instAppend.{0}
          (Yulang.PresenceNormalForm.Atom
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
      (@List.map.{0, 0}
        (Yulang.PresenceNormalForm.Atom (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (Yulang.PresenceNormalForm.Atom
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@Yulang.PresenceNormalForm.Atom.rename (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Yulang.CommonRoleOpenConstraints.shift (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Yulang.CommonRoleSettledConstraints.State.atoms (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Yulang.CommonRoleSettledConstraints.State.empty
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Yulang.CommonRoleCandidateConstraints.generate
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Yulang.CommonRoleOpenConstraints.slots (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil.{0} Nat))))))
Yulang.CommonRoleOpenDescent.checked_child_decreases : ∀ (d : Yulang.CommonRoleSettledSyntax.Declaration),
  @Eq.{1} Bool d.check true →
    ∀ (r : Prod.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template),
      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template)
          (List.{0} (Prod.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template))
          (@List.instMembership.{0} (Prod.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template)) d.requirements r →
        ∀ (lower upper lowerPayload upperPayload : Yulang.CommonRoleSettledSyntax.Ty),
          Yulang.CommonRoleSettledSyntax.Inspect d.head lower
              (Yulang.CommonRoleSettledSyntax.Observation.hit lowerPayload) →
            Yulang.CommonRoleSettledSyntax.Inspect d.head upper
                (Yulang.CommonRoleSettledSyntax.Observation.hit upperPayload) →
              @LT.lt.{0} Nat instLTNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Yulang.CommonRoleSettledSyntax.Template.instantiate lowerPayload
                      (@Prod.snd.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template r)).weight
                  (Yulang.CommonRoleSettledSyntax.Template.instantiate upperPayload
                      (@Prod.snd.{0, 0} Nat Yulang.CommonRoleSettledSyntax.Template r)).weight)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) lower.weight upper.weight)
Yulang.CommonRoleOpenDescent.step_decreases : ∀ (declarations : List.{0} Yulang.CommonRoleSettledSyntax.Declaration),
  (∀ (d : Yulang.CommonRoleSettledSyntax.Declaration),
      @Membership.mem.{0, 0} Yulang.CommonRoleSettledSyntax.Declaration
          (List.{0} Yulang.CommonRoleSettledSyntax.Declaration)
          (@List.instMembership.{0} Yulang.CommonRoleSettledSyntax.Declaration) declarations d →
        @Eq.{1} Bool d.check true) →
    ∀ (child parent : Yulang.CommonRoleOpenDescent.Request),
      Yulang.CommonRoleOpenDescent.Step declarations child parent →
        @LT.lt.{0} Nat instLTNat (Yulang.CommonRoleOpenDescent.weight child)
          (Yulang.CommonRoleOpenDescent.weight parent)
Yulang.CommonRoleOpenDescent.accessible : ∀ (declarations : List.{0} Yulang.CommonRoleSettledSyntax.Declaration),
  (∀ (d : Yulang.CommonRoleSettledSyntax.Declaration),
      @Membership.mem.{0, 0} Yulang.CommonRoleSettledSyntax.Declaration
          (List.{0} Yulang.CommonRoleSettledSyntax.Declaration)
          (@List.instMembership.{0} Yulang.CommonRoleSettledSyntax.Declaration) declarations d →
        @Eq.{1} Bool d.check true) →
    ∀ (q : Yulang.CommonRoleOpenDescent.Request),
      @Acc.{1} Yulang.CommonRoleOpenDescent.Request (Yulang.CommonRoleOpenDescent.Step declarations) q
Yulang.CommonRoleOpenExamples.x15_local : ∀ (A B : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal
    (Yulang.CommonRoleOpenNormalization.normalize
      (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor A))
      (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor B)))
    (Yulang.CommonRoleOpenNormalization.Normal.wrap Yulang.CommonRoleOpenExamples.listConstructor
      (Yulang.CommonRoleOpenNormalization.Normal.wrap Yulang.CommonRoleOpenExamples.boxConstructor
        (Yulang.CommonRoleOpenNormalization.normalize A B)))
Yulang.CommonRoleOpenExamples.x16_local : ∀ (A B : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal
    (Yulang.CommonRoleOpenNormalization.normalize
      (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor A))
      (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor B)))
    (Yulang.CommonRoleOpenNormalization.Normal.wrap Yulang.CommonRoleOpenExamples.listConstructor
      (Yulang.CommonRoleOpenNormalization.Normal.interval
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor A)
        (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.listConstructor B)))
Yulang.CommonRoleOpenExamples.unequal_endpoint_example : @Ne.{1} Yulang.CommonRoleSettledSyntax.Ty
  (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor
    (Yulang.CommonRoleSettledSyntax.Ty.atom Yulang.CommonRoleSettledSyntax.Atom.int))
  (Yulang.CommonRoleSettledSyntax.Ty.wrap Yulang.CommonRoleOpenExamples.boxConstructor
    (Yulang.CommonRoleSettledSyntax.Ty.atom
      (Yulang.CommonRoleSettledSyntax.Atom.named (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
Yulang.CommonRoleOpenNormalization.normalize_same : ∀ (c : Yulang.CommonRoleSettledSyntax.Constructor)
  (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal
    (Yulang.CommonRoleOpenNormalization.normalize (Yulang.CommonRoleSettledSyntax.Ty.wrap c lo)
      (Yulang.CommonRoleSettledSyntax.Ty.wrap c up))
    (Yulang.CommonRoleOpenNormalization.Normal.wrap c (Yulang.CommonRoleOpenNormalization.normalize lo up))
Yulang.CommonRoleOpenNormalization.normalize_different : ∀ (c d : Yulang.CommonRoleSettledSyntax.Constructor)
  (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  @Ne.{1} Yulang.CommonRoleSettledSyntax.Constructor c d →
    @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal
      (Yulang.CommonRoleOpenNormalization.normalize (Yulang.CommonRoleSettledSyntax.Ty.wrap c lo)
        (Yulang.CommonRoleSettledSyntax.Ty.wrap d up))
      (Yulang.CommonRoleOpenNormalization.Normal.interval (Yulang.CommonRoleSettledSyntax.Ty.wrap c lo)
        (Yulang.CommonRoleSettledSyntax.Ty.wrap d up))
Yulang.CommonRoleOpenNormalization.normalize_interval : ∀ (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  Not (Yulang.CommonRoleOpenNormalization.SameWrap lo up) →
    @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal (Yulang.CommonRoleOpenNormalization.normalize lo up)
      (Yulang.CommonRoleOpenNormalization.Normal.interval lo up)
Yulang.CommonRoleOpenNormalization.normalize_sound : ∀ (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  Yulang.CommonRoleOpenNormalization.Normalizes lo up (Yulang.CommonRoleOpenNormalization.normalize lo up)
@Yulang.CommonRoleOpenNormalization.normalize_complete : ∀ {lo up : Yulang.CommonRoleSettledSyntax.Ty}
  {result : Yulang.CommonRoleOpenNormalization.Normal},
  Yulang.CommonRoleOpenNormalization.Normalizes lo up result →
    @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal (Yulang.CommonRoleOpenNormalization.normalize lo up) result
Yulang.CommonRoleOpenNormalization.normalize_exact : ∀ (lo up : Yulang.CommonRoleSettledSyntax.Ty)
  (result : Yulang.CommonRoleOpenNormalization.Normal),
  Iff (@Eq.{1} Yulang.CommonRoleOpenNormalization.Normal (Yulang.CommonRoleOpenNormalization.normalize lo up) result)
    (Yulang.CommonRoleOpenNormalization.Normalizes lo up result)
@Yulang.CommonRoleOpenNormalization.endpoints_preserved : ∀ {lo up : Yulang.CommonRoleSettledSyntax.Ty}
  {result : Yulang.CommonRoleOpenNormalization.Normal},
  Yulang.CommonRoleOpenNormalization.Normalizes lo up result →
    And (@Eq.{1} Yulang.CommonRoleSettledSyntax.Ty result.lower lo)
      (@Eq.{1} Yulang.CommonRoleSettledSyntax.Ty result.upper up)
Yulang.CommonRoleOpenNormalization.normalize_lower : ∀ (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleSettledSyntax.Ty (Yulang.CommonRoleOpenNormalization.normalize lo up).lower lo
Yulang.CommonRoleOpenNormalization.normalize_upper : ∀ (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleSettledSyntax.Ty (Yulang.CommonRoleOpenNormalization.normalize lo up).upper up
Yulang.CommonRoleOpenNormalization.normalize_prefix : ∀
  (constructors : List.{0} Yulang.CommonRoleSettledSyntax.Constructor) (lo up : Yulang.CommonRoleSettledSyntax.Ty),
  @Eq.{1} Yulang.CommonRoleOpenNormalization.Normal
    (Yulang.CommonRoleOpenNormalization.normalize (Yulang.CommonRoleOpenNormalization.wrapPrefix constructors lo)
      (Yulang.CommonRoleOpenNormalization.wrapPrefix constructors up))
    (Yulang.CommonRoleOpenNormalization.normalPrefix constructors (Yulang.CommonRoleOpenNormalization.normalize lo up))
@Yulang.CommonRoleOpenState.add_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (bindings : Yulang.CommonRoleCandidateConstraints.Bindings n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Iff
    (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
      (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.add n s bindings)))
    (And
      (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
        (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
      (@Yulang.CommonRoleCandidateConstraints.Compatible n bindings assignment))
@Yulang.CommonRoleOpenState.recollect_sound : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)),
  @Yulang.CommonRoleOpenState.Recollect n s updates
    (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s updates))
@Yulang.CommonRoleOpenState.recollect_complete : ∀ {n : Nat} {s : Yulang.CommonRoleSettledConstraints.State n}
  {updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)}
  {atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))},
  @Yulang.CommonRoleOpenState.Recollect n s updates atoms →
    @Eq.{1} (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
      (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s updates)) atoms
@Yulang.CommonRoleOpenState.recollect_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))),
  Iff
    (@Eq.{1} (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
      (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s updates)) atoms)
    (@Yulang.CommonRoleOpenState.Recollect n s updates atoms)
@Yulang.CommonRoleOpenState.recollect_models : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Iff
    (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
      (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s updates)))
    (And
      (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
        (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
      (∀ (bindings : Yulang.CommonRoleCandidateConstraints.Bindings n),
        @Membership.mem.{0, 0} (Yulang.CommonRoleCandidateConstraints.Bindings n)
            (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
            (@List.instMembership.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)) updates bindings →
          @Yulang.CommonRoleCandidateConstraints.Compatible n bindings assignment))
@Yulang.CommonRoleOpenState.recollect_atoms : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)),
  @Eq.{1} (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
    (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s updates))
    (@HAppend.hAppend.{0, 0, 0} (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
      (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
      (@instHAppendOfAppend.{0} (List.{0} (Yulang.PresenceNormalForm.Atom (Fin n)))
        (@List.instAppend.{0} (Yulang.PresenceNormalForm.Atom (Fin n))))
      (@Yulang.CommonRoleSettledConstraints.State.atoms n s)
      (@List.flatMap.{0, 0} (Yulang.CommonRoleCandidateConstraints.Bindings n) (Yulang.PresenceNormalForm.Atom (Fin n))
        (@Yulang.CommonRoleCandidateConstraints.generate n) updates))
@Yulang.CommonRoleOpenState.recollect_preserves_prefix : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (before after : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  @Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
      (@Yulang.CommonRoleSettledConstraints.State.atoms n
        (@Yulang.CommonRoleOpenState.recollect n s
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
            (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
            (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
            (@instHAppendOfAppend.{0} (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
              (@List.instAppend.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)))
            before after))) →
    @Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
      (@Yulang.CommonRoleSettledConstraints.State.atoms n (@Yulang.CommonRoleOpenState.recollect n s before))
@Yulang.CommonRoleOpenState.solve_all_instances_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Iff
    (And
      (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
        (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
      (∀ (bindings : Yulang.CommonRoleCandidateConstraints.Bindings n),
        @Membership.mem.{0, 0} (Yulang.CommonRoleCandidateConstraints.Bindings n)
            (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
            (@List.instMembership.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)) updates bindings →
          @Yulang.CommonRoleCandidateConstraints.Compatible n bindings assignment))
    (@Exists.{1} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n) fun scheme =>
      And
        (@Membership.mem.{0, 0} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n)
          (List.{0} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n))
          (@List.instMembership.{0} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n))
          (@Yulang.CommonRoleOpenState.solve n s updates) scheme)
        (@Exists.{1} (Fin n → Yulang.Common.Row) fun rows =>
          @Exists.{1} (@Yulang.CommonDeclaredNominalSourceFamily.Scheme.Parameters n scheme) fun parameters =>
            @Yulang.CommonDeclaredNominalSourceFamily.AssignmentEquivalent n
              (@Yulang.CommonDeclaredNominalSourceFamily.Scheme.instantiate n scheme rows parameters) assignment))
@Yulang.CommonRoleOpenState.solve_empty_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (updates : List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)),
  Iff
    (@Eq.{1} (List.{0} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n))
      (@Yulang.CommonRoleOpenState.solve n s updates)
      (@List.nil.{0} (Yulang.CommonDeclaredNominalSourceFamily.Scheme n)))
    (Not
      (@Exists.{1} (Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model) fun assignment =>
        And
          (@Yulang.PresenceNormalForm.All.{0, 0} (Fin n) Yulang.Common.model assignment
            (@Yulang.CommonRoleSettledConstraints.State.atoms n s))
          (∀ (bindings : Yulang.CommonRoleCandidateConstraints.Bindings n),
            @Membership.mem.{0, 0} (Yulang.CommonRoleCandidateConstraints.Bindings n)
                (List.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n))
                (@List.instMembership.{0} (Yulang.CommonRoleCandidateConstraints.Bindings n)) updates bindings →
              @Yulang.CommonRoleCandidateConstraints.Compatible n bindings assignment)))
```
