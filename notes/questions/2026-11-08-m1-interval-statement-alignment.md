# M1 の全体 statement と、承認済み区間規則の対応 (2026-11-08)

状態: **承認済み(2026-11-08, ユーザー): 選択肢 1 を採用する。** 以下の「承認の範囲」を読むこと。

## 承認の範囲(ユーザーの決定, 2026-11-08)

- **採用**: 旧定理(点モデル)はそのまま保存し、現在の規則(区間・遅延・宣言別 variance)を明示した**別の全体 statement を、B4 と B5/B1 の E1 の対象にする**。
  B4: 有限の実宣言・caller-visible 集合・共有 constraint graph・通常/関連型の上下境界・kind/level metadata を全称量化し、出力に pending/selected/ambiguous/rejected、実際に生成した全 where 子と ordinary 制約、完成した有限辞書を含める。lower head の未確定は正当な pending。未実装 branch を pending とすることは認めない。
  B5/B1: 実宣言から得る方向・kind・arity と、不変 slot の中心なし区間を明示し、全構文・全元 slot と unrestricted family 回収を維持する。
- **この statement の下の E1 は、元の B4・B5/B1 の完了として数える**(旧点モデルの statement の E1/E2 は数えない)。追加の support、fuel、成功、未証明の residual 条件を一般定理の前提に移さない。
- **決めていないこと(従来どおり、局所の補題か場合分けで進め、決めずに待たない)**: 「無限に入れ子」の正確な定義、non-variable payload の捕捉、拒否と曖昧性の優先順位、保留境界の適用範囲、B2 の二問。
- 終わり方は契約の最後の追記のとおり: **E2(反例)は終わりではない**。反例が出たら、定義を設計し直して、その定義の上で証明まで進む。

(以下は Pro が書いた提案の原文。)

状態(原文): 提案。全体 statement の変更は未承認。作業は局所補題で継続し、回答を待って停止しない。
出典: `2026-11-08-chatgpt-prompt-m1-interval-continuation.md` の作業 0・B4・B5、同日のモデル忠実性監査。

## 問い

**B4 と B5/B1 の E1 を判定する全体 statement を、既に承認された区間・遅延・宣言別 variance を直接表す形に更新するか。**
言語の規則を追加する問いではなく、旧点モデルの theorem と現仕様の theorem を区別するための契約の問いである。

```yulang
struct box 'a { value: 'a }       // 宣言時に共変
type list 'a                    // 不変な引数の例

impl R {x: int, ..'a}:
    where 'a: R
```

この最後の head に具体的な `{x: int, y: str}` が到達したとき、`'a` は残りの `{y: str}` から決まる。
head と要求同値になる任意の型を `'a` に選ぶ算法ではない。未解決の tail は保留する。
同様に、共変 `box` の引数比較を、全 nominal 引数についての相互部分型付けと同一視しない。
例は意味規則を示す断片であり、現 parser/runtime での実行結果を主張しない。

## 選択肢

1. **推奨: 旧定理はそのまま保存し、現在の規則を明示した別の全体 statement を E1 の対象にする。**
   B4 は有限の実宣言・caller-visible 集合・共有 constraint graph・通常/関連型の上下境界・kind/level metadata を全称量化する。
   出力には pending/selected/ambiguous/rejected、実際に生成した全 where 子と ordinary 制約、完成した有限辞書を含める。
   lower head の未確定は正当な pending とする。未実装 branch を pending とすることは認めない。
   実生成した fresh slot への割当ては意味上の exactness のために量化するが、任意の点代入存在を候補発見の定義にしない。
   B5/B1 は実宣言から得る方向・kind・arity と、不変 slot の中心なし区間を明示し、全構文・全元 slot と unrestricted family 回収を維持する。
   追加の support、fuel、成功、未証明の residual 条件を一般定理の前提に移さない。
2. **旧全体 statement をそのまま維持し、新モデルへの保存拡張定理を必須にする。**
   ただし旧側が「全 nominal は不変」「role の head を任意の点代入で照合する」と定義している範囲では、現仕様との無条件同値は期待できない。
   その場合、どの全体 statement を E1/E2 の対象とするか、モデル忠実性との整合を先に決める必要がある。

## 今回の扱い

選択肢 1 を採用済みとはしない。局所の宣言別 inspector、区間生成、正準残余、field scheme、coverage を別名で証明する。
新しい局所前提のある結果や部分言語を、元の B1〜B5 の E1/E2 と呼ばない。
既存の「無限に入れ子」の定義、non-variable payload の捕捉、拒否と曖昧性の優先順位、保留境界の適用範囲、B2 二問はこの問いで決めない。
