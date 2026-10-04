# 回答案 — 未承認

Question ID: `function-effect-row-denotation`
Question revision: `q1`
Draft ID: `function-effect-row-denotation-answer`
Draft revision: `d1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `c3fe10151e6e73fda428ade0a30224cecfd8bb4b`
Task/thread locator: unavailable: この会話には安定したmessage/thread locatorが公開されていない。
Governing source/section: `notes/design/2026-10-03-concrete-compatibility-boundary.md` §§3–8およびFunction効果descriptorの既存決定; `notes/design/2026-10-02-ordinary-computation-semantics-package.md` §§2, 4–5; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §9; `notes/design/2026-10-03-callback-context-delivery.md` §§2–4; `syntax-reference/en/src/types/effect-row-type.md` §1

## ユーザーの原文と出典

2026-10-05、この回答会話での説明への返答：

> これは共変位置と反変位置で答えが変わります．
>
> ## 共変位置の場合
> 共変位置に`['e, write int]`がある場合必ず反変位置にも`'e`が含まれるので，効果の種類を許すという意味になる．
>
> ## 反変位置
> 反変位置に`['e, write int]`がある場合，`'e`が`write 'a`を含むなら矛盾がない必要があり（例えば`int <: 'a`），さらに共変位置に`'e`が現れる場合`'e`から`write int`は失われている．
>
> こんな感じの回答でしょうか．

続くshallow/deepの区別への説明：

> shallow handlerの場合は（おそらく）`'a ['e & [any, write int]] -> ['e] 'a`という主型がつきます．いま言っている型ではdeep handlerを表しています．

## 回答者の解釈

効果rowの意味は共変・反変で分ける。具体的な効果が共変側の共有変数から失われるという説明は、今回のdeep handlerを表す型についての説明である。shallow handlerの主型は留保付きの候補であり、確定した主型として扱わない。

## 決定案と範囲

1. q1にはCとして、以下の極性別の意味を回答する。Aの共変側の許容という読み方は維持するが、反変側とdeep/shallowの区別は以下の説明で具体化する。
2. 共変位置の`['e, write int]`では、`'e`が反変位置にも含まれることを前提とし、その共有効果と具体的な`write int`を許す意味とする。
3. 反変位置の`['e, write int]`では、`'e`が`write 'a`を含むなら具体的な`write int`と矛盾しない制約が必要となる。ユーザーの例は`int <: 'a`である。この例だけから全効果familyの型引数に一律の分散規則を定めない。
4. 今回の反変側の型はdeep handlerを表す。共変位置にも現れる`'e`には、対象の`write int`が除かれた効果が伝わる。この意味は、元の継続をそのまま再開するshallow handlerで同familyの後続要求まで消せるという規則ではない。除去の適用範囲と完全なhandler像との対応は、元の要求・継続・attachmentの証拠から導く必要がある。
5. shallow handlerについての`'a ['e & [any, write int]] -> ['e] 'a`は「おそらく」という主型候補として記録する。主型性の証明、`&`や`any`の一般的意味、parser表記、`any`と既存の`Any`や内部極値との同一視は、この回答では決定しない。
6. 共変・反変の制約は、roleとtyped portを選んだ後、既存の`Rel_C`と同一の`(nu,K,D)`で解釈し、元の発生・path・attachment・依存関係を保つ。型変数を極性ごとに独立に具体化したり、family名だけを理由に要求を同一視したりしない。具体的なmembership規則、sourceからの証拠の導出、健全性・principality、独立した設計レビューと設計記録への反映は引き続き必要であり、compiler実装を承認する回答ではない。

## 承認対象と引き渡し

承認対象は`function-effect-row-denotation-answer/d1`の全文。明示的承認後に、同じ全文と実際の承認発言を含む`approved-answer.md`を保存する。

回答者は選択した回答ファイルのみを書き、Git操作を行わない。回答は未ステージ・未コミットのまま残し、質問者が検証して対応する質問・回答案・承認済み回答を統合する。公開だけで別の作業の再開や回答の適用は起こらない。確定後の訂正には、新しい関連質問と再承認が必要となる。
