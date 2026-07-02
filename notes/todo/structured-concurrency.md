# 構造化並行性とキャンセル TODO

出典: notes/design/2026-07-02-parting-assessment.md §2（Claude Fable 5、ユーザ承認済み）。
関連正本: 2026-07-02-resource-lifetime-decisions.md（v1 決定1〜3）、
2026-07-02-host-act-ffi-decisions.md（v2 F6）、spec/2026-07-02-io-resource-api.md。

2026-07-03: 決定文書として
[notes/design/2026-07-03-structured-concurrency-decisions.md](../design/2026-07-03-structured-concurrency-decisions.md)
を追加した。以後 serve first slice はこの文書を入口にし、この TODO は
実装チェックリストとして扱う。

## 問題

`accept`（suspend multi-shot tier）は接続ごとに分岐世界を作るが、
分岐の**死の規則**が未定義。

- 接続が途中で切断されたとき、その分岐の継続は孤児になる。
- 孤児分岐が持つ資源（lock、conn、書きかけ buffer）の解放点がない。
- 長寿サーバでは孤児が積もり、実質的なリークになる。

## 既に正本にある答え（決定文書の材料）

- **分岐の寿命 ≤ それを配った handler の extent**（v1 決定1 の自然な拡張）。
  serve の scope が終われば全分岐が終わる。
- **キャンセル = 分岐の drop = rollback**。v1 決定2 が既に
  「scope exit に到達しなかった分岐は write-back しない」と定義しており、
  キャンセルされた分岐のファイル編集は自動的に無かったことになる。
  新しい意味論は不要。
- lock 解放は v1 決定3 のとおり当面 handler extent。分岐単位の解放は
  continuation-drop hook（決定3 の (a)）が入った時に細粒度化される。
  **キャンセル通知と drop hook は同じ VM 工事**なので、一度に設計する。

## 決めるべきこと（決定文書 1 枚の範囲）

1. **drop の通知経路**: host（接続切断を知る側）→ scheduler → 分岐継続の破棄。
   v2 R2 の enqueue 規律に合わせ、「cancel(branch_id) を queue に積む」形にする。
2. **実行中の分岐の扱い**: suspend 点で止まっている分岐は即 drop できる。
   実行中の分岐は「次の suspend 点まで走らせてから drop」（協調的キャンセル）
   を既定とする。プリエンプションは導入しない。
3. **cleanup の表現**: rollback で足りない後始末（応答途中の接続への
   エラー通知など）を書きたい場合の受け皿。候補は「cancel も一つの effect で
   あり、分岐内の handler が catch できる」形。新機構より handler の再利用を優先。
4. **タイムアウト**: `timeout` は cancel の上の糖衣として std に置けるか。
   clock act + cancel で書けるなら core に入れない。
5. **観測可能性**: 分岐の生死を診断に出す（生きている分岐数、孤児 drop 数）。

## 依存と順序

- serve の実装（FFI 指示書の実装順 5）より**前に**決定文書を書く。
  実装後にキャンセルを入れると scheduler の作り直しになる。
- record/replay（notes/todo/record-replay.md）とは分岐 id を共有する。
  同じ識別子空間で設計すること。

## First slice

1. 決定文書: `notes/design/2026-07-03-structured-concurrency-decisions.md` で完了。
2. scheduler に branch id / parent id / status を持たせる。
3. scheduler に cancel(branch_id) を実装。suspend 中の分岐の即時 drop のみ。
4. fixture: accept 分岐を suspend 中に cancel → 分岐のファイル編集が
   rollback されている（v1 決定2 の検証と同一機構）。
5. fixture: parent extent 終了で suspended child branches が drop される。
6. fixture: double respond は dynamic failure になる。
7. 実行中分岐の協調的 drop は次 slice。

## やってはいけないこと

- プリエンプティブな分岐停止（任意点での強制終了）を入れること。
- cancel のために unwind finalizer を入れること（rollback で足りる範囲を守る）。
- 孤児分岐を GC に回収させて済んだことにすること（v1 決定1 違反）。
