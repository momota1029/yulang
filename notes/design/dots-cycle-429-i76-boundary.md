# C429 I-76: C427 の監査を単独実行できるようにする

対象は Forest・Readback・Visits。C427 の元の source snapshot、wires、positive pair の executable readback に必要な共有定義だけを新しい `Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429` に置く。SameRole 自体は変更しないので共有コピーは固有 namespace、移動した Readback の公開定義名はそのまま。各 Audit のテスト・定理・元の順序/候補/実行器・反例の判定は変更しない。Readback が利用する実データ自体を共有するので、同じ診断や辞書を得ることを新しい仮定として供給しない。

この変更は R15、check、check_sound、spec、C の数を変えない。凍結対象も変更なし。古い C428 の監査は対象外。独立検査では本番モジュールだけの LEAN_PATH を使い、新規作業ディレクトリで結果を出力せずに各 Audit の入力を直接実行する。全 7 本の C427 監査が個別に通った。
